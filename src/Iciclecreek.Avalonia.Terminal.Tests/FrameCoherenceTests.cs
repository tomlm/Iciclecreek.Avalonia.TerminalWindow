using Avalonia.Controls;
using Avalonia.Headless.NUnit;
using Avalonia.Threading;
using NUnit.Framework;

namespace Iciclecreek.Terminal.Tests;

/// <summary>
/// A painted screen must be one frame, not halves of two.
/// </summary>
/// <remarks>
/// <para>The renderer used to walk the live buffer while the reader thread wrote into it. Every row
/// was individually protected, but rows were read independently, so a paint landing mid-frame drew
/// row 1 from one frame and row 40 from another. Proven with a probe that labelled every row with
/// its frame's letter: clean while frames were small enough to land between two paints, torn under
/// per-cell-colour frames that were not.</para>
/// <para>The fix is <see cref="FrameCapturePool"/>: at ESU the reader publishes a copy of the
/// viewport, and the renderer draws from the copy. These tests drive that machinery the way the
/// real threads do — publish through the emulator's own DEC 2026 handling, consume through the same
/// pin call the renderer makes.</para>
/// </remarks>
[TestFixture]
public class FrameCoherenceTests
{
    private static readonly string Esc = ((char)0x1B).ToString();

    private static (TerminalView view, Window window) Realised()
    {
        var view = new TerminalView { Process = "" };
        var window = new Window { Width = 800, Height = 600, Content = view };
        window.Show();
        window.UpdateLayout();
        return (view, window);
    }

    private static T Field<T>(TerminalView view, string name)
    {
        var f = typeof(TerminalView).GetField(name,
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        Assert.That(f, Is.Not.Null, $"{name} has been renamed; this test needs updating");
        return (T)f!.GetValue(view)!;
    }

    /// <summary>Writes one full frame of <paramref name="fill"/> rows, wrapped in DEC 2026.</summary>
    private static void WriteFrame(TerminalView view, char fill)
    {
        view.Terminal.Write($"{Esc}[?2026h");
        WriteRows(view, fill, 0, view.Terminal.Rows);
        view.Terminal.Write($"{Esc}[?2026l");
    }

    private static void WriteRows(TerminalView view, char fill, int from, int to)
    {
        var cols = view.Terminal.Cols;

        for (var row = from; row < to; row++)
            view.Terminal.Write($"{Esc}[{row + 1};1H" + new string(fill, cols));
    }

    /// <summary>The pin call the renderer makes, with the arguments it would pass right now.</summary>
    private static CapturedFrame? Pin(TerminalView view, bool atomicUpdate, int startLineOffset = 0)
    {
        var pool = Field<FrameCapturePool>(view, "_frameCapture");
        var generation = Field<long>(view, "_liveWriteGeneration");

        return pool.PinForRender(
            view.Terminal.Buffer.ViewportY + startLineOffset,
            view.Terminal.Cols,
            view.Terminal.Rows,
            generation,
            atomicUpdate);
    }

    private static char CellAt(CapturedFrame frame, int row, TerminalView view)
    {
        var line = frame.LineAt(view.Terminal.Buffer.ViewportY + row);
        Assert.That(line, Is.Not.Null, $"the capture has no line for row {row}");
        return line![0].Content is { Length: > 0 } c ? c[0] : ' ';
    }

    // ---------------------------------------------------- the tear itself

    [AvaloniaTest]
    public void A_paint_landing_mid_frame_draws_the_last_complete_frame()
    {
        // The regression test for the tear. Frame A is complete and published; frame B is half
        // written with the update still open — exactly the moment a paint used to catch half of
        // each. The renderer's pin must hand back A whole, while the live buffer visibly holds B.
        var (view, window) = Realised();
        try
        {
            WriteFrame(view, 'A');

            view.Terminal.Write($"{Esc}[?2026h");
            WriteRows(view, 'B', 0, view.Terminal.Rows / 2);

            var frame = Pin(view, atomicUpdate: true);

            Assert.That(frame, Is.Not.Null, "no capture was published at ESU");

            var liveTop = view.Terminal.Buffer.GetLine(view.Terminal.Buffer.ViewportY);
            Assert.That(liveTop![0].Content, Is.EqualTo("B"),
                "sanity: the live buffer must hold the half-written frame, or this test is "
                + "comparing the capture against itself");

            for (var row = 0; row < view.Terminal.Rows; row++)
            {
                Assert.That(CellAt(frame!, row, view), Is.EqualTo('A'),
                    $"row {row} came from the frame being written, not the one that was complete "
                    + "-- which is the tear");
            }
        }
        finally { window.Close(); }
    }

    [AvaloniaTest]
    public void A_paint_during_a_chunk_write_before_its_BSU_serves_the_last_complete_frame()
    {
        // The residual tear after the mid-frame one was fixed: an atomic update only protects
        // from the BSU byte onward, but the reader bumps the write generation when a CHUNK
        // arrives — so a paint landing while the bytes BEFORE the chunk's BSU parse saw a stale
        // generation with no update open, declined the capture, and read the buffer mid-write.
        // While the reader declares a write in progress, a stale capture that still describes
        // the viewport must serve; outside any write, staleness must still send the paint to
        // the live buffer, whose freshness is the point.
        var (view, window) = Realised();
        try
        {
            WriteFrame(view, 'A');

            var pool = Field<FrameCapturePool>(view, "_frameCapture");
            var generation = Field<long>(view, "_liveWriteGeneration");

            var duringWrite = pool.PinForRender(
                view.Terminal.Buffer.ViewportY, view.Terminal.Cols, view.Terminal.Rows,
                generation + 1, atomicUpdate: false, writeInProgress: true);

            Assert.That(duringWrite, Is.Not.Null,
                "a stale capture must serve while the buffer is mid-write, or the paint tears");
            Assert.That(CellAt(duringWrite!, 0, view), Is.EqualTo('A'));

            var quiescent = pool.PinForRender(
                view.Terminal.Buffer.ViewportY, view.Terminal.Cols, view.Terminal.Rows,
                generation + 1, atomicUpdate: false, writeInProgress: false);

            Assert.That(quiescent, Is.Null,
                "outside any write a stale capture must be declined -- the live buffer is "
                + "quiescent and fresher, and serving old frames there is plain staleness");
        }
        finally { window.Close(); }
    }

    [AvaloniaTest]
    public void The_next_complete_frame_replaces_the_capture()
    {
        // Coherence must not mean staleness: the moment B's ESU lands, B is what renders.
        var (view, window) = Realised();
        try
        {
            WriteFrame(view, 'A');
            WriteFrame(view, 'B');

            var frame = Pin(view, atomicUpdate: false);

            Assert.That(frame, Is.Not.Null);
            Assert.That(CellAt(frame!, 0, view), Is.EqualTo('B'));
        }
        finally { window.Close(); }
    }

    // ---------------------------------------------------- when live must win

    [AvaloniaTest]
    public void A_write_outside_any_frame_retires_the_capture()
    {
        // The staleness guard. A write with no update open — a shell echoing, WriteOwnLine, any
        // output from a program that never heard of DEC 2026 — moves the buffer past the capture,
        // and the capture must stand down rather than show the screen as it used to be. The
        // generation bump here mirrors the one ConsumeOutputChunk makes for every real chunk.
        var (view, window) = Realised();
        try
        {
            WriteFrame(view, 'A');

            var genField = typeof(TerminalView).GetField("_liveWriteGeneration",
                System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!;
            genField.SetValue(view, (long)genField.GetValue(view)! + 1);
            WriteRows(view, 'C', 0, 1);

            var frame = Pin(view, atomicUpdate: false);

            Assert.That(frame, Is.Null,
                "the capture outlived a write it knows nothing about; a shell would render as the "
                + "screen stood before its own output");
        }
        finally { window.Close(); }
    }

    [AvaloniaTest]
    public void A_capture_for_a_different_viewport_is_declined()
    {
        // Scrolling moves the viewport without writing a byte. A capture keyed to the old position
        // must not be stretched over the new one.
        var (view, window) = Realised();
        try
        {
            WriteFrame(view, 'A');

            var frame = Pin(view, atomicUpdate: false, startLineOffset: 1);

            Assert.That(frame, Is.Null,
                "a capture of one viewport was served for another");
        }
        finally { window.Close(); }
    }

    [AvaloniaTest]
    public void No_capture_means_the_live_path_and_nothing_else()
    {
        // A terminal that has never seen an ESU must behave exactly as before this machinery
        // existed. Chunk-boundary publishes need the real read loop; a test writing the emulator
        // directly never publishes at all, so the pin must answer null rather than something.
        var (view, window) = Realised();
        try
        {
            WriteRows(view, 'A', 0, view.Terminal.Rows);

            Assert.That(Pin(view, atomicUpdate: false), Is.Null);
        }
        finally { window.Close(); }
    }

    // ---------------------------------------------------- the pool's handoff

    [AvaloniaTest]
    public void A_pinned_frame_survives_later_publishes_untouched()
    {
        // The renderer may replay runs from a pinned frame well after pinning it, so the publisher
        // must never write into that slot. Three publishes after the pin cycle the pool past every
        // other slot; the pinned content must still read as the frame that was pinned.
        var (view, window) = Realised();
        try
        {
            WriteFrame(view, 'A');
            var pinned = Pin(view, atomicUpdate: false);
            Assert.That(pinned, Is.Not.Null);
            Assert.That(CellAt(pinned!, 0, view), Is.EqualTo('A'), "sanity");

            WriteFrame(view, 'B');
            WriteFrame(view, 'C');
            WriteFrame(view, 'D');

            Assert.That(CellAt(pinned!, 0, view), Is.EqualTo('A'),
                "a later publish reused the pinned slot; a render in flight would have drawn from "
                + "cells being overwritten under it -- the tear again, one layer down");
        }
        finally { window.Close(); }
    }

    // ---------------------------------------------------- rows a capture cannot hold

    [AvaloniaTest]
    public void A_doubled_row_is_left_to_the_live_line()
    {
        // DECDWL and friends carry a transform the render paths resolve against the live line, so
        // the capture stores null there and the renderer falls back — for that row only.
        var (view, window) = Realised();
        try
        {
            view.Terminal.Write($"{Esc}[?2026h");
            WriteRows(view, 'A', 0, view.Terminal.Rows);
            view.Terminal.Write($"{Esc}[2;1H{Esc}#6DOUBLED");
            view.Terminal.Write($"{Esc}[?2026l");

            var frame = Pin(view, atomicUpdate: false);

            Assert.That(frame, Is.Not.Null);
            Assert.That(frame!.LineAt(view.Terminal.Buffer.ViewportY + 1), Is.Null,
                "the doubled row was captured; its transform lives on the live line and a clone "
                + "renders it as ordinary text");
            Assert.That(frame.LineAt(view.Terminal.Buffer.ViewportY), Is.Not.Null,
                "and the ordinary row above it must still be served by the capture");
        }
        finally { window.Close(); }
    }
}
