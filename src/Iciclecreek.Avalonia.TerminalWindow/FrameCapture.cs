using System;
using System.Diagnostics;
using System.Threading;
using XTerm.Buffer;
using XT = global::XTerm;

namespace Iciclecreek.Terminal
{
    /// <summary>
    /// One complete frame of the viewport, captured at a moment the application declared it whole.
    /// </summary>
    /// <remarks>
    /// <para>This exists because the renderer walks the live buffer while the reader thread writes
    /// into it. Every row is individually protected — the stamp-and-retry in CollectLineRuns and
    /// SnapshotBuilder sees to that — but rows are read independently, so a painted screen can hold
    /// row 1 from one frame and row 40 from another. That mixture is the tear: proven with a probe
    /// that labelled every row with its frame, clean under synchronised output only while frames
    /// were small enough to land between two paints, torn as soon as they were not.</para>
    /// <para>A capture is taken on the READER thread, inside the ESU handler — which runs from
    /// within <c>Terminal.Write</c>, so at that instant the reader owns the buffer by construction
    /// and no lock is needed. The renderer then draws from the capture instead of the live buffer,
    /// and a paint landing mid-frame shows the LAST COMPLETE frame rather than half of two.</para>
    /// <para>The rows are <see cref="BufferLine"/> clones rather than a private cell format, so the
    /// render paths consume them through the exact code they already have. A row the clone cannot
    /// represent faithfully — pictures, OSC 66 sized runs, a doubled line — is left null, and the
    /// renderer falls back to the live line for that row, which is today's behaviour. Those rows
    /// are rare and mostly static, so their tearing exposure is negligible.</para>
    /// </remarks>
    internal sealed class CapturedFrame
    {
        /// <summary>Viewport rows, by screen row. Null means "read the live line for this row".</summary>
        public BufferLine?[] Lines = Array.Empty<BufferLine?>();

        /// <summary>The absolute buffer index of <c>Lines[0]</c> when the capture was taken.</summary>
        public int StartLine;

        /// <summary>Column count the capture was taken at; a resize since makes it unusable.</summary>
        public int Cols;

        /// <summary>
        /// The view's write generation this capture is current WITH — see
        /// <see cref="FrameCapturePool.PinForRender"/> for how it gates use.
        /// </summary>
        public long Generation;

        /// <summary>The line for an absolute buffer index, or null when the live line must serve.</summary>
        public BufferLine? LineAt(int absolute)
        {
            int index = absolute - StartLine;

            return index >= 0 && index < Lines.Length ? Lines[index] : null;
        }
    }

    /// <summary>
    /// Owns the captured frames and the handoff between the thread that writes them and the thread
    /// that draws them.
    /// </summary>
    /// <remarks>
    /// <para>Lock-free on purpose. The one rule this codebase has about reader/UI locking is that
    /// there must not be any: the emulator answers some requests synchronously through
    /// <c>Dispatcher.UIThread.Invoke</c> from inside <c>Terminal.Write</c>, so a UI thread blocked
    /// on anything the reader holds is a deadlock, not a stall. Publication is a single volatile
    /// reference write; consumption is a volatile read plus a pin.</para>
    /// <para>Three slots, reused rather than reallocated — a capture is tens of kilobytes of cells,
    /// and fifty fresh ones a second is the kind of steady garbage this renderer is measured on not
    /// producing. Three is the minimum that always leaves a writable slot: one published, one
    /// possibly pinned by a render in progress, one free.</para>
    /// <para>The publisher is never concurrent with itself: every publish site runs on the thread
    /// that is delivering output at that moment — the pty reader in production, the UI thread when
    /// a test writes the emulator directly — and those never overlap by construction of the read
    /// loop and its handover.</para>
    /// </remarks>
    internal sealed class FrameCapturePool
    {
        /// <summary>
        /// The least time between two chunk-boundary publishes, for output that never declares a
        /// frame. Sync applications publish at ESU and are not throttled by this — their frames
        /// arrive at most as fast as they draw them.
        /// </summary>
        /// <remarks>
        /// A chunk boundary is not a frame boundary, so for non-sync output a capture merely
        /// freezes what today's renderer would have raced for — same picture, minus the race. That
        /// is worth at most a paint interval of freshness, so copying faster than the paint
        /// throttle (30fps) buys nothing and a full-rate producer would otherwise ask for
        /// thousands of copies a second.
        /// </remarks>
        private static readonly long ChunkPublishIntervalTicks = Stopwatch.Frequency / 30;

        private readonly CapturedFrame[] _slots = { new(), new(), new() };

        private CapturedFrame? _published;
        private CapturedFrame? _pinned;
        private long _lastChunkPublish;

        /// <summary>
        /// Captures the viewport. Must be called on the thread that owns the buffer at that moment
        /// — the ESU handler and the chunk tail both qualify, being inside or immediately after
        /// <c>Terminal.Write</c> on the delivering thread.
        /// </summary>
        /// <param name="generation">
        /// The view's write generation this capture will be current with. Callers pass the value
        /// that INCLUDES the write being delivered, so a capture taken at the end of a chunk is
        /// usable until the next write, not stale on arrival.
        /// </param>
        public void Publish(XT.Terminal terminal, long generation)
        {
            var slot = FreeSlot();

            var buffer = terminal.Buffer;
            int rows = terminal.Rows;
            int cols = terminal.Cols;
            int start = buffer.ViewportY;

            if (slot.Lines.Length != rows)
                slot.Lines = new BufferLine?[rows];

            for (int row = 0; row < rows; row++)
            {
                int absolute = start + row;

                var live = absolute >= 0 && absolute < buffer.Length
                    ? buffer.GetLine(absolute)
                    : null;

                // The rows the snapshot renderer already declines, for the same reasons: a sized
                // run and a doubled row carry state the consumers resolve against the live line.
                // Null sends the renderer to the live line, which is exactly what happens for
                // these rows today.
                //
                // Image rows are NOT excluded, and that is load-bearing: CopyFrom carries the
                // placements along with the cells. A full-screen picture drawn through Unicode
                // placeholders (Consolonia) makes every viewport row an image row, and every one
                // of them read live was exactly the tear this class exists to prevent — a paint
                // landing mid-write showed rows whose tiles were mid-replacement, a black band
                // sweeping the picture while text rows above it held steady.
                if (live is null
                    || live.HasSizedRuns
                    || live.LineAttribute != LineAttribute.Normal)
                {
                    slot.Lines[row] = null;
                    continue;
                }

                var clone = slot.Lines[row];

                if (clone is null)
                    slot.Lines[row] = clone = new BufferLine(cols);

                // CopyFrom brings the live line's run cache along with its cells. That is wanted:
                // the cache describes exactly the content being copied, so an unchanged row renders
                // from cache without being re-shaped — and a later write to the LIVE line clears
                // only the live line's slot, never this one's.
                clone.CopyFrom(live);
            }

            slot.StartLine = start;
            slot.Cols = cols;
            slot.Generation = generation;

            Volatile.Write(ref _published, slot);
        }

        /// <summary>Publishes at a chunk boundary, at most at the throttled rate.</summary>
        public void PublishThrottled(XT.Terminal terminal, long generation)
        {
            long now = Stopwatch.GetTimestamp();

            if (now - _lastChunkPublish < ChunkPublishIntervalTicks)
                return;

            _lastChunkPublish = now;
            Publish(terminal, generation);
        }

        /// <summary>
        /// The frame the renderer should draw from, or null to read the live buffer. Pins the
        /// returned frame: the publisher will not reuse its slot until the next pin replaces it.
        /// </summary>
        /// <remarks>
        /// <para>A capture serves when it is CURRENT — its generation matches the view's, meaning
        /// nothing has written the buffer since it was taken — or when an atomic update is open,
        /// where the live buffer is mid-frame by declaration and a complete previous frame beats a
        /// fresh half-written one. A capture that is neither is declined: the buffer has moved on
        /// outside any frame, and live is both correct and as safe as it ever was.</para>
        /// <para>The pin stays until the next call rather than being released per render. Runs
        /// built from the capture can be replayed by later frames through the line cache, so "in
        /// use" genuinely extends past the render that pinned it; holding one slot back costs
        /// nothing with three.</para>
        /// <para>The verify loop closes the one gap volatile handoff leaves: a publisher choosing
        /// its slot between this thread reading the reference and recording the pin. Publication
        /// always follows slot selection, so re-reading the reference after pinning proves the
        /// selection that mattered saw this pin.</para>
        /// </remarks>
        public CapturedFrame? PinForRender(
            int startLine, int cols, int rows, long liveGeneration, bool atomicUpdate)
        {
            CapturedFrame? frame;

            while (true)
            {
                frame = Volatile.Read(ref _published);
                Volatile.Write(ref _pinned, frame);

                if (Volatile.Read(ref _published) == frame)
                    break;
            }

            if (frame is null)
                return null;

            if (frame.Cols != cols || frame.StartLine != startLine || frame.Lines.Length < rows)
                return null;

            if (frame.Generation != liveGeneration && !atomicUpdate)
                return null;

            return frame;
        }

        /// <summary>
        /// Discards every capture, sending the renderer back to the live buffer until the next
        /// publish. For whole-view invalidations — a palette change re-resolves brushes, and the
        /// run caches riding inside the captured lines would replay the old ones.
        /// </summary>
        public void InvalidateAll()
        {
            Volatile.Write(ref _published, null);
        }

        private CapturedFrame FreeSlot()
        {
            var published = Volatile.Read(ref _published);
            var pinned = Volatile.Read(ref _pinned);

            foreach (var slot in _slots)
            {
                if (!ReferenceEquals(slot, published) && !ReferenceEquals(slot, pinned))
                    return slot;
            }

            // Unreachable with three slots and two exclusions, but a wrong answer here must corrupt
            // nothing rather than throw in the middle of Terminal.Write.
            return _slots[0];
        }
    }
}
