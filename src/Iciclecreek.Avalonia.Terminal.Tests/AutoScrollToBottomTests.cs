using System.Collections.Concurrent;
using System.Text;
using Porta.Pty;
using Avalonia.Controls;
using Avalonia.Headless.NUnit;
using NUnit.Framework;

namespace Iciclecreek.Terminal.Tests;

/// <summary>
/// <see cref="TerminalView.AutoScrollToBottom"/> — follow the tail, pause when the user scrolls back,
/// resume when they return to it or type.
///
/// <para>Driven through <see cref="TerminalView.AttachConnection"/> with a connection the test pushes output
/// into, so each assertion is made at a known point rather than against whatever a real shell happened to
/// have written by then.</para>
/// </summary>
[TestFixture]
public class AutoScrollToBottomTests
{
    // ── Harness ─────────────────────────────────────────────────────────────────────────────────

    private static Window Show(Control content)
    {
        var window = new Window { Width = 800, Height = 600, Content = content };
        window.Show();
        window.UpdateLayout();
        global::Avalonia.Headless.AvaloniaHeadlessPlatform.ForceRenderTimerTick();
        return window;
    }

    private static async Task WaitUntil(Func<bool> condition, string because, int timeoutMs = 10_000)
    {
        var deadline = DateTime.UtcNow.AddMilliseconds(timeoutMs);
        while (!condition())
        {
            if (DateTime.UtcNow > deadline)
                throw new TimeoutException($"timed out after {timeoutMs}ms waiting until {because}");
            await Task.Delay(10);
        }
    }



    private static string Lines(int n, string tag = "line")
        => string.Concat(Enumerable.Range(0, n).Select(i => $"{tag} {i}\r\n"));

    /// <summary>Push output and wait for the emulator to have consumed it.</summary>
    private static async Task PushAndSettle(TerminalView view, PushConnection connection, string text)
    {
        var before = view.MaxScrollback;
        connection.Push(text);
        await WaitUntil(() => view.MaxScrollback > before, "the buffer grew");
        await Task.Delay(50);   // let the posted change notifications drain
    }

    // ── The contract ────────────────────────────────────────────────────────────────────────────

    /// <summary>Default on: output drags the viewport along, which is the pre-existing behaviour.</summary>
    [AvaloniaTest]
    public Task Following_by_default() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));
        Assert.That(view.ViewportY, Is.EqualTo(view.MaxScrollback), "a following view sits at the tail");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// The point of the feature: scroll back and output stops yanking the viewport down. This is the case
    /// that made reading a scrollback impossible while anything was still printing.
    /// </summary>
    [AvaloniaTest]
    public Task Scrolling_back_pauses_the_follow() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));

        view.ViewportY = view.MaxScrollback - 50;      // park up in the scrollback
        var parked = view.ViewportY;

        await PushAndSettle(view, connection, Lines(200, "more"));

        Assert.That(view.ViewportY, Is.EqualTo(parked), "output must not move a viewport the user parked");
        Assert.That(view.ViewportY, Is.LessThan(view.MaxScrollback), "and the buffer did grow underneath it");

        connection.Done();
        window.Close();
    });

    /// <summary>Scrolling back to the tail resumes following, with no explicit resume call needed.</summary>
    [AvaloniaTest]
    public Task Returning_to_the_tail_resumes_the_follow() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));
        view.ViewportY = view.MaxScrollback - 50;
        await PushAndSettle(view, connection, Lines(50, "more"));

        view.ViewportY = view.MaxScrollback;           // back to the bottom
        await PushAndSettle(view, connection, Lines(50, "again"));

        Assert.That(view.ViewportY, Is.EqualTo(view.MaxScrollback), "returning to the tail resumes following");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// <see cref="TerminalView.IsFollowingTail"/> is what a host reads to show a "jump to bottom" affordance, so
    /// it has to be true the moment the user scrolls, not the moment the next output happens to arrive. The
    /// flag used to be sampled only at write time; a view scrolled up in a quiet terminal reported "following"
    /// until something was printed.
    /// </summary>
    [AvaloniaTest]
    public Task Scrolling_back_stops_following_before_any_output_arrives() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);
        await PushAndSettle(view, connection, Lines(200));
        Assert.That(view.IsFollowingTail, Is.True, "a view at the tail follows");

        view.ViewportY = view.MaxScrollback - 50;      // park up in the scrollback; nothing is printed
        Assert.That(view.IsFollowingTail, Is.False, "scrolling back stops the follow immediately");

        view.ViewportY = view.MaxScrollback;           // and back to the bottom, still nothing printed
        Assert.That(view.IsFollowingTail, Is.True, "returning to the tail resumes it immediately");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// A scrollback trim that lands while the user is parked must shift the viewport by what the ring dropped,
    /// so the same rows stay under the eye (<c>OnBufferTrimmed</c>). That handler bails while following -- and
    /// with the flag sampled only at write time, a trim caused by a write that did NOT go through the view's
    /// own read loop (a host writing to <see cref="TerminalView.Terminal"/> directly, which is public for that)
    /// found the flag still true after a scroll-up and did nothing: the parked view drifted onto other rows.
    /// </summary>
    [AvaloniaTest]
    public Task A_trim_while_parked_keeps_the_same_rows_under_the_viewport_even_for_direct_writes() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);
        await PushAndSettle(view, connection, Lines(200));
        var terminal = view.Terminal;

        view.ViewportY = view.MaxScrollback - 12;      // park 12 lines up
        var parked = view.ViewportY;
        var topRowBefore = terminal.Buffer.Lines[parked].TranslateToString(trimRight: true);
        Assert.That(topRowBefore, Does.StartWith("line "), "the view is parked over earlier output, not the tail");

        // Push the ring past capacity and evict, writing STRAIGHT to the emulator -- not through the read loop,
        // which samples the flag for itself. Well short of evicting the parked rows.
        var capacity = terminal.Options.Scrollback + terminal.Rows;
        var flood = capacity - terminal.Buffer.Length + 100;
        Assert.That(flood, Is.GreaterThan(0));
        for (var i = 0; i < flood; i++)
            terminal.WriteLine($"flood {i}");

        Assert.That(view.ViewportY, Is.LessThan(parked), "the ring dropped lines off the top and the viewport moved with them");
        Assert.That(terminal.Buffer.Lines[view.ViewportY].TranslateToString(trimRight: true), Is.EqualTo(topRowBefore),
            "the same row is still at the top of the parked view");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// The last item of #25's own test plan, which failed as originally written: turning the property off has
    /// to actually stop the terminal scrolling itself.
    /// </summary>
    [AvaloniaTest]
    public Task Off_means_never_auto_scrolls() => Run(async () =>
    {
        var view = new TerminalView { Process = "", AutoScrollToBottom = false };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));

        Assert.That(view.ViewportY, Is.Zero, "with auto-scroll off the viewport never moves on its own");
        Assert.That(view.MaxScrollback, Is.GreaterThan(0), "though the buffer still grew");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// Set in an object initialiser, which runs before the emulator exists. The volatile mirror the reader
    /// consults is updated ahead of the null-guard in OnPropertyChanged precisely so this is not dropped —
    /// without that, the test above passes for the wrong reason and this one fails.
    /// </summary>
    [AvaloniaTest]
    public Task Off_survives_being_set_before_initialisation() => Run(async () =>
    {
        var view = new TerminalView { Process = "", AutoScrollToBottom = false };
        var window = Show(view);
        Assert.That(view.AutoScrollToBottom, Is.False, "the property itself round-trips");

        var connection = new PushConnection();
        view.AttachConnection(connection);
        await PushAndSettle(view, connection, Lines(100));

        Assert.That(view.ViewportY, Is.Zero, "the reader saw the mirrored value, not the default");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// A scrollbar drag moves ViewportY directly rather than going through the wheel handler. The flag-based
    /// design missed this — sampling the buffer at write time covers it without enumerating the paths.
    /// </summary>
    [AvaloniaTest]
    public Task A_programmatic_viewport_move_pauses_the_follow() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));

        // Exactly what TerminalControl.OnScrollBarScroll does — no wheel event involved.
        view.ViewportY = view.MaxScrollback - 30;
        var parked = view.ViewportY;

        await PushAndSettle(view, connection, Lines(100, "more"));
        Assert.That(view.ViewportY, Is.EqualTo(parked), "a scrollbar-driven move has to pause the follow too");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// On TerminalControl the property must be STYLED, not a CLR forwarder: a forwarder drops anything set
    /// before the template runs, which is the normal timing for XAML attributes and object initialisers.
    /// </summary>
    [AvaloniaTest]
    public void TerminalControl_keeps_a_value_set_before_its_template_runs()
    {
        var control = new TerminalControl { Process = "", AutoScrollToBottom = false };
        Assert.That(control.AutoScrollToBottom, Is.False, "set before the template is applied");

        var window = Show(control);
        Assert.That(control.AutoScrollToBottom, Is.False, "and still false once it has");

        window.Close();
    }

    /// <summary>
    /// Once the scrollback ring is FULL it drops its oldest lines, and every absolute index shifts down with
    /// them. A parked viewport keeps its ViewportY, so without compensation the content under the user's eye
    /// slides upward while output keeps arriving — they drift off what they were reading even though the
    /// follow is correctly paused.
    ///
    /// <para>A small BufferSize is what makes this testable: it reaches the eviction threshold in a hundred
    /// lines rather than a thousand. The push is sized to evict PAST the parked position but not past the
    /// parked CONTENT — once the ring drops the line the user is reading, it is genuinely gone and no
    /// compensation can help, which is a limit of the buffer rather than of this fix.</para>
    /// </summary>
    [AvaloniaTest]
    public Task A_parked_viewport_rides_out_scrollback_eviction() => Run(async () =>
    {
        var view = new TerminalView { Process = "", BufferSize = 120 };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(100, "old"));

        view.ViewportY = view.MaxScrollback - 20;
        var parkedY = view.ViewportY;
        var parkedText = TopVisibleLine(view);
        Assert.That(parkedText, Does.StartWith("old "), "sanity: parked over the earlier output");

        // Enough to drive the ring past capacity and force eviction.
        await PushAndSettle(view, connection, Lines(90, "new"));

        Assert.That(view.ViewportY, Is.LessThan(parkedY),
            "sanity: the ring evicted, so the compensation had something to do");
        Assert.That(TopVisibleLine(view), Is.EqualTo(parkedText),
            "the line under the user must not slide away as the ring evicts beneath it");

        connection.Done();
        window.Close();
    });

    /// <summary>The text of the first row the viewport shows, trailing blanks trimmed.</summary>
    private static string TopVisibleLine(TerminalView view)
    {
        var line = view.Terminal.Buffer.GetLine(view.Terminal.Buffer.ViewportY);
        if (line == null) return string.Empty;
        var sb = new StringBuilder();
        for (int x = 0; x < line.Length; x++)
            sb.Append(string.IsNullOrEmpty(line[x].Content) ? " " : line[x].Content);
        return sb.ToString().TrimEnd();
    }

    /// <summary>
    /// A terminal that can pause its follow needs a way to resume it on demand — the "jump to bottom"
    /// affordance a host shows once the user scrolls away. IsFollowingTail drives whether that affordance is
    /// visible; FollowTail() is what it calls.
    /// </summary>
    [AvaloniaTest]
    public Task FollowTail_returns_the_view_to_the_bottom() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));
        Assert.That(view.IsFollowingTail, Is.True, "a fresh view follows");

        view.ViewportY = view.MaxScrollback - 50;
        await PushAndSettle(view, connection, Lines(50, "more"));
        Assert.That(view.IsFollowingTail, Is.False, "scrolling back stops the follow");

        view.FollowTail();
        Assert.That(view.ViewportY, Is.EqualTo(view.MaxScrollback), "and this puts it back");

        await PushAndSettle(view, connection, Lines(50, "again"));
        Assert.That(view.IsFollowingTail, Is.True, "following again, so new output drags the viewport");
        Assert.That(view.ViewportY, Is.EqualTo(view.MaxScrollback));

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// The guards are the reason this is a method rather than "set ViewportY yourself": with auto-scroll off
    /// the host owns the viewport, and a jump-to-bottom button must not quietly take it back.
    /// </summary>
    [AvaloniaTest]
    public Task FollowTail_is_a_no_op_when_auto_scroll_is_off() => Run(async () =>
    {
        var view = new TerminalView { Process = "", AutoScrollToBottom = false };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));
        var before = view.ViewportY;

        view.FollowTail();
        Assert.That(view.ViewportY, Is.EqualTo(before), "auto-scroll off means the host owns the viewport");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// The view's OWN lines obey the follow rules too.
    ///
    /// <para>The exit notice used to scroll to the bottom whenever auto-scroll was on, regardless of whether
    /// the follow was paused — and a process exiting is precisely when somebody is scrolled up reading what
    /// it printed, so it was the worst available moment to yank them to the end.</para>
    /// </summary>
    [AvaloniaTest]
    public Task The_exit_notice_does_not_yank_a_parked_view_to_the_bottom() => Run(async () =>
    {
        var view = new TerminalView { Process = "" };
        var window = Show(view);
        var connection = new PushConnection();

        var exited = false;
        view.ProcessExited += (_, _) => exited = true;
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(200));

        view.ViewportY = view.MaxScrollback - 50;

        // The follow state is SAMPLED at each write rather than latched, so it takes a write for the pause
        // to be observable — same idiom as the FollowTail tests above.
        await PushAndSettle(view, connection, Lines(20, "more"));
        Assert.That(view.IsFollowingTail, Is.False, "sanity: scrolled back, so the follow is paused");

        var parkedY = view.ViewportY;
        var parkedText = TopVisibleLine(view);

        // EOF, which is what makes the read loop write "Process exited with code: 0".
        connection.Done();
        await WaitUntil(() => exited, "the exit was reported, so the notice has been written");
        await Task.Delay(50);   // let the posted change notifications drain

        Assert.That(view.ViewportY, Is.EqualTo(parkedY), "the exit notice must not resume a paused follow");
        Assert.That(TopVisibleLine(view), Is.EqualTo(parkedText), "and the user keeps reading what they were");

        window.Close();
    });

    /// <summary>
    /// Eviction compensation survives a re-parent, and is applied exactly ONCE afterwards.
    ///
    /// <para>Both failure directions are real and this pins both. <c>Terminal.Buffer</c> outlives
    /// detach/re-attach, so subscribing on attach without unsubscribing on detach adds a handler per
    /// re-parent and moves a parked viewport by a MULTIPLE of the evicted count; unsubscribing without
    /// re-subscribing leaves the compensation off entirely and the content slides away as before. Either way
    /// the line under the user moves, which is the one thing the compensation exists to prevent.</para>
    /// </summary>
    [AvaloniaTest]
    public Task Eviction_compensation_survives_a_reparent() => Run(async () =>
    {
        var view = new TerminalView { Process = "", BufferSize = 120 };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(100, "old"));

        // Out of the tree and back, with the PTY held across it — the pop-out/dock-back path.
        view.BeginReparent();
        window.Content = null;
        window.Content = view;
        window.UpdateLayout();
        view.EndReparent();

        view.ViewportY = view.MaxScrollback - 20;
        var parkedY = view.ViewportY;
        var parkedText = TopVisibleLine(view);
        Assert.That(parkedText, Does.StartWith("old "), "sanity: parked over the earlier output");

        await PushAndSettle(view, connection, Lines(90, "new"));

        Assert.That(view.ViewportY, Is.LessThan(parkedY),
            "sanity: the ring evicted, so the compensation had something to do");
        Assert.That(TopVisibleLine(view), Is.EqualTo(parkedText),
            "compensated exactly once — neither dropped by the detach nor doubled by the re-attach");

        connection.Done();
        window.Close();
    });

    /// <summary>
    /// The other half of the same balance: a view that is off the tree for good stops listening.
    ///
    /// <para><see cref="TerminalView.Terminal"/> is public, so a host holding the emulator holds the buffer,
    /// and a <c>Trimmed</c> handler never unsubscribed keeps the whole view alive through it — and goes on
    /// moving the viewport of a control nobody is showing.</para>
    /// </summary>
    [AvaloniaTest]
    public Task A_detached_view_stops_compensating() => Run(async () =>
    {
        var view = new TerminalView { Process = "", BufferSize = 120 };
        var window = Show(view);
        var connection = new PushConnection();
        view.AttachConnection(connection);

        await PushAndSettle(view, connection, Lines(100, "old"));

        view.ViewportY = view.MaxScrollback - 20;

        // A write through the VIEW, so the paused follow is actually sampled. Without it _followBottom is
        // still true from the push above, OnBufferTrimmed returns early whether it is subscribed or not,
        // and this test asserts nothing. Small enough not to evict on its own.
        await PushAndSettle(view, connection, Lines(10, "settle"));
        Assert.That(view.IsFollowingTail, Is.False, "sanity: parked, so there is compensation to suppress");

        var parkedY = view.ViewportY;

        window.Content = null;      // a real detach — no BeginReparent, so nothing is coming back

        // Written straight through the emulator rather than pushed down the connection, deliberately: the
        // detach has already dropped the connection, and going through it would drag the exit path in and
        // leave this asserting on two things at once.
        view.Terminal.Write(Lines(90, "new"));

        Assert.That(view.Terminal.Buffer.ViewportY, Is.EqualTo(parkedY),
            "a detached view must not still be moving the viewport in response to the buffer");

        connection.Done();          // let the read loop unwind now the assertions are made
        window.Close();
    });

    /// <summary>
    /// The harness itself, pinned: every test above reads through this stream, so a stream that only works
    /// against one particular consumer buffer size makes all of them depend on a decision made in the read
    /// loop. Read through a buffer far SMALLER than a pushed chunk and the bytes must still arrive whole and
    /// in order.
    /// </summary>
    [Test]
    public void PushStream_honours_the_requested_count()
    {
        var stream = new PushStream();
        var pushed = Lines(40);
        stream.Push(pushed);
        stream.Done();

        var small = new byte[7];        // deliberately smaller than the chunk
        var got = new MemoryStream();
        int n;
        while ((n = stream.Read(small, 0, small.Length)) > 0)
        {
            Assert.That(n, Is.LessThanOrEqualTo(small.Length), "a stream must never write past the count it was given");
            got.Write(small, 0, n);
        }

        Assert.That(Encoding.UTF8.GetString(got.ToArray()), Is.EqualTo(pushed),
            "the chunk is delivered whole and in order across as many reads as it takes");
    }

    private static Task Run(Func<Task> body) => body();
}
