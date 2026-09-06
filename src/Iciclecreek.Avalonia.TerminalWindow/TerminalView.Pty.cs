using Avalonia;
using Avalonia.Controls;
using Avalonia.Input;
using Avalonia.Input.Platform;
using Avalonia.Input.TextInput;
using Avalonia.Interactivity;
using Avalonia.LogicalTree;
using Avalonia.Media;
using Avalonia.Media.TextFormatting;
using Avalonia.Media.Immutable;
using Avalonia.Media.Imaging;
using Avalonia.Platform;
using Avalonia.Rendering;
using Avalonia.Threading;
using Iciclecreek.Avalonia.Terminal;
using Porta.Pty;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using XTerm.Buffer;
using XTerm.Events;
using XT = global::XTerm;

namespace Iciclecreek.Terminal
{

    public partial class TerminalView
    {
        public void WaitForExit(int ms) => _ptyConnection?.WaitForExit(ms);

        protected override void OnDetachedFromLogicalTree(LogicalTreeAttachmentEventArgs e)
        {
            base.OnDetachedFromLogicalTree(e);

            // The remembered top level goes with the tree it belonged to. A re-parented view finds
            // the new one on its next frame.
            _topLevel = null;

            // Nothing left to unwind, and nothing that wants unwinding twice.
            if (_disposed)
                return;

            // Mirror of the guard in OnAttachedToLogicalTree, which already notes that _terminal is null
            // during initial attachment because OnInitialized has not fired yet. Attachment is NOTIFIED in
            // that window, so a handler that re-parents the view on attach detaches it while the emulator
            // still does not exist — and every unsubscribe below then throws.
            //
            // CleanupProcess still runs: a view can have been handed a connection through AttachConnection
            // without ever having been initialised, and that connection still has to be let go.
            if (_terminal == null)
            {
                if (!_suppressCleanupOnDetach)
                    CleanupProcess();
                return;
            }

            UnsubscribeTerminalEvents();

            // A view detached mid-update must not keep the gate closed: a view re-attached inside
            // that window would start out refusing to paint for no reason.
            _atomicUpdate = false;

            if (!_suppressCleanupOnDetach)
                CleanupProcess();
        }

        protected override void OnPointerExited(PointerEventArgs e)
        {
            base.OnPointerExited(e);
            // Re-entering begins a new motion stream. Its first position is meaningful even when it
            // happens to be the same edge cell as the final event before the pointer left.
            _lastReportedMotion = null;
            ClearHoveredUrl();
        }

        private async Task SendToPtyAsync(string data, CancellationToken ct = default)
        {
            InputSent?.Invoke(this, data);

            // Capture the connection reference locally to avoid any potential race conditions
            var ptyConnection = _ptyConnection;
            if (ptyConnection == null || string.IsNullOrEmpty(data))
                return;

            await _semaphore.WaitAsync(ct).ConfigureAwait(false);
            try
            {
                // Re-asked after the wait, not just captured before it.
                //
                // The capture above stops the reference changing mid-write, which is a different
                // problem from this one. Waiting on the semaphore is an await, and a queue of
                // keystrokes waiting behind a slow write can sit here across a detach or a relaunch --
                // at which point the captured connection is one the view has handed back to its owner,
                // and writing to it types this view's input into somebody else's process.
                //
                // Dropped rather than redirected to the current connection. Input aimed at a process
                // that is no longer here belongs to nothing: sending it onwards would put half a
                // command line into whatever replaced it.
                if (!ReferenceEquals(_ptyConnection, ptyConnection))
                    return;

                var bytes = Utf8NoBom.GetBytes(data);
                await ptyConnection.WriterStream.WriteAsync(bytes, 0, bytes.Length, ct).ConfigureAwait(false);
                await ptyConnection.WriterStream.FlushAsync(ct).ConfigureAwait(false);
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"[{_instanceId}] Error writing to PTY: {ex.Message}");
            }
            finally
            {
                _semaphore.Release();
            }
        }

        /// <summary>
        /// Drive this view from a PTY the CALLER owns, instead of one the view spawns.
        /// </summary>
        /// <remarks>
        /// <para>The view already knows how to render a PTY and report its exit; what it cannot currently do is
        /// take one it did not create. A host that keeps connections alive across UI changes — a pane that is
        /// closed and reopened, a session moved between tabs, a process that must outlive the control showing
        /// it — has to own the <see cref="IPtyConnection"/> itself, and today there is no way to hand it over.</para>
        /// <para>Ownership follows the caller. An attached connection is neither killed NOR disposed when the
        /// view is cleaned up — it is unsubscribed and its reader stopped, which detaches this view without
        /// stopping the process behind it. (Disposing would stop it: closing the pty ends the child on every
        /// platform.) A connection the view spawned through <see cref="LaunchProcess()"/> is killed and disposed
        /// as before. <see cref="DetachConnection"/> does the same thing on demand.</para>
        /// <para>It also makes the exit paths testable. A test can hand the view a connection whose child has
        /// exited but not yet been reaped — the window the EOF/reap handling exists for — and assert what gets
        /// reported, instead of racing a real shell and hoping to land in it.</para>
        /// </remarks>
        public void AttachConnection(IPtyConnection connection)
        {
            ArgumentNullException.ThrowIfNull(connection);

            CleanupProcess();
            _externalConnection = true;
            _processCts = new CancellationTokenSource();

            // Same ordering as the spawn path: publish the connection, SUBSCRIBE, then start the reader. An
            // attached connection may already have a live process behind it, so an exit can arrive immediately
            // — subscribing after the reader starts is a window in which it is missed entirely.
            InstallConnection(connection);
            connection.ProcessExited += OnPtyProcessExited;

            // Bytes a detached reader stole before this attach are the EARLIEST unread output, so
            // replaying them before our own reader starts preserves stream order exactly -- consume
            // them through the same pipeline a read would. After the loop below starts, that
            // guarantee is gone, which is why the claim happens here and not lazily.
            if (PendingHandoverBytes.ClaimOnAttach(connection) is { Length: > 0 } parked)
            {
                var replayLatch = true;   // mid-session bytes; readiness must not re-announce
                ConsumeOutputChunk(parked, ref replayLatch, _processCts.Token);
            }

            // A thread of its own, not the pool — see ReadPtyOutputAsync for why the read is blocking.
            //
            // No readiness wait here, unlike the spawn path, and that is deliberate. AttachConnection is
            // synchronous and called from the UI thread; blocking it for up to five seconds would freeze the
            // app to protect against losing a few bytes. Subscribing above already removes the part that
            // matters — an exit can no longer be missed — and for an attached connection the caller already
            // owned it, so output from before the attach was never ours to catch.
            // The token is read HERE, not inside the lambda. Read there it is a field access that
            // happens on the new thread whenever it gets scheduled -- and CleanupProcess nulls
            // _processCts, so a relaunch or a close landing in that gap killed the reader with an
            // unobserved NullReferenceException before it had read a byte. Nothing reports that: the
            // task is discarded, so the exception goes nowhere and the terminal simply never shows
            // output.
            var readerToken = _processCts.Token;

            _readLoopTask = Task.Factory.StartNew(
                () => ReadPtyOutputAsync(connection, readerToken),
                CancellationToken.None,
                TaskCreationOptions.LongRunning | TaskCreationOptions.DenyChildAttach,
                TaskScheduler.Default).Unwrap();
        }

        /// <summary>
        /// Stop following the current connection and hand it back, without stopping the process behind it.
        /// </summary>
        /// <returns>The connection that was detached, or <c>null</c> if none was attached.</returns>
        /// <remarks>
        /// <para>Detaching already happens implicitly — closing the view, or attaching a replacement, does it —
        /// but only as a side effect of cleanup, where it is easy to get wrong. It was wrong here until
        /// recently: cleanup disposed the connection and a comment called that the detach, when disposing is
        /// what ends the child. Giving the operation a name is what makes that mistake visible next time.</para>
        /// <para>Ownership passes to the caller for whatever it returns, including a connection this view
        /// spawned itself — detaching one of those hands over a process the view would otherwise have killed,
        /// so the caller must dispose it when done. The view is left with nothing attached and
        /// <see cref="IsLive"/> false.</para>
        /// </remarks>
        public IPtyConnection? DetachConnection()
        {
            IPtyConnection? connection;
            lock (_exitGate)
            {
                connection = _ptyConnection;
            }

            if (connection is null)
            {
                return null;
            }

            // Marked external BEFORE cleanup, which is what makes cleanup let it live: the same flag the
            // attach path sets, meaning exactly the same thing — this process is somebody else's now.
            _externalConnection = true;
            var readLoop = _readLoopTask;
            _readLoopTask = null;

            // Marked ownerless BEFORE cleanup, and the ordering is load-bearing. The read loop
            // parks a stolen chunk only when the connection is marked detached; it decides to
            // steal the moment cleanup swaps _ptyConnection out. Marking afterwards left a
            // window -- cleanup done, mark not yet set -- where a chunk arriving right then was
            // dropped as if an owner had attached, when none had. Before cleanup there is no
            // such window: while the view still owns the connection the loop delivers normally
            // and never consults the mark.
            PendingHandoverBytes.NoteDetached(connection);
            CleanupProcess();

            if (connection.SupportsCancellableRead)
            {
                // CleanupProcess cancelled the token, and a cancellable read honours it while parked
                // -- so the loop is unwinding NOW, having consumed nothing. Waiting for it makes the
                // handover deterministic: when this returns, exactly zero readers hold the stream,
                // and the next owner's first read sees the next byte the process writes. The timeout
                // is a ceiling for a loop mid-chunk, not an expected cost; a loop that outlives it
                // parks its final chunk like a blocking one would, so nothing is lost either way.
                try { readLoop?.Wait(TimeSpan.FromSeconds(2)); }
                catch (AggregateException) { /* the loop's own exit paths already spoke for it */ }
            }
            else
            {
                // A blocking reader cannot be stopped without closing the stream, so it stays parked
                // until the process next speaks -- see the KNOWN LIMITATION below. What CHANGED: the
                // chunk that finally unparks it is no longer simply lost. It is parked in
                // PendingHandoverBytes, and an owner attaching afterwards replays it first, in
                // order. Only a chunk stolen AFTER the new owner attached is dropped, because late
                // delivery could reorder -- and reordered output corrupts where a gap merely gaps.
            }

            // KNOWN LIMITATION -- for BLOCKING-mode connections only, as of issue #123's fix.
            // A connection whose SupportsCancellableRead is true has no such window: its loop was
            // cancelled and awaited above, consuming nothing.
            //
            // For the rest: this does not stop the reader. That thread is parked inside a SYNCHRONOUS Read on the
            // connection's stream, and the only way to make such a read return is to close the stream
            // underneath it — which is exactly what must not happen here, since the stream is what is
            // being handed over. Cancelling _processCts does not touch a blocking read.
            //
            // So for a quiet process the thread stays parked indefinitely, holding this view, its
            // emulator and its scrollback alive through the loop's closure. And when the process does
            // write, that thread takes the chunk: the loop now notices it is no longer the owner and
            // stops without painting it anywhere, which is better than delivering another owner's
            // output into this view, but the bytes are still gone rather than delivered to the new
            // owner.
            //
            // Fixing it properly means deciding what a handover IS at the API level -- the detached
            // connection would have to carry its reader, or carry the bytes already taken off the
            // stream, so the new owner resumes rather than races. That is a public contract change,
            // and it is not being made quietly in a bug fix.
            return connection;
        }

        /// <summary>
        /// Launch the terminal process with the current Process, ProcessArgs, and StartingDirectory properties. If the process is already running, it will be
        /// terminated and replaced with a new instance using the updated properties. 
        /// </summary>
        /// <returns></returns>
        /// <exception cref="InvalidOperationException"></exception>
        /// <remarks>
        /// A no-op under a XAML designer. The previewer renders live controls and runs the handlers
        /// wired to them, so both the automatic launch in OnLoaded and an explicit call from a
        /// consumer's code reach here inside Visual Studio's and Rider's designers -- and a preview
        /// that rebuilds on every edit would spawn a child process per refresh, none of which the
        /// developer asked for or can see exit. The check sits HERE rather than at the automatic
        /// caller so one guard covers both paths. Design.IsDesignMode is set by the previewer's
        /// entry point before the AppBuilder runs, so it is already true when the first control loads.
        /// </remarks>
        public async Task LaunchProcess()
        {
            if (Design.IsDesignMode)
                return;

            CleanupProcess();
            _externalConnection = false;   // this view owns what it spawns

            try
            {
                _processCts = new CancellationTokenSource();
                // NOT reset here: the interlock is armed by InstallConnection, together with the connection
                // itself. Arming it early opens a window in which the OUTGOING connection is still the live one
                // AND the flag is clear, which is the same defect with the operands swapped.

                // Determine the process to launch based on OS if not explicitly set
                string processToLaunch = Process;
                if (string.IsNullOrEmpty(processToLaunch))
                {
                    processToLaunch = RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "cmd.exe" : "bash";
                }

                // Held in a local as well as raised, because the PTY needs a directory that is definitely not
                // null and the field is only non-null by way of what SetAndRaise just did to it.
                var workingDirectory = StartingDirectory ?? Environment.CurrentDirectory;
                SetAndRaise(CurrentDirectoryProperty, ref _currentDirectory, workingDirectory);

                var options = new PtyOptions
                {
                    Name = processToLaunch,
                    Cols = _terminal.Cols,
                    Rows = _terminal.Rows,
                    Cwd = workingDirectory,
                    App = processToLaunch,
                    VerbatimCommandLine = VerbatimCommandLine
                };

                // Merged by the PTY layer into the environment the child would otherwise inherit, so a caller
                // adding one variable does not have to rebuild the rest.
                //
                // TERM is set here because nothing else sets it. The PTY layer does not, and on Windows the
                // environment has none to inherit, so the child was being launched with TERM absent entirely
                // -- which every curses-based program then has to guess around. `ucs-detect` reported this
                // terminal as "vtwin10", which is not something the terminal said: it is blessed's Windows
                // fallback for "no TERM, assume a Win10 console", and it costs the program every capability
                // it would otherwise have used.
                //
                // xterm-256color and not xterm-kitty. TERM is a claim about the WHOLE terminal, and
                // xterm-kitty asserts the keyboard protocol, notifications, text sizing and clipboard as well
                // as the graphics. The keyboard protocol matters most: it changes how applications SEND input,
                // so claiming it without answering risks breaking key handling to win a format negotiation
                // that already falls back correctly.
                var environment = EnvironmentVariables is null
                    ? new Dictionary<string, string>()
                    : new Dictionary<string, string>(EnvironmentVariables);

                if (!environment.ContainsKey("TERM"))
                    environment["TERM"] = DefaultTermType;

                // COLORTERM alongside it, because TERM cannot carry this. A terminfo entry describes an
                // indexed palette, so xterm-256color says "256 colours" and a program quantises to them --
                // this terminal takes full RGB, and that would be discarding colour it could have shown.
                // It is the first thing consulted by everything that looks, ahead of terminfo entirely.
                if (!environment.ContainsKey("COLORTERM"))
                    environment["COLORTERM"] = DefaultColorTerm;

                options.Environment = environment;


                // Add arguments if provided
                if (ProcessArgs != null && ProcessArgs.Count > 0)
                {
                    options.CommandLine = ProcessArgs.ToArray();
                }

                var spawned = await PtyProvider.SpawnAsync(options, _processCts.Token);
                InstallConnection(spawned);

                // Subscribe to process exit event for reliable exit detection
                spawned.ProcessExited += OnPtyProcessExited;

                // Start reading from the PTY connection, and do not continue until the loop is actually
                // reading. The loop is handed THIS connection so a relaunch cannot redirect it onto the next
                // one — see ReadPtyOutputAsync.
                //
                // The process is already running the moment SpawnAsync returns, so every instant before the
                // first read is a window in which it can write, finish, and have its output discarded. A
                // shell that exits immediately loses EVERYTHING; one that lives loses its opening prompt and
                // banner, which presents as a pane that opened blank.
                //
                // Measured downstream over the same Porta.Pty layer: starting 24 short-lived shells at once
                // lost 23 of 24 outputs entirely while reporting a clean exit 0. It never reproduced on an
                // idle developer machine and was near-total on a contended CI box.
                var readerUp = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
                _readLoopTask = Task.Factory.StartNew(
                    () => ReadPtyOutputAsync(spawned, _processCts.Token, readerUp),
                    CancellationToken.None,
                    TaskCreationOptions.LongRunning | TaskCreationOptions.DenyChildAttach,
                    TaskScheduler.Default).Unwrap();

                // Bounded and never fatal: if the reader cannot start, the terminal behaves exactly as it
                // used to rather than hanging the caller that opened it.
                await Task.WhenAny(readerUp.Task, Task.Delay(TimeSpan.FromSeconds(5))).ConfigureAwait(true);
            }
            catch (Exception ex)
            {
                await Dispatcher.UIThread.InvokeAsync(() =>
                {
                    _terminal.WriteLine($"Error launching process: {ex.Message}\n");
                });
            }
        }

        /// <summary>
        /// Launch the terminal process with the specified parameters, updating the Process, ProcessArgs, and StartingDirectory properties. 
        /// If the process is already running, it will be terminated and replaced with a new instance using the updated properties.
        /// </summary>
        /// <param name="startingDirectory"></param>
        /// <param name="process"></param>
        /// <param name="args"></param>
        /// <returns></returns>
        public virtual async Task LaunchProcess(string? startingDirectory, string process, params string[] args)
        {
            StartingDirectory = startingDirectory;
            Process = process;
            ProcessArgs = args ?? Array.Empty<string>();
            await LaunchProcess();
        }

        /// <summary>
        /// Runs one chunk of process output through everything a chunk gets: the sniffer event, the
        /// emulator, scroll-follow, readiness, IME and the repaint.
        /// </summary>
        /// <remarks>
        /// Extracted from the read loop so an ATTACH can replay bytes a detached reader parked
        /// (<see cref="PendingHandoverBytes"/>) through the identical pipeline — a second,
        /// almost-the-same delivery path would drift. <paramref name="shellReadyPosted"/> is the
        /// loop's once-per-process latch; a replay passes true, because parked bytes are mid-session
        /// output and must not re-announce readiness. <paramref name="cancellationToken"/> is the
        /// loop's token, which two of the posted callbacks compare against the CURRENT process's to
        /// refuse stale delivery — a replay passes the current one.
        /// </remarks>
        private void ConsumeOutputChunk(ReadOnlyMemory<byte> chunk, ref bool shellReadyPosted, CancellationToken cancellationToken)
        {

            // Guarded so an unsubscribed terminal pays nothing: without it every chunk allocates a
            // closure and queues a dispatcher callback for no subscriber. The ?.Invoke inside still
            // covers the race where the last handler unsubscribes between here and delivery.
            if (OutputReceived != null)
            {
                if (_outputOnReadTask)
                {
                    // Straight through, on this thread. No staleness guard is needed here that the
                    // loop does not already provide -- and what provides it is the check after the
                    // READ, not the one in the while condition this comment used to cite. That one
                    // is asked before a read that blocks for the whole idle life of the process, so
                    // it says nothing about who owns the bytes it eventually returns. A sniffer was
                    // being handed another connection's output on the strength of it.
                    //
                    // The catch matters MORE on this path than on the dispatcher one, and for a
                    // different reason: an escaping exception here propagates into ReadPtyOutputAsync
                    // and ends the read loop, leaving a live process with a frozen view and nothing
                    // reported.
                    try { OutputReceived?.Invoke(this, new OutputReceivedEventArgs(chunk)); }
                    catch { /* a sniffer must never kill the read loop */ }
                }
                else
                {
                    Dispatcher.UIThread.Post(() =>
                    {
                        // Same guard ShellReady uses: the callback can still be queued when a relaunch
                        // swaps the process out underneath it, and without this a consumer sees the old
                        // process's bytes attributed to the new one.
                        if (_processCts?.Token != cancellationToken)
                            return;

                        try { OutputReceived?.Invoke(this, new OutputReceivedEventArgs(chunk)); }
                        catch { /* a sniffer must never take the app down */ }
                    });
                }
            }

            // Snapshot before write so we can detect buffer growth (MaxScrollback
            // increases when _terminal.Write adds lines; ScrollToBottom only moves
            // ViewportY and does not affect buffer length).
            var oldMax = MaxScrollback;
            var oldY = _terminal.Buffer.ViewportY;

            // Sampled BEFORE the write. Ordering is the subtle part: once _terminal.Write has run
            // YBase has already advanced, so a view that genuinely WAS at the tail reads as
            // not-following and the terminal stops following its own output.
            //
            // Alternate-buffer apps (vim, htop) position their own cursor and the scroll below is
            // skipped for them regardless, so they count as following.
            _followBottom = _isAlternateBuffer || (_autoScroll && _terminal.Buffer.IsAtBottom);

            lock (_terminalLock)
            {
                // Any capture taken before this write describes a buffer that no longer exists
                // once it lands; bumping FIRST means a capture published from inside the write —
                // the ESU handler — carries the new generation and is current on arrival.
                Interlocked.Increment(ref _liveWriteGeneration);

                // Declared for the renderer BEFORE the first byte parses. An application's atomic
                // update only protects from the BSU byte onward — a paint landing between this
                // chunk's arrival and its BSU being reached saw "generation moved, no update open",
                // declined the capture, and read the buffer mid-write: the residual tear. While
                // this flag is up the renderer prefers the last COMPLETE capture over the live
                // buffer; once the write finishes, live is quiescent and serves as before.
                _bufferWriteInProgress = true;

                try
                {
                    // Bytes straight through, no UTF-16 round trip. This fixes a real defect, not just
                    // an allocation: decoding each read on its own corrupts any multi-byte sequence the
                    // read boundary happens to split, and pty reads end wherever they end. The parser
                    // carries the partial sequence into the next chunk instead -- which is what
                    // OutputReceivedEventArgs.Bytes has been promising subscribers all along.
                    _terminal.Write(chunk.Span);
                }
                finally
                {
                    _bufferWriteInProgress = false;
                }

                // See _inputStartRow. A change of row means the shell drew something new, so the
                // recorded input start is stale — but where the prompt ENDS is not known until the
                // user types, since the prompt may still be arriving.
                int cursorRow = _terminal.Buffer.YBase + _terminal.Buffer.Y;
                if (cursorRow != _lastOutputRow)
                {
                    _lastOutputRow = cursorRow;
                    _inputStartPending = !_semanticPrompt;
                }

                // For output that never declares a frame, the chunk boundary is the closest thing
                // to one: the buffer is quiescent here, still under the lock, on the thread that
                // owns it. Skipped mid-update — a capture there would freeze exactly the half-drawn
                // state this machinery exists to keep off the screen — and throttled, because a
                // chunk boundary is worth at most a paint interval of freshness.
                if (!_atomicUpdate)
                    _frameCapture.PublishThrottled(_terminal, Interlocked.Read(ref _liveWriteGeneration));
            }

            // Signal on the first chunk only. Posting per chunk would keep queueing UI-thread
            // callbacks for the life of the process, which is pure overhead once the shell is
            // long since ready and adds up under high-throughput output.
            if (!shellReadyPosted)
            {
                shellReadyPosted = true;
                Dispatcher.UIThread.Post(() =>
                {
                    // The callback can still be queued when a relaunch swaps the process out
                    // underneath it; the token identifies which process it belongs to.
                    if (_processCts?.Token != cancellationToken)
                        return;

                    ShellReady?.Invoke(this, EventArgs.Empty);
                });
            }

            // Auto-scroll to bottom when new content arrives, but only in normal buffer.
            // Alternate buffer (used by full-screen apps like vim, htop, asciiquarium)
            // handles its own cursor positioning and shouldn't be scrolled.
            if (!_isAlternateBuffer)
            {
                if (_followBottom)
                {
                    _terminal.Buffer.ScrollToBottom();
                }
                else if (!_autoScroll && _terminal.Buffer.ViewportY != oldY)
                {
                    // Gating ScrollToBottom is NOT enough to mean "never auto-scrolls", which is what
                    // this property advertises. The emulator advances ViewportY itself as YBase grows
                    // whenever the view is sitting at the bottom, so with the scroll merely skipped a
                    // terminal with auto-scroll off still tracked the tail exactly — measured at
                    // ViewportY == MaxScrollback after every chunk, indistinguishable from on.
                    //
                    // ScrollToBottom only ever mattered for a view that had been scrolled AWAY, which
                    // is why skipping it looks sufficient and is not. Holding the position here is
                    // what actually hands the viewport to the host.
                    _terminal.Buffer.ViewportY = Math.Min(oldY, MaxScrollback);
                }

                // Read and notified either way: a view parked in the scrollback still needs its
                // scrollbar to learn that the buffer grew underneath it.
                var newY = _terminal.Buffer.ViewportY;
                var newMax = MaxScrollback;

                if (oldMax != newMax || oldY != newY)
                {
                    Dispatcher.UIThread.Post(() =>
                    {
                        if (oldMax != newMax)
                            RaisePropertyChanged(MaxScrollbackProperty, oldMax, newMax);
                        if (oldY != newY)
                            RaisePropertyChanged(ViewportYProperty, oldY, newY);
                    });
                }
            }

            // Notify IME of cursor position change after terminal processes data
            NotifyInputMethodCoalesced();

            // Output is the only thing that can start or stop an animation, and the clock is
            // a dispatcher timer, so the decision has to be made on the UI thread. The check
            // behind it is a walk of a list that is empty for a terminal showing text.
            //
            // Coalesced for the same reason as the IME notification above: this is a state SYNC,
            // so N queued calls and one queued call reach the same answer, and only the count
            // differs.
            if (Interlocked.CompareExchange(ref _animationSyncQueued, 1, 0) == 0)
            {
                Dispatcher.UIThread.Post(() =>
                {
                    Interlocked.Exchange(ref _animationSyncQueued, 0);
                    SyncAnimationClock();
                });
            }

            RequestPaint();
        }

        /// <summary>
        /// Tells the IME its cursor rectangle and surrounding text have moved, at most once per
        /// dispatcher drain no matter how many chunks asked.
        /// </summary>
        /// <remarks>
        /// <para>Both notifications say "what you cached is stale, come and re-read it" — they carry
        /// no payload of their own. So N of them queued back to back and one of them queued reach the
        /// identical state, and the only difference is how much UI-thread time is spent getting there.</para>
        /// <para>That difference is the whole bug. This is called once per pty CHUNK, which for a
        /// full-screen animation redrawing every cell is hundreds of times a second — far faster than
        /// the UI thread can retire them, because on Windows NotifyCursorRectangleChanged reaches
        /// IMM32 (ImmSetCandidateWindow), which sends messages and so RE-ENTERS the window procedure
        /// on its way through. The dispatcher queue then grows without bound, the message loop never
        /// gets back to pumping input or painting, and the window goes "Not Responding" while the
        /// child process is still happily writing. Measured with libcaca's cacademo: unresponsive
        /// within about five seconds, responsive indefinitely once coalesced.</para>
        /// <para>The latch is cleared BEFORE the notifications rather than after, which is what makes
        /// coalescing lossless. Cleared after, a chunk landing while the notification runs would see
        /// the latch still set, skip, and then find it cleared with nothing queued — and the IME would
        /// be left reading a line the buffer no longer holds until some later chunk happened along.</para>
        /// </remarks>
        private void NotifyInputMethodCoalesced()
        {
            // Coalescing alone was not enough, and a dump of a frozen window is what said so: the
            // UI thread sat in ImmSetCandidateWindow, reached from Imm32InputMethod.SetCursorRect,
            // while the pty reader was parked in ReadFile with nothing to do. The terminal was not
            // behind on its input at all -- it was spending the UI thread inside the IME.
            //
            // One notification per dispatcher drain is still one IMM32 call per drain, and against
            // a full-screen animation that is tens of blocking calls a second, for a cursor the
            // user is not typing at. So the OUTPUT-driven notification is rate limited as well as
            // coalesced. An IME needs the rectangle to be right when composition starts, not to
            // track a running animation; a tenth of a second is far below anything a person can
            // act on and two orders of magnitude off the flood.
            //
            // Deliberately time-based rather than "only when the cursor moved": a full-screen
            // application moves the cursor on every frame by definition, so a movement test admits
            // exactly the case that hurts and excludes the quiet one it would help.
            // Nothing unfocused can be composing, so nothing unfocused needs telling. This is
            // the free half of the fix: a terminal in a background tab or an unfocused window now
            // costs nothing at all, however hard its process is writing.
            if (!_imeFocused)
                return;

            long now = Stopwatch.GetTimestamp();
            long last = Interlocked.Read(ref _imeNotifiedAt);

            if (last != 0 && Stopwatch.GetElapsedTime(last, now) < ImeNotifyInterval)
                return;

            if (Interlocked.CompareExchange(ref _imeNotifyQueued, 1, 0) != 0)
                return;

            Interlocked.Exchange(ref _imeNotifiedAt, now);

            Dispatcher.UIThread.Post(() =>
            {
                Interlocked.Exchange(ref _imeNotifyQueued, 0);

                _inputMethodClient?.NotifyCursorRectangleChanged();

                // And the TEXT around it, which the client advertises support for and was
                // never told about. An IME asks once, caches, and waits to be told -- so it
                // was composing against whatever the line held the first time it looked.
                _inputMethodClient?.NotifySurroundingTextChanged();
            });
        }

        /// <param name="connection">
        /// The connection this loop reads, passed in rather than re-read from the field on every
        /// iteration. A read is an await, and a relaunch during one swaps the field — so a loop that
        /// consults _ptyConnection afterwards can find itself operating on the NEXT process: waiting
        /// on it, reading its exit code, and claiming the exit interlock LaunchProcess had just
        /// reset for it, which swallows that process's own exit.
        /// </param>
        private async Task ReadPtyOutputAsync(
            IPtyConnection connection, CancellationToken cancellationToken, TaskCompletionSource? up = null)
        {
            // Raised BEFORE the first read, and deliberately not after one. Signalling after a read would
            // make readiness depend on the process PRODUCING output, so a shell that prints nothing on
            // startup would never signal and every launch would pay the full five-second wait. The guarantee
            // wanted is only that the loop is running and the next thing it does is read.
            //
            // The window this leaves — between the signal and the read — is closed by the caller subscribing
            // to ProcessExited before starting the loop, so an exit landing in it is still seen.
            up?.TrySetResult();

            try
            {
                var buffer = new byte[0x40000];

                // Local rather than a field: this method runs once per launch, so the flag is
                // per-process by construction and a chunk still in flight from a previous process
                // cannot consume the current one's signal.
                var shellReadyPosted = false;

                while (!cancellationToken.IsCancellationRequested && ReferenceEquals(_ptyConnection, connection))
                {
                    // SYNCHRONOUS, on the thread StartNew handed this loop. `await ReadAsync` undid the
                    // LongRunning hint entirely: LongRunning owns a dedicated thread only up to the first
                    // await that YIELDS, and every continuation after that is scheduled on the THREAD POOL.
                    // Worse, the stream underneath is a FileStream opened isAsync: false on Windows, whose
                    // ReadAsync performs no overlapped I/O — it parks a POOL thread in a blocking read for
                    // the whole life of the process, because ConPTY does not signal EOF while the
                    // pseudoconsole is open.
                    //
                    // Measured downstream over the same layer, 24 concurrent short-lived processes on a
                    // 4-vCPU box: time-to-first-output was 137 ms with a dedicated thread and 7546 ms
                    // pooled, and under load the pooled form lost output entirely rather than merely
                    // delaying it. A blocking read on a thread we own cannot be starved, and costs one
                    // thread per terminal — which the pooled form was already costing, minus the scheduling.
                    //
                    // Cancellation is by teardown rather than by token: disposing the connection closes the
                    // stream and the blocking read throws, which the catch below handles.
                    int bytesRead;
                    if (connection.SupportsCancellableRead)
                    {
                        // A connection that PROMISES cancellable reads gets the awaited form: parked
                        // on the pty layer's poller rather than on this thread, and the token lands
                        // while waiting for data -- before read(2) runs -- so a detach unparks the
                        // loop without consuming a byte and without touching the stream it is
                        // handing over. The measured case against `await ReadAsync` (137 ms vs
                        // 7,546 ms, output lost under load) damned SYNC-OVER-ASYNC -- fake async
                        // over a blocking descriptor parking pool threads -- and says nothing about
                        // an event-driven wait, which is what the capability certifies.
                        try
                        {
                            bytesRead = await connection.ReaderStream
                                .ReadAsync(buffer, 0, buffer.Length, cancellationToken)
                                .ConfigureAwait(false);
                        }
                        catch (OperationCanceledException)
                        {
                            // A detach or teardown. Nothing was consumed -- that is the guarantee
                            // the capability advertises, and Porta.Pty tests it.
                            break;
                        }
                    }
                    else
                    {
                        bytesRead = connection.ReaderStream.Read(buffer, 0, buffer.Length);
                    }

                    // Asked AGAIN, on the other side of the read.
                    //
                    // The condition on the while loop is the same question, and asking it there is
                    // not enough on its own: this read blocks for as long as the process stays quiet,
                    // which at an idle prompt is indefinitely. A detach or a relaunch lands in that
                    // window routinely -- it is the window a detach is most likely to land in, being
                    // nearly all of the loop's life -- and the chunk that ends the read then belongs
                    // to a connection this view no longer owns.
                    //
                    // Everything below assumed otherwise. The bytes went into _terminal, so output
                    // meant for whoever now owns the process was painted into this view and lost to
                    // them; OutputReceived fired for it, under a comment asserting the check above
                    // had already made that impossible; and ShellReady could be raised for a process
                    // that is not this view's.
                    //
                    // Breaking rather than continuing: the while condition would stop the loop on the
                    // next pass anyway, and this makes it stop without first reading a SECOND chunk
                    // out of a stream that is not ours to read.
                    //
                    // The chunk in hand is not simply dropped any more. If the connection's next
                    // owner has not attached yet, these are by construction the earliest unread
                    // bytes, and parking them lets that owner replay them FIRST -- lossless, in
                    // order. Once an owner is attached its own reader races this one on the same
                    // descriptor, and late delivery could interleave into the middle of what it
                    // already consumed -- inside an escape sequence, even. Reordered output
                    // corrupts; a gap merely gaps. So then, and only then, the chunk is dropped.
                    if (!ReferenceEquals(_ptyConnection, connection))
                    {
                        if (bytesRead > 0)
                            PendingHandoverBytes.TryPark(connection, buffer.AsSpan(0, bytesRead));
                        break;
                    }

                    if (bytesRead == 0)
                    {
                        // Process has exited — fallback in case OnPtyProcessExited didn't fire first.
                        //
                        // EOF on the master side means the child closed its end, which can beat the
                        // child actually being REAPED — and until it is, ExitCode is still its
                        // default 0. Reading it straight away reports a clean exit for a process
                        // that failed, whenever this path wins the race against OnPtyProcessExited.
                        //
                        // Reaping happens BEFORE the interlock is claimed, which does two things:
                        // it makes the exit code readable, and it gives OnPtyProcessExited — which
                        // carries the code authoritatively — its chance to win the race instead of
                        // being locked out by a claim staked before we knew anything. The child is
                        // gone by definition, so this returns almost immediately; the timeout is a
                        // ceiling for a pathological reap, not an expected cost.
                        var reaped = false;
                        try { reaped = connection.WaitForExit(ExitReapGraceMs); }
                        catch { /* never let reaping be the reason output stops */ }

                        // A child that will not reap inside the grace period leaves no trustworthy
                        // code, and the one we would otherwise read is 0 — the single wrong answer
                        // that reads as SUCCESS. So it is still not reported here.
                        //
                        // It is NOT abandoned either. Leaving the interlock unclaimed means no
                        // ProcessExited is raised AT ALL if the pty layer's own event never fires
                        // — and a host that is never told the process ended cannot leave the state
                        // it entered when the process started. Trading "no wrong exit code" for
                        // "no notification" loses more than it saves; the notification is the part
                        // a host cannot reconstruct.
                        //
                        // The child is dead by definition, so the reap WILL land — the grace period
                        // is only a ceiling on how long this READ LOOP waits for it. Hand the wait
                        // off, so the loop ends now and the host still hears about it.
                        if (!reaped)
                        {
                            ReapInBackground(connection);
                        }

                        // TryClaimExit rather than a bare interlock: this loop may have been waiting on a read
                        // while a relaunch replaced the connection, in which case the exit it is holding belongs
                        // to a process this view has already moved on from.
                        if (reaped && TryClaimExit(connection))
                        {
                            var exitCode = connection.ExitCode;

                            WriteOwnLine($"\nProcess exited with code: {exitCode}\n");

                            await Dispatcher.UIThread.InvokeAsync(() =>
                            {
                                ProcessExited?.Invoke(this, new ProcessExitedEventArgs(exitCode));
                            });
                        }
                        break;
                    }

                    // Nothing is decoded here any more: the terminal takes bytes, and OutputReceived
                    // carries bytes. The copy is only made when someone is listening -- `buffer` is
                    // reused on the next iteration, and the dispatcher delivery outlives this one --
                    // so an unsubscribed view allocates nothing per read at all.
                    var chunk = OutputReceived != null
                        ? new ReadOnlyMemory<byte>(buffer.AsSpan(0, bytesRead).ToArray())
                        : buffer.AsMemory(0, bytesRead);
                    ConsumeOutputChunk(chunk, ref shellReadyPosted, cancellationToken);
                }
            }
            catch (OperationCanceledException)
            {
                // Expected when cancellation is requested
            }
            catch (Exception ex)
            {
                // Only speak for the connection this loop was reading, and only while it is still the
                // one the view owns.
                //
                // The interlock alone could not answer that. InstallConnection RESETS it as it
                // publishes a new connection, so a stale loop -- one whose stream was closed out from
                // under it by exactly that replacement, which is how it got here -- read the flag as
                // 0 and took it for permission to speak. It then wrote "Error reading from process"
                // into the terminal belonging to its SUCCESSOR: a relaunch that worked, reporting a
                // failure, describing a process that is already gone.
                //
                // ReferenceEquals is asked first because it is the question that was missing. The
                // interlock stays behind it for its original job: a stream closing after the process
                // has already exited is expected, and not worth a line of red.
                if (!ReferenceEquals(_ptyConnection, connection))
                    return;

                // If the process has already exited the stream closing is expected — swallow silently.
                if (_processExitHandled != 0)
                    return;

                WriteOwnLine($"\nError reading from process: {ex.Message}\n");
            }
        }

        /// <summary>
        /// Make <paramref name="connection"/> the live one and arm the exit interlock for it, atomically.
        /// Null clears both — the teardown case.
        /// </summary>
        private void InstallConnection(IPtyConnection? connection)
        {
            lock (_exitGate)
            {
                _ptyConnection = connection;
                Interlocked.Exchange(ref _processExitHandled, 0);
            }
        }

        /// <summary>
        /// Claim the right to report the exit OF THIS CONNECTION. False when somebody already reported it, and
        /// false when the connection is no longer the live one — a stale loop must not speak for its successor.
        /// </summary>
        private bool TryClaimExit(IPtyConnection connection)
        {
            lock (_exitGate)
            {
                if (!ReferenceEquals(_ptyConnection, connection)) return false;
                return Interlocked.Exchange(ref _processExitHandled, 1) == 0;
            }
        }

        /// <summary>
        /// Keep waiting for a child that did not reap inside <see cref="ExitReapGraceMs"/>, off the
        /// read loop, and report the exit when it finally lands.
        /// </summary>
        /// <remarks>
        /// <para>The read loop must not block on this — it is the thing that would otherwise be
        /// pumping output — but the exit still has to be reported, or the host is left believing a
        /// dead process is running.</para>
        /// <para>Claims the same interlock, so if <see cref="OnPtyProcessExited"/> gets there first
        /// with the authoritative code, this stays silent. If the ceiling expires the exit IS still
        /// reported, with <see cref="ProcessExitedEventArgs.ExitCodeKnown"/> false — "ended, outcome
        /// unreadable" is honest, whereas 0 would read as success and silence reads as running.</para>
        /// <para>The connection may be disposed underneath this at any point (a relaunch, a close).
        /// That is not an error worth surfacing: it means the exit is moot.</para>
        /// </remarks>
        private void ReapInBackground(IPtyConnection connection)
        {
            _ = Task.Run(async () =>
            {
                var deadline = DateTime.UtcNow.AddMilliseconds(ExitReapCeilingMs);
                var reaped = false;

                while (DateTime.UtcNow < deadline)
                {
                    if (Volatile.Read(ref _processExitHandled) != 0) return;   // someone else reported it
                    try
                    {
                        if (connection.WaitForExit(ExitReapPollMs)) { reaped = true; break; }
                    }
                    catch
                    {
                        return;   // disposed / gone — nothing left to report about
                    }
                    await Task.Yield();
                }

                if (!TryClaimExit(connection)) return;

                int? code = null;
                if (reaped)
                {
                    try { code = connection.ExitCode; } catch { /* fall through as unknown */ }
                }

                WriteOwnLine(code is { } c
                    ? $"\nProcess exited with code: {c}\n"
                    : "\nProcess exited\n");

                await Dispatcher.UIThread.InvokeAsync(() =>
                {
                    ProcessExited?.Invoke(this, code is { } c
                        ? new ProcessExitedEventArgs(c)
                        : ProcessExitedEventArgs.UnknownCode());
                });
            });
        }

        private void OnPtyProcessExited(object? sender, PtyExitedEventArgs e)
        {
            // Interlocked ensures only one of (event, EOF path, exception path) prints the message.
            // Claims for the connection that raised it, so a late event from a replaced connection cannot
            // speak for its successor either. A null sender predates this and is treated as the live one.
            if (sender is IPtyConnection origin ? !TryClaimExit(origin)
                                                : Interlocked.Exchange(ref _processExitHandled, 1) != 0)
                return;

            WriteOwnLine($"\nProcess exited with code: {e.ExitCode}\n");

            Dispatcher.UIThread.InvokeAsync(() =>
            {
                // Raise event on UI thread so subscribers can safely update UI
                var args = new ProcessExitedEventArgs(e.ExitCode);
                ProcessExited?.Invoke(this, args);
            });
        }

        private void CleanupProcess()
        {
            _processCts?.Cancel();
            ReleaseImageBitmaps();

            if (_ptyConnection != null)
            {
                try
                {
                    // Unsubscribe from event before cleanup
                    _ptyConnection.ProcessExited -= OnPtyProcessExited;

                    // An ATTACHED connection belongs to its owner: neither killed NOR disposed. Closing or
                    // re-parenting a view must not stop the process behind it, and Dispose does stop it —
                    // disposing without any Kill() leaves the child dead within 300ms on both Windows
                    // (PseudoConsoleConnection) and Unix, where closing the master fd sends SIGHUP to the
                    // foreground process group. An earlier revision of this code disposed unconditionally and
                    // described it as the detach; it was the opposite.
                    //
                    // Detaching needs nothing from Dispose. The unsubscribe above drops this view's event, and
                    // the cancelled _processCts plus the read loop's ReferenceEquals check stop the reader.
                    // Disposing an object the view does not own would be wrong even if the process survived it.
                    if (!_externalConnection)
                    {
                        _ptyConnection.Kill();
                        _ptyConnection.Dispose();
                    }
                }
                catch
                {
                    // Ignore cleanup errors
                }
                finally
                {
                    // Cleared with the flag, under the gate: a loop still unwinding must not find a null
                    // connection paired with a clear flag and conclude it owns the exit.
                    InstallConnection(null);
                }
            }

            _processCts?.Dispose();
            _processCts = null;
        }

    }
}
