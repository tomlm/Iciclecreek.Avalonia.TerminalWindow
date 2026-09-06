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
        /// <summary>
        /// Paints the hits on the rows the viewport is showing.
        /// </summary>
        /// <remarks>
        /// An overlay after the text, exactly as the selection is, and cheap for the same structural
        /// reason the emulator stores hits by row: each visible row asks <c>HitsOnRow</c> once and
        /// the answer is almost always an empty span.
        /// </remarks>
        private void RenderSearchHighlights(DrawingContext context, int viewportY, double scale)
        {
            if (_search is null || _search.Count == 0)
                return;

            for (var screenY = 0; screenY < _terminal.Rows; screenY++)
            {
                var absoluteRow = viewportY + screenY;
                var cellScale = RowCellScale(absoluteRow);
                foreach (var hit in _search.HitsOnRow(absoluteRow))
                {
                    var brush = hit.MatchId == _currentMatchId ? SearchCurrentBrush : SearchHighlightBrush;
                    if (brush is null)
                        continue;

                    // Clamped to the grid. A hit is recorded against the buffer at the width the
                    // line had when it was searched, and a resize narrower than that leaves hits
                    // naming columns that no longer exist -- so the tint was painted hundreds of
                    // pixels past the right edge of the control, over whatever the host had there.
                    //
                    // Clamped to the columns VISIBLE on this row, which on a doubled row is half of
                    // them: each is drawn twice as wide, so the same count would reach twice the
                    // width. Clamping to Cols and then scaling would put the right edge of a hit at
                    // the far end of a control twice as wide as this one.
                    var visibleCols = (int)(_terminal.Cols / cellScale);

                    if (!ClampSpanToGrid(hit.Column, hit.EndColumn, visibleCols,
                                         out var startCol, out var endCol))
                        continue;

                    var x1 = Snap(startCol * _charWidth * cellScale, scale);
                    var x2 = Snap(endCol * _charWidth * cellScale, scale);
                    var y1 = Snap(screenY * _charHeight, scale);
                    var y2 = Snap((screenY + 1) * _charHeight, scale);
                    context.FillRectangle(brush, new Rect(x1, y1, Math.Max(0, x2 - x1), Math.Max(0, y2 - y1)));
                }
            }
        }

        /// <summary>
        /// Gets the operating system process identifier of the launched PTY process.
        /// </summary>
        /// <summary>
        /// Ask for a frame, unless an application is mid-update.
        /// </summary>
        /// <remarks>
        /// <para>Where the atomic-update deadline is enforced, because this is the one place that
        /// already asks the question and it costs a timestamp comparison to answer. An update held
        /// open past the deadline is a broken application rather than a synchronised update — it
        /// set the mode and never cleared it — and the frame is drawn rather than withheld for
        /// ever.</para>
        /// <para>Called from both sides. The PTY reader thread reaches it when output arrives; the
        /// UI thread reaches it from the cursor blink and the animation clock, and from the mouse,
        /// keyboard and selection paths. Nothing here arms or cancels a dispatcher timer, which is
        /// the part the reader thread had no business doing — and a stale tick from that churn could
        /// end a LATER update early and tear the frame. That the flag is read from more than one
        /// thread is why it is volatile: see <c>BeginAtomicUpdate</c>.</para>
        /// <para>So an update left open outlives its deadline only until something asks for a
        /// frame, and output is not the only thing that asks: a blinking cursor on a focused view
        /// asks about twice a second, an animation asks every frame, and any mouse or key that
        /// reaches the view asks at once. Whichever comes first drops the hold and paints. With
        /// none of them — unfocused, nothing animating, no input, no output — the screen keeps the
        /// last COMPLETE frame rather than a half-written one, which is the better of the two and
        /// is not a wedge: the next byte of output recovers it, and both teardown paths clear the
        /// flag outright.</para>
        /// </remarks>
        private void RequestPaint()
        {
            if (_atomicUpdate)
            {
                if (Stopwatch.GetElapsedTime(_atomicUpdateStartedAt) < AtomicUpdateTimeout)
                    return;

                _atomicUpdate = false;
            }

            TerminalRenderThrottle.RequestInvalidate(this);
        }

        /// <summary>
        /// Move the emulator's live colour pair after it has been built, for a host that re-themes.
        /// </summary>
        private void SyncPaletteToBrushes()
        {
            if (_terminal == null)
                return;

            if (Foreground is ISolidColorBrush fg)
                _terminal.Colors.SetForeground(ToRgb(fg.Color));

            if (Background is ISolidColorBrush bg)
                _terminal.Colors.SetBackground(ToRgb(bg.Color));

            static int ToRgb(Color c) => (c.R << 16) | (c.G << 8) | c.B;
        }

        // ---- Host seams for the emulator's clipboard, notification, attention and pointer ----
        //
        // Every handler below is raised from Terminal.Write, and the read loop calls that from the pty
        // READER thread (see StartReading), never the UI thread. So they all marshal, exactly like
        // OnTerminalBellRang and the window handlers above: SetCurrentValue verifies dispatcher access
        // and throws off-thread, RaiseEvent does not verify and instead runs an application's handlers
        // on the reader thread, and Avalonia's Win32 clipboard is thread-affine on the set path. An
        // exception here unwinds through Terminal.Write into the read loop's catch-all, which ends the
        // loop - the terminal shows no further output for the rest of its life.

        /// <summary>Whether a run is nothing but blanks, and so has no ink to put down.</summary>
        /// <remarks>
        /// Spaces only, deliberately. A tab has already been expanded by the emulator, and anything
        /// else that LOOKS blank -- a zero-width space, an ideographic space -- still occupies its
        /// cell in a way a font may render, so it is left to draw.
        /// </remarks>
        private static bool IsBlankRun(string text)
        {
            for (var i = 0; i < text.Length; i++)
            {
                if (text[i] != ' ')
                    return false;
            }

            return text.Length > 0;
        }

        /// <summary>Drops every cached run, so the next frame resolves its brushes again.</summary>
        private void InvalidateRunCaches()
        {
            if (_terminal == null)
                return;

            for (int y = 0; y < _terminal.Buffer.Length; y++)
            {
                var line = _terminal.Buffer.GetLine(y);
                if (line != null)
                    line.Cache = null;
            }

            // The captured lines carry their own copies of those caches, and would replay runs
            // resolved against the palette this invalidation is retiring.
            _frameCapture.InvalidateAll();

            InvalidateVisual();
        }

        /// <summary>
        /// Paints the marks for the rows on screen into the gutter lane.
        /// </summary>
        /// <remarks>
        /// A bar per prompt, coloured by how its command ended, and nothing at all where the host has
        /// set no brush for that case. There is no built-in palette here on purpose: a terminal
        /// picking its own red and green would be picking them for every theme it ever runs under.
        /// </remarks>
        private void DrawGutter(DrawingContext context, double gutter, double scale)
        {
            if (gutter <= 0 || _charHeight <= 0)
                return;

            // Straight over the visible lines rather than through VisibleMarks, which builds a list
            // -- fine for a host asking once, not for a render path asking per frame.
            var lines = _terminal.Buffer.Lines;
            var top = _terminal.Buffer.ViewportY;

            for (var row = 0; row < _terminal.Rows; row++)
            {
                var bufferRow = top + row;
                if (bufferRow < 0 || bufferRow >= lines.Length)
                    continue;

                if (lines[bufferRow] is not { } line || !line.HasMarks)
                    continue;

                // ONE bar for the row, decided by all of its marks together, rather than one fill
                // per mark into the same rectangle. A shell's prompt string carries OSC 133;D;<code>
                // for the command that just finished immediately before the OSC 133;A that opens the
                // next prompt, so both land on the same line -- and filling per mark painted the exit
                // status and then covered it with the prompt colour, which made success and failure
                // unreachable for any host that set GutterPromptBrush.
                //
                // The status wins the lane, because how a command ended is the one thing here the user
                // cannot read off the screen; where a prompt began is visible in the prompt itself.
                int? exitCode = null;
                bool anyMark = false;

                foreach (var mark in line.Marks)
                {
                    if (mark.Kind != XT.Common.ShellIntegrationMark.PromptStart
                        && mark.Kind != XT.Common.ShellIntegrationMark.CommandFinished)
                        continue;

                    anyMark = true;
                    if (mark.Kind == XT.Common.ShellIntegrationMark.CommandFinished
                        && mark.ExitCode is int code)
                        exitCode ??= code;
                }

                if (!anyMark)
                    continue;

                var brush = exitCode switch
                {
                    0 => GutterSuccessBrush,
                    int => GutterFailureBrush,
                    _ => null,
                };

                // A finish with no status to report is a prompt bar, as it was before; so is a finish
                // whose case the host left unstyled, which keeps a host that styled only the prompt
                // showing its bar on every prompt row rather than losing the ones a command ended on.
                brush ??= GutterPromptBrush;

                if (brush is null)
                    continue;

                // SNAPPED, from the same arithmetic every text row uses. Raw row * _charHeight is a
                // fractional pixel whenever the cell height is, and the rows themselves are snapped
                // to the device grid -- so the bars drifted against the text they annotate, growing
                // to nearly a pixel out by the bottom of the screen and landing between two rows.
                var barTop = Snap(row * _charHeight, scale);
                var barBottom = Snap((row + 1) * _charHeight, scale);

                context.FillRectangle(brush,
                    new Rect(0, barTop, gutter, Math.Max(0, barBottom - barTop)));
            }
        }

        /// <summary>
        /// Narrows a column span to the columns that currently exist, answering false when nothing
        /// of it is left.
        /// </summary>
        /// <remarks>
        /// Spans outlive the grid they were measured against. A search hit is recorded at the width
        /// the line had when it was searched, and a resize narrower than that leaves it naming
        /// columns that are gone -- painted, in the old geometry, past the right edge of the control
        /// and over whatever the host had beside it.
        /// </remarks>
        internal static bool ClampSpanToGrid(int start, int end, int cols, out int clampedStart, out int clampedEnd)
        {
            clampedStart = Math.Clamp(start, 0, cols);
            clampedEnd = Math.Clamp(end, clampedStart, cols);
            return clampedEnd > clampedStart;
        }

        /// <summary>
        /// How much of something starting at <paramref name="x"/> fits before <paramref name="right"/>.
        /// </summary>
        /// <remarks>
        /// For draws whose width is not decided by the grid. An IME composition is as long as the
        /// user makes it -- a whole phrase before it commits -- and drawing it at its measured width
        /// from the cursor ran it off the end of the control.
        /// </remarks>
        internal static double FitWidth(double x, double measured, double right)
            => Math.Min(measured, Math.Max(0, right - x));

        public override void Render(DrawingContext context)
        {
            _sizedBlockDraws.Clear();
            // The terminal's own background, painted once for the whole surface.
            //
            // Nothing else paints it. TerminalView is a plain Control, so Avalonia has no Background of its
            // own to draw, and the control template is a bare Grid with no Border in it. The only thing that
            // ever filled the surface was the per-cell fill — which no longer runs for a cell using the
            // default background, so Background became a property that was read and then thrown away, and
            // setting it did nothing at all.
            //
            // Painting it here rather than per cell keeps what that change was after: a host layering the
            // terminal over its own surface sets a Background with alpha and still sees through.
            //
            // ONE snapshot for the whole frame. Every colour on screen resolves against it, so the frame is
            // painted from a set of colours that belong to each other even if a program changes the palette
            // while it is being drawn.
            _palette = _terminal.Colors.Take();

            // Snapshotted with it, and for the same reason: one answer for the whole frame. It is an
            // ordinary settable option, so a program or a host can move it between frames, and half a
            // screen drawn under each rule would be worse than either.
            _boldIsBright = _terminal.Options.DrawBoldTextInBrightColors;

            // Same discipline for the contrast floor: one ratio for the whole frame. The snapshot
            // also owns the (fg, bg) -> adjusted cache, cleared when the ratio moves.
            _minimumContrast.SnapshotRatio(_terminal.Options.MinimumContrastRatio);

            var surface = GetValue(BackgroundProperty);
            // Through the shared test, which also asks about IBrush.Opacity -- a second way to be
            // translucent that this checked alpha alone for, and missed.
            if (BufferCellExtensions.IsFullyOpaque(surface))
            {
                // The terminal's default background is the emulator's, not this brush — they agree until a
                // program moves it with OSC 11, and then the program is the one that should win. A brush
                // carrying alpha is left alone: that is a host asking to be seen through, which no RGB
                // palette entry can express.
                //
                // DECSCNM is a property of the DISPLAY, not of the cells that happen to hold text, so
                // the surface inverts with them. Without this the mode reached only written cells and
                // an inverted screen kept a band of page colour across every row a program had not
                // reached -- the more visible half of the screen, on a screen that is mostly empty.
                surface = new SolidColorBrush(BufferCellExtensions.FromRgb(
                    _terminal.ReverseVideo ? _palette.Foreground : _palette.Background));
            }

            if (surface is not null)
                context.FillRectangle(surface, new Rect(Bounds.Size));

            var scale = RenderScale;

            // The gutter, and the shift that keeps the grid out of it.
            //
            // One transform rather than an offset threaded through every column-to-pixel sum in this
            // method. There are sixteen of those and they would each have to be found and changed;
            // a translation catches all of them at once and cannot be half-applied. The pointer maths
            // takes the offset off the other end -- see PointerColumn.
            var gutter = Math.Max(0, GutterWidth);
            DrawGutter(context, gutter, scale);

            using var gutterShift = gutter > 0
                ? context.PushTransform(Matrix.CreateTranslation(gutter, 0))
                : default;

            //Debug.WriteLine("======");
            //Debug.WriteLine(_terminal.Buffer.PrintViewport());

            // Use the terminal buffer's ViewportY to determine what to render
            int viewportY = _terminal.Buffer.ViewportY;
            int viewportLines = _terminal.Rows;
            int startLine = viewportY;
            int endLine = Math.Min(_terminal.Buffer.Length, startLine + viewportLines);

            // The frame this render draws from, when one is usable: complete, captured at a frame
            // boundary, still describing this viewport. Null sends every row to the live buffer,
            // which is exactly the path that existed before captures did. Pinned for as long as the
            // NEXT render might replay runs built from it, which the pool accounts for.
            var capturedFrame = _frameCapture.PinForRender(
                startLine, _terminal.Cols, viewportLines,
                Interlocked.Read(ref _liveWriteGeneration), _atomicUpdate, _bufferWriteInProgress);

            // The direct renderer draws the cell grid onto the Skia canvas instead of recording a fill
            // and a text draw per run. Everything after it — cursor, selection, the hovered link —
            // still goes through DrawingContext and lands on top, because Custom() enqueues into the
            // same list.
            //
            // The snapshot is taken HERE, on the UI thread. The operation runs during compositing, on
            // another thread, while the pty read loop may be writing to the buffer; it must never
            // touch the buffer or the palette itself.
            // Null unless the direct path both applies and can run; the row loop below consults it
            // to draw exactly the rows the snapshot declined.
            Skia.TerminalSnapshot? skiaSnapshot = null;

            // A custom draw operation only draws where Avalonia is on its Skia backend, and there
            // is no way to ask before enqueuing one -- so the layer reports afterwards and this
            // reads the report BEFORE deciding, on the frame after the one that failed. Asking
            // inside the else of the decision (as this first did) never runs: on any frame where
            // the direct path applies, the if branch is taken and the report is never read, so a
            // non-Skia backend stayed silently blank forever instead of falling back once.
            if (_lastSkiaLayer is { Unsupported: true })
            {
                _skiaUnsupported = true;
                _lastSkiaLayer = null;
            }

            // INSIDE a try of its own: this reads the live buffer without the lock, exactly as the
            // classic loop does, and the classic loop's own catch is what keeps a concurrent write
            // from turning a race into an unhandled exception out of Render. Building outside that
            // protection gave the two paths different failure modes for the same race.
            try
            {
            if (UseSkiaRenderer && !_skiaUnsupported && _charWidth > 0 && _charHeight > 0)
            {
                var snapshot = _snapshotBuilder.Build(
                    _terminal, _palette, startLine, viewportLines, _terminal.Cols,
                    _charWidth, _charHeight, FontSize, _fontFamilyChain,
                    GetValue(ForegroundProperty), surface, RequestPaint, Ligatures,
                    _terminal.ReverseVideo, _cursorBlinkOn, _boldIsBright, _minimumContrast,
                    capturedFrame);

                snapshot.RenderScale = scale;

                var layer = new Skia.TerminalSkiaLayer(snapshot, _skiaFonts,
                    new Rect(0, 0, _terminal.Cols * _charWidth, viewportLines * _charHeight),
                    _snapshotBuilder, RequestPaint);
                context.Custom(layer);

                skiaSnapshot = snapshot;
                _lastSkiaLayer = layer;
            }
            }
            catch (Exception ex)
            {
                // A write landed mid-read. Draw this frame classically rather than losing it, and
                // let the write that interrupted us ask for the next one.
                Debug.WriteLine($"[TerminalView] Skia snapshot skipped: {ex.Message}");
                skiaSnapshot = null;
            }

            try
            {
                // A block anchored ABOVE the viewport still hangs into it. The row pass below starts
                // at viewportY, so it never visits such a block's own line and _sizedBlockDraws would
                // never hear about it -- and the rows it covers are deliberately blank in the buffer,
                // SkipCellsCoveredFromAbove having steered text around them, so nothing else paints
                // there either. Scrolling one line through any output holding an s=2 heading would
                // blank the heading rather than clip it.
                //
                // At most MaxScale - 1 rows to walk, and only when the buffer has ever held a tall
                // block. The draw's StartYPos goes NEGATIVE, which is what puts the box back where it
                // belongs, and the PushClip in RenderSizedBlocks trims what falls above the top.
                if (_terminal.Buffer.HasMultiRowSizedRuns)
                {
                    for (int above = 1; above < XT.Common.TextSizing.MaxScale; above++)
                    {
                        int anchorRow = viewportY - above;
                        if (anchorRow < 0)
                            break;

                        var anchorLine = anchorRow < _terminal.Buffer.Length
                            ? _terminal.Buffer.GetLine(anchorRow) : null;
                        if (anchorLine is null || !anchorLine.HasSizedRuns)
                            continue;

                        var hangStart = Snap(-above * _charHeight, scale);
                        var hangEnd = Snap((-above + 1) * _charHeight, scale);

                        foreach (var run in anchorLine.SizedRuns)
                        {
                            // Rows > above is the test TryGetSizedRunCovering applies: a run reaches
                            // this row only if it is taller than the distance up to its anchor.
                            if (run.Rows > above)
                                _sizedBlockDraws.Add(new SizedBlockDraw(
                                    anchorLine, run, hangStart, Math.Max(0, hangEnd - hangStart)));
                        }
                    }
                }

                for (int y = startLine; y < endLine; y++)
                {
                    // With the direct path running, this loop draws only what the snapshot declined:
                    // a doubled row, or one carrying OSC 66 sized runs. Both need what the snapshot
                    // has no field for, and drawing them wrong is worse than not drawing them fast.
                    if (skiaSnapshot is not null && !skiaSnapshot.IsDeferred(y - startLine))
                        continue;

                    // The buffer can SHRINK underneath a render. CSI 3 J — what cmd.exe's `cls` sends —
                    // discards the entire scrollback, and it arrives on the PTY thread, so the bounds
                    // captured above can point past the end by the time we reach this line.
                    //
                    // This could not happen before: the buffer only ever grew, or dropped a single line at
                    // a time once it hit capacity, so a stale index stayed valid. A wholesale discard can
                    // remove hundreds at once. Without this check GetLine throws IndexOutOfRangeException,
                    // the catch below swallows it, and the REST OF THE FRAME is lost — plus anyone running
                    // under a debugger gets a first-chance break every time they clear the screen.
                    //
                    // Breaking out costs at most one dropped frame: the write that trimmed the buffer
                    // requests another render, and that one sees consistent bounds.
                    if (y >= _terminal.Buffer.Length)
                        break;

                    // The captured row when there is one; the live line for the rows a capture
                    // cannot represent (pictures, sized runs, doubled lines) and whenever no
                    // capture is usable at all.
                    var line = capturedFrame?.LineAt(y) ?? _terminal.Buffer.GetLine(y);
                    if (line == null)
                        continue;

                    int screenY = y - startLine;

                    // Calculate Y positions for this screen row
                    var startYPos = Snap(screenY * _charHeight, scale);
                    var endYPos = Snap((screenY + 1) * _charHeight, scale);
                    var rowHeight = Math.Max(0, endYPos - startYPos);

                    // Check for double-width/double-height line attributes
                    var lineAttr = line.LineAttribute;
                    if (lineAttr == LineAttribute.DoubleWidth ||
                             lineAttr == LineAttribute.DoubleHeightTop ||
                             lineAttr == LineAttribute.DoubleHeightBottom)
                    {
                        RenderDoubleWidthLine(context, line, screenY, startYPos, rowHeight, lineAttr, scale);
                    }
                    else
                    {
                        RenderNormalLine(context, line, screenY, startYPos, rowHeight, scale);
                    }
                }

                // The DEC status line, drawn after the grid and before the overlays.
                //
                // Through RenderNormalLine like any other row, which is the point: vttest writes
                // graphic renditions into the status line, so it is not a text strip with a colour.
                // Sending it down the same path means bold, inverse, colours and underlines work
                // there because they already work everywhere else.
                //
                // It sits BELOW the grid, at the height the grid was already shortened by -- see
                // StatusLineHeight, taken off in ArrangeOverride before the rows were counted. No
                // clip: it occupies space nothing else was given.
                if (_statusLine is { } statusLine && _charHeight > 0)
                {
                    var statusTop = Snap(_terminal.Rows * _charHeight, scale);
                    var statusBottom = Snap((_terminal.Rows + 1) * _charHeight, scale);

                    RenderNormalLine(context, statusLine, _terminal.Rows, statusTop,
                                     Math.Max(0, statusBottom - statusTop), scale);
                }

                // OSC 66 blocks, after every row's background and text and before the overlays:
                // selection and the cursor still draw over scaled text, as they do over plain text.
                RenderSizedBlocks(context, scale);

                // Search highlights under the selection, so a selected match still reads as selected.
                RenderSearchHighlights(context, viewportY, scale);

                // Render URL underline when hovering
                RenderHoveredUrl(context, viewportY, scale);

                // Render selection overlay
                RenderSelection(context, viewportY, scale);

                RenderCursor(context, viewportY, scale);

                // Render IME preedit (composition) text overlay
                RenderPreeditText(context, viewportY, scale);
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"[TerminalView] Render error: {ex.Message}");
            }
        }

        /// <summary>
        /// Renders a normal (single-width, single-height) line.
        /// </summary>
        private void RenderNormalLine(DrawingContext context, BufferLine line, int screenY, double startYPos, double rowHeight, double scale)
        {
            // Try to use cached text runs for this line (but not when ReverseVideo mode is active as it affects all cells)
            var textRuns = !_terminal.ReverseVideo ? line.Cache as List<CachedTextRun> : null;

            textRuns ??= CollectLineRuns(line, startYPos, rowHeight);

            DrawLineRuns(context, textRuns, startYPos, rowHeight, scale);
        }

        /// <summary>
        /// Paints a row from its runs -- the same list whether it was cached or collected a moment ago.
        /// </summary>
        /// <remarks>
        /// One draw path rather than two. Collecting used to paint as it went, so every change had to be
        /// made in both places and the two drifted: styled underlines were wired into the replay and
        /// missing from a freshly built row until something else invalidated it. Collecting now only
        /// READS, which is also what lets it be retried -- see <see cref="CollectLineRuns"/>.
        /// </remarks>
        private void DrawLineRuns(DrawingContext context, List<CachedTextRun> textRuns,
                                  double startYPos, double rowHeight, double scale)
        {
            foreach (var run in textRuns)
            {
                // Recalculate position based on current screen row
                var startX = Snap(run.StartX * _charWidth, scale);
                var endX = Snap((run.StartX + run.CellCount) * _charWidth, scale);
                var rect = new Rect(startX, startYPos, Math.Max(0, endX - startX), rowHeight);
                var position = new Point(startX, startYPos);

                // The background goes down first either way: a Sixel drawn with background select 1 leaves
                // its unset pixels transparent, and the cell's own background is meant to show through them.
                if (run.Background is not null)
                    context.FillRectangle(run.Background, rect);

                if (run.IsImage)
                    DrawImageRun(context, run, startYPos, rowHeight, scale);
                else if (run.Glyphs is not null)
                    DrawGlyphs(context, run, position);
                else if (run.Text is not null)
                    context.DrawText(run.Text, position);

                if (run.UnderlineStyle != XT.Common.UnderlineStyle.None)
                    DrawUnderline(context, run, position, rect.Width, rowHeight);
            }
        }

        /// <summary>
        /// Reads a row's cells into runs, and publishes them as the line's cache only if the line held
        /// still while they were read.
        /// </summary>
        /// <remarks>
        /// <para>The pty reader thread writes into the buffer while this runs on the UI thread. It holds
        /// <c>_terminalLock</c> to do it and this does not take it, so a row can be REWRITTEN mid-read and
        /// the runs then describe a row that never existed -- part of it as it was, the rest as it became.
        /// Taking the lock here would be safe now that the reader no longer waits on the UI thread while
        /// holding it, but the reader would then be stopped for the length of every frame, which is a
        /// third of the clock at 30 FPS and is paid on every frame rather than on the rare torn one.</para>
        /// <para>A sprite moving LEFT is where that shows, because ncurses moves one with DCH: a delete
        /// that shifts the whole rest of the line at once. Read across that shift, the row comes out with
        /// fragments of the sprite smeared along it rather than one blurred cell -- the trail of leftover
        /// glyphs asciiquarium leaves behind.</para>
        /// <para>Worse than the frame it happened on: the mixture was then stored as the line's cache, and
        /// a cache is dropped only by the next WRITE to that line. A sprite that has moved away leaves a
        /// row nothing writes to again, so the smear stayed on screen until something else touched it.</para>
        /// <para>Every write to a line clears its <c>Cache</c>, which makes that field a read stamp as well
        /// as a cache: park a token in it, read the row, and a token still there means no write landed.
        /// Retried a couple of times, because a re-read costs only the read. When it will not settle the
        /// row is still drawn from what was read -- one frame of tearing is what any terminal does -- but
        /// it is NOT cached, and another frame is asked for.</para>
        /// </remarks>
        private List<CachedTextRun> CollectLineRuns(BufferLine line, double startYPos, double rowHeight)
        {
            // Three reads of one row, on the rare frame a write lands in the middle of one. Unbounded
            // retries would let a row being written continuously stall the whole frame.
            const int Attempts = 3;

            var deferredBefore = _sizedBlockDraws.Count;

            for (var attempt = 1; ; attempt++)
            {
                // Whatever an abandoned read deferred came from the row it misread, so it goes with it.
                if (_sizedBlockDraws.Count > deferredBefore)
                    _sizedBlockDraws.RemoveRange(deferredBefore, _sizedBlockDraws.Count - deferredBefore);

                var stamp = new object();
                line.Cache = stamp;

                var runs = BuildLineRuns(line, startYPos, rowHeight, out var hasSizedRuns);

                if (!ReferenceEquals(line.Cache, stamp))
                {
                    if (attempt < Attempts)
                        continue;

                    line.Cache = null;
                    RequestPaint();
                    return runs;
                }

                // Sized lines are not cached: the cache stores finished draw calls and the blocks are
                // deliberately not among them -- they are painted in the deferred pass after every row.
                line.Cache = hasSizedRuns || _terminal.ReverseVideo ? null : runs;
                return runs;
            }
        }

        /// <summary>
        /// A line's picture runs, ordered back to front.
        /// </summary>
        /// <remarks>
        /// <para>Z-index first, then age, age being the order the emulator added the runs to the
        /// line. <c>OrderBy</c> is stable, so sorting on z alone leaves equal depths in the order
        /// they arrived — which is Kitty's rule that the placement made later is drawn on top.</para>
        /// <para>Nothing is collected or coalesced: a picture is already one run per line, so the
        /// emulator's storage IS the draw list and each run is a single blit. The list is copied
        /// only because it has to be sorted, and only on a line that has a picture on it.</para>
        /// </remarks>
        private static List<XT.Graphics.LinePlacement> OrderedPlacements(BufferLine line)
        {
            if (!line.HasImages)
                return EmptyPlacements;

            var placements = line.Placements;
            if (placements.Count == 1)
                return new List<XT.Graphics.LinePlacement>(placements);

            return placements.OrderBy(p => p.ZIndex).ToList();
        }

        /// <summary>
        /// The image a run shows, found among the ones its line holds.
        /// </summary>
        /// <remarks>
        /// A run names its picture by id rather than holding it, because the line owns the pixels and
        /// its death is what releases them. A line holds one or two images, so this is a scan of a
        /// list that is almost always length one.
        /// </remarks>
        private static XT.Graphics.TerminalImage? ImageFor(BufferLine line, XT.Graphics.LinePlacement placement)
        {
            foreach (var image in line.Images)
            {
                if (image.Id == placement.ImageId)
                    return image;
            }

            return null;
        }

        /// <summary>
        /// Adds one picture run to the row's runs.
        /// </summary>
        /// <remarks>
        /// One blit per run, which is one per row of a picture. There is no coalescing to do and no
        /// tile arithmetic left: the run already carries the source rectangle and the columns it
        /// covers, so the whole strip goes down in a single call.
        /// </remarks>
        private void AppendImageRun(BufferLine line,
                                    XT.Graphics.LinePlacement placement,
                                    List<CachedTextRun> textRuns,
                                    List<XT.Graphics.LinePlacement> alreadyPainted)
        {
            var image = ImageFor(line, placement);
            if (image is null)
                return;

            // Cols is the picture's NATURAL width and is deliberately not clipped by the emulator, so
            // the clipping happens here: a narrow window shows less of the picture and a wider one
            // shows more, without anything having been destroyed in between.
            var start = Math.Max(0, placement.Column);
            var end = Math.Min(placement.EndColumn, Math.Min(line.Length, _terminal.Cols));
            var cellCount = end - start;
            if (cellCount <= 0)
                return;

            // The cell's own background goes under the picture, which is what a Sixel drawn with
            // background select 1 needs: its unset pixels are transparent and the cell colour is
            // meant to show through them.
            //
            // Only where nothing has painted it already. Runs are drawn back to front, so a nearer
            // picture repainting the background would erase the one behind it rather than blend over
            // it -- which is the whole of what overlapping placements are for.
            var first = line[start];
            var background = first.GetBackgroundBrush(_palette, this.Background);
            var fill = first.GetBackgroundColor(_palette).HasValue
                       && !OverlapsAny(alreadyPainted, start, end)
                       ? background
                       : null;

            textRuns.Add(new CachedTextRun(null, start, cellCount, fill, placement, image));
        }

        /// <summary>
        /// Draws a run's underline in whatever style it asked for.
        /// </summary>
        /// <remarks>
        /// <para>By hand rather than through Avalonia's TextDecorations, which have no curly form
        /// and no way to give the line SGR 58's colour of its own.</para>
        /// <para>Width and height arrive ALREADY SNAPPED, from the same rect every other draw in
        /// this file paints with -- so an underline's edges land exactly where its neighbours' do.
        /// Re-deriving the width from a raw cell width here put an antialiased seam at every
        /// attribute change inside an underlined span.</para>
        /// <para>The curly geometry and the pens are built once per cached run and replayed with
        /// it; only the rectangles are re-issued per frame, and those allocate nothing. The
        /// geometry is kept relative to the run's origin and translated into place, because the
        /// run's row changes as the screen scrolls while the shape does not.</para>
        /// </remarks>
        private static void DrawUnderline(DrawingContext context, CachedTextRun run, Point position,
                                          double width, double cellHeight)
        {
            var brush = run.UnderlineBrush;
            if (brush is null || width <= 0)
                return;

            var thickness = Math.Max(1.0, cellHeight / 14.0);
            var x = position.X;
            var baseY = position.Y + cellHeight - thickness * 2;

            switch (run.UnderlineStyle)
            {
                case XT.Common.UnderlineStyle.Double:
                    // The pair straddles where a single line would sit; a second line below would
                    // fall out of the cell.
                    context.FillRectangle(brush, new Rect(x, baseY - thickness, width, thickness));
                    context.FillRectangle(brush, new Rect(x, baseY + thickness, width, thickness));
                    break;

                case XT.Common.UnderlineStyle.Curly:
                {
                    // Centred ON baseY, amplitude chosen so a lobe plus half the pen's width ends
                    // exactly at the cell's bottom edge. The first version centred the wave lower
                    // and its lobes fell ~1.5 thicknesses out of the row -- chopped flat when the
                    // row below had its own background fill, bleeding into its glyphs when it did
                    // not: the same escape sequence rendered differently depending on the line
                    // under it.
                    var amplitude = thickness * 1.5;
                    var cellWidth = run.CellCount > 0 ? width / run.CellCount : width;
                    var period = Math.Max(4.0, cellWidth / 2.0);

                    var geometry = run.UnderlineGeometry;
                    if (geometry is null)
                    {
                        // One quadratic bezier per half-period lobe instead of eight line segments
                        // per period: smoother, and a quarter of the verbs. The sine's phase keeps
                        // ABSOLUTE x in its argument so two adjacent runs continue one wave
                        // instead of each restarting their own.
                        double Wave(double dx) => amplitude * Math.Sin((x + dx) / period * Math.PI * 2.0);

                        var half = period / 2.0;
                        var g = new StreamGeometry();
                        using (var ctx = g.Open())
                        {
                            ctx.BeginFigure(new Point(0, Wave(0)), false);

                            // First boundary of a whole lobe at or after the run's left edge.
                            var firstEdge = (Math.Floor(x / half) + 1) * half - x;
                            if (firstEdge > 0 && firstEdge < width)
                                ctx.QuadraticBezierTo(
                                    new Point(firstEdge / 2.0, Wave(0) + (Wave(firstEdge) - Wave(0)) / 2.0
                                              + LobeSign(x, half) * amplitude / 2.0),
                                    new Point(firstEdge, Wave(firstEdge)));

                            var dx = Math.Max(0.0, firstEdge);
                            while (dx + half <= width)
                            {
                                // A full lobe: endpoints on the axis, control at twice the peak.
                                ctx.QuadraticBezierTo(
                                    new Point(dx + half / 2.0, LobeSign(x + dx, half) * amplitude * 2.0),
                                    new Point(dx + half, 0));
                                dx += half;
                            }

                            if (dx < width)
                                ctx.QuadraticBezierTo(
                                    new Point(dx + (width - dx) / 2.0,
                                              LobeSign(x + dx, half) * amplitude / 2.0 + Wave(width) / 2.0),
                                    new Point(width, Wave(width)));

                            ctx.EndFigure(false);
                        }
                        geometry = g;
                        run.UnderlineGeometry = geometry;
                    }

                    var pen = run.UnderlinePen ??= new ImmutablePen(brush.ToImmutable(), thickness);
                    using (context.PushTransform(Matrix.CreateTranslation(x, baseY)))
                        context.DrawGeometry(null, pen, geometry);
                    break;
                }

                case XT.Common.UnderlineStyle.Dotted:
                case XT.Common.UnderlineStyle.Dashed:
                {
                    // What Pen.DashStyle is for: one line and the renderer draws the marks, in
                    // place of a FillRectangle per dot. Dash lengths are in pen-thickness units;
                    // the offset carries the phase-lock, so a run does not restart the pattern
                    // and stamp a mark at every attribute boundary.
                    if (run.UnderlinePen is not { } dashPen)
                    {
                        var pattern = run.UnderlineStyle == XT.Common.UnderlineStyle.Dotted
                            ? new[] { 1.0, 1.0 }
                            : new[] { 3.0, 2.0 };
                        var periodPx = (pattern[0] + pattern[1]) * thickness;
                        var offset = (x % periodPx) / thickness;
                        dashPen = new ImmutablePen(
                            brush.ToImmutable(), thickness,
                            new ImmutableDashStyle(pattern, offset));
                        run.UnderlinePen = dashPen;
                    }

                    var midY = baseY + thickness / 2.0;
                    context.DrawLine(dashPen, new Point(x, midY), new Point(x + width, midY));
                    break;
                }

                default:
                    context.FillRectangle(brush, new Rect(x, baseY, width, thickness));
                    break;
            }
        }

        /// <summary>Which way the sine lobe starting at this absolute position points.</summary>
        private static double LobeSign(double absoluteX, double halfPeriod)
            => Math.Floor(absoluteX / halfPeriod) % 2 == 0 ? 1.0 : -1.0;

        /// <summary>
        /// Blits one strip of a picture into the cells it belongs to.
        /// </summary>
        /// <remarks>
        /// The destination is derived from the cell grid rather than from the image's own pixel size, so a
        /// picture stays locked to the text it was placed among even after a font or DPI change has moved the
        /// grid out from under it. Tiles on the right and bottom edges cover only part of a cell, so the
        /// destination is scaled by how much of one the source actually holds -- stretching a half-tile over a
        /// whole cell is the difference between a picture and a smeared one.
        /// </remarks>
        private void DrawImageRun(DrawingContext context, CachedTextRun run,
                                  double startYPos, double rowHeight, double scale)
        {

            if (_imageRenderingUnavailable)
                return;

            if (!TryPlanImageBlit(run, startYPos, rowHeight, _charWidth, _charHeight, scale,
                                  out _, out var destination, out var unifiedDest))
                return;

            var bitmap = GetOrCreateBitmap(run.Image!);
            if (bitmap is null)
                return;

            try
            {
                // The whole picture's mapping, clipped to this row -- see TryPlanImageBlit. Nine
                // rows drawn this way sample identically to one draw, which is what keeps a
                // fractional display scale from putting a hairline at every strip boundary.
                using (context.PushClip(destination))
                    context.DrawImage(bitmap, new Rect(0, 0, run.Image!.PixelWidth, run.Image.PixelHeight), unifiedDest);
            }
            catch (Exception ex) when (IndicatesNoRasterBackend(ex))
            {
                // The backend cannot draw a bitmap at all -- Consolonia runs this same control over text
                // cells, and the headless platform's recording context is the same. That will not change
                // on the next frame, so stop trying rather than throwing out of Render thirty times a
                // second, and let the text carry on drawing.
                _imageRenderingUnavailable = true;
                Debug.WriteLine($"[TerminalView] image rendering unavailable: {ex.Message}");
            }
            catch (Exception ex)
            {
                // Anything else is about THIS picture rather than the platform: a bitmap that will not
                // blit, a frame that ran out of memory. Remember the failure against the image so only
                // that one is skipped. Latching here instead would let a single bad picture turn every
                // picture off for the life of the control, and hide whatever caused it.
                if (_imageBitmaps.TryGetValue(run.Image!, out var cached))
                {
                    try { cached.Bitmap?.Dispose(); } catch { /* already gone; nothing to salvage */ }
                    cached.Bitmap = null;
                }

                Debug.WriteLine($"[TerminalView] could not draw image {run.Image!.Id}: {ex.Message}");
            }
        }

        /// <summary>
        /// Whether an exception from <c>DrawImage</c> means the platform has no raster surface at all,
        /// as opposed to something being wrong with one picture.
        /// </summary>
        /// <remarks>
        /// The distinction decides whether images are abandoned for the life of the control or only for
        /// the image that failed, so it is kept as a named predicate rather than an inline type test --
        /// it is a policy, and it is worth being able to assert on it directly.
        /// </remarks>
        internal static bool IndicatesNoRasterBackend(Exception exception)
            => exception is NotImplementedException or PlatformNotSupportedException or NotSupportedException;

        /// <summary>
        /// Whether any run drawn earlier on this line covers part of this one's span.
        /// </summary>
        /// <remarks>
        /// <para>What decides whether a run paints the cell background under itself. Runs go down
        /// back to front, so a nearer picture repainting the background would erase the one behind
        /// it rather than blend over it — which is the whole of what overlapping placements buy.
        /// </para>
        /// <para>The whole span rather than the columns actually uncovered, because the run's fill
        /// is what its CACHED form replays: a rectangle over the run. A partial overlap therefore
        /// costs the upper run's spare columns their background, which errs toward leaving a picture
        /// alone rather than painting over one.</para>
        /// </remarks>
        /// <summary>
        /// Whether a Sixel covers this column, and so has replaced whatever text was under it.
        /// </summary>
        /// <remarks>
        /// <para>The one place the two protocols have to be told apart. A Kitty placement is an
        /// OVERLAY: the cell keeps its character, both are drawn, and the z-index decides which one
        /// is seen. A Sixel is CONTENT: it replaced what was there, which is why the emulator splits
        /// a Sixel run when something prints over it and leaves a Kitty run alone.</para>
        /// <para>The emulator does not clear the cells a Sixel covers -- placing one only adds a run
        /// -- so they keep whatever was on screen beforehand. Drawing them puts that text under the
        /// picture: invisible beneath an opaque one, and showing through a Sixel drawn with
        /// background select 1, whose unset pixels are transparent so that the cell's own colour
        /// comes through. The cell's colour, not the previous screen's text.</para>
        /// </remarks>
        private static bool CoveredBySixel(BufferLine line, int column)
        {
            if (!line.HasImages)
                return false;

            foreach (var placement in line.Placements)
            {
                if (placement.Kind == XT.Graphics.PlacementKind.Sixel && placement.Covers(column))
                    return true;
            }

            return false;
        }

        /// <summary>
        /// Whether a picture has already been drawn UNDER the columns <paramref name="start"/> to
        /// <paramref name="end"/>, so painting a background there would erase it.
        /// </summary>
        /// <remarks>
        /// Only the negative-z placements reach this list at the point it is asked, because the row
        /// pass draws those before the text and the rest after it. That is the whole distinction: a
        /// picture in front of the text is allowed to cover a background, a picture behind it is what
        /// the background was covering.
        /// </remarks>
        private static bool CoveredByBackdrop(List<XT.Graphics.LinePlacement> painted, int start, int end)
            => OverlapsAny(painted, start, end);

        /// <summary>
        /// The line's negative-z placements — the pictures its text sits ON TOP of. The row pass
        /// accumulates this list as it paints; the deferred sized-block pass runs after every row
        /// and has no such running state, so it derives the same set from the line directly.
        /// OrderedPlacements sorts by z, which is why the walk can stop at the first non-negative.
        /// </summary>
        private static List<XT.Graphics.LinePlacement> BackdropPlacements(BufferLine line)
        {
            var ordered = OrderedPlacements(line);
            if (ordered.Count == 0 || ordered[0].ZIndex >= 0)
                return EmptyPlacements;

            var backdrops = new List<XT.Graphics.LinePlacement>();
            foreach (var placement in ordered)
            {
                if (placement.ZIndex >= 0)
                    break;
                backdrops.Add(placement);
            }

            return backdrops;
        }

        private static bool OverlapsAny(List<XT.Graphics.LinePlacement> earlier, int start, int end)
        {
            foreach (var placement in earlier)
            {
                if (placement.Column < end && placement.EndColumn > start)
                    return true;
            }

            return false;
        }

        /// <summary>
        /// Works out which pixels of a picture a run shows and where on screen they go.
        /// </summary>
        /// <remarks>
        /// <para>Separated from the drawing so the arithmetic can be asserted directly. It is the part with
        /// something to get wrong, and it cannot be observed through a rendered frame: the headless platform's
        /// recording context throws from DrawImage.</para>
        /// <para>The destination comes off the cell grid rather than the picture's own pixel size, so an
        /// image stays locked to the text it was placed among after a font or DPI change has moved the
        /// grid.</para>
        /// <para>A run's <c>Cols</c> is its natural width and the caller has already clipped the columns to
        /// what the line can show, so the SOURCE has to be narrowed by the same proportion — otherwise a
        /// narrow window would squeeze the whole picture into fewer cells instead of showing less of it.</para>
        /// </remarks>
        internal static bool TryPlanImageBlit(CachedTextRun run, double startYPos, double rowHeight,
                                              double charWidth, double charHeight, double scale,
                                              out Rect source, out Rect destination)
            => TryPlanImageBlit(run, startYPos, rowHeight, charWidth, charHeight, scale,
                                out source, out destination, out _);

        /// <summary>
        /// Plans one row's blit: the strip of the picture it shows (<paramref name="source"/>,
        /// <paramref name="destination"/>) and the ONE mapping of the whole picture that every row
        /// of the placement shares (<paramref name="unifiedDest"/>).
        /// </summary>
        /// <remarks>
        /// The unified mapping is why fractional display scales stopped showing hairlines. Each row
        /// is its own DrawImage, and a sampler resamples each call independently, clamping at the
        /// source strip's edges instead of reading the neighbouring row's pixels -- so nine strips
        /// are not pixel-identical to one picture except at integer scales, which is why macOS at
        /// 2.0 looked perfect while Windows at 1.25 showed seams. Drawing every row as the WHOLE
        /// picture's mapping clipped to the row makes the nine draws mathematically one draw.
        /// The mapping is deliberately NOT snapped: it is a transform, not an edge, and snapping it
        /// per row would hand each row a slightly different transform -- the disease again. The
        /// CLIP (<paramref name="destination"/>) is what lands on device pixels.
        /// </remarks>
        internal static bool TryPlanImageBlit(CachedTextRun run, double startYPos, double rowHeight,
                                              double charWidth, double charHeight, double scale,
                                              out Rect source, out Rect destination, out Rect unifiedDest)
        {
            source = default;
            destination = default;
            unifiedDest = default;

            if (run.Placement is not { } placement || run.Image is null)
                return false;
            if (run.CellCount <= 0 || charWidth <= 0 || charHeight <= 0)
                return false;
            if (placement.Cols <= 0 || placement.SrcWidth <= 0 || placement.SrcHeight <= 0)
                return false;

            // How much of the run's natural width is actually being drawn, and the slice of the
            // source that corresponds to it.
            var shown = Math.Min(run.CellCount, placement.Cols);
            var sourceWidth = (double)placement.SrcWidth * shown / placement.Cols;
            if (sourceWidth <= 0)
                return false;

            // The offsets shift the picture inside its first cell without enlarging the box, so what
            // overflows the last cell is clipped. They are in image pixels, and the cell they shift
            // within is a screen cell, so they cross over as a fraction of one.
            var cell = run.Image.CellWidth > 0 ? run.Image.CellWidth : 1;
            var cellHigh = run.Image.CellHeight > 0 ? run.Image.CellHeight : 1;
            var offsetX = placement.OffsetX / (double)cell * charWidth;
            var offsetY = placement.OffsetY / (double)cellHigh * charHeight;

            // How many source pixels one cell of THIS placement covers. For a natural placement it
            // is the image's own cell metric -- one image pixel per screen-cell pixel, edges left
            // unstretched. For a c/r-stretched placement it is the placement's share of its box, so
            // a full row's strip fills exactly one row and a full run fills its columns: drawing
            // those at natural size was the striping in every scaled picture, and the clipping in
            // every shrunken one. Zero means an emulator from before the field existed -- natural.
            // Zero means a NATURAL placement (or an emulator from before the field existed):
            // the image's own cell metric, edges unstretched. Non-zero means stretched into a
            // c/r box -- and then the destination is taken from the ROW GEOMETRY, not converted
            // back from source pixels: the emulator slices strips to whole pixels, and a 37px
            // strip against a 37.375px/row ratio drawn by conversion comes out a fraction of a
            // pixel short of its row. Repeated every row, that is a hairline seam across every
            // scaled picture. The strip is one full row of the box by construction, so fill the
            // row and let the rounding be a sub-pixel sampling shift instead.
            var stretched = placement.PxPerCellX > 0 || placement.PxPerCellY > 0;
            double pxPerCellX = placement.PxPerCellX > 0 ? placement.PxPerCellX : cell;
            double pxPerCellY = placement.PxPerCellY > 0 ? placement.PxPerCellY : cellHigh;

            // The destination is the picture's OWN size expressed in screen pixels, not the box of
            // cells it was assigned. Those agree for every full cell and disagree at the edges, which
            // is exactly where the stretching showed.
            //
            // A picture whose width is not a whole number of cells still occupies a whole number of
            // cells in the buffer, so drawing it across all of them stretched it sideways to fill the
            // remainder. Worse vertically: the LAST row of a picture usually has fewer pixels left
            // than a cell is tall, and that short strip was being stretched over a full text row --
            // so the bottom of every picture was subtly taller than the rest of it.
            //
            // srcWidth and srcHeight are in image pixels and cell/cellHigh say how many of those make
            // one cell, which is the same conversion the offsets above already use.
            var drawnWidth = stretched ? shown * charWidth : sourceWidth / pxPerCellX * charWidth;

            // rowHeight, NOT charHeight, and that is the whole of the hairline bug on Windows.
            // The row's box is snapped to device pixels -- startYPos and startYPos + rowHeight are
            // both Snap() results -- while charHeight is the unsnapped ideal. At a fractional
            // display scale the two disagree: 13.0 at 1.25 makes rows alternate 16 and 17 device
            // pixels, so on every stretched row a strip measured in charHeight stops one pixel short
            // of the row it fills, the next row's clip starts at the row boundary, and the terminal
            // background shows through the gap. Measured: pure black 1px lines every fourth row,
            // 65 device pixels apart, on natural placements only -- the stretched branch has filled
            // rowHeight since the c/r-box fix and never showed them.
            //
            // Only the CLIP moves. mapScaleY below stays on charHeight, because that is the shared
            // transform every row of the placement draws through, and rowHeight varies row to row.
            var drawnHeight = stretched ? rowHeight : placement.SrcHeight / pxPerCellY * rowHeight;

            // Clip the shifted destination to the cell box. Cropping the source by the same
            // proportions is essential: merely shortening the destination would squeeze the full
            // source into it and recreate the edge stretching this method is meant to remove.
            var boxLeft = run.StartX * charWidth;
            var boxRight = (run.StartX + shown) * charWidth;
            var rawLeft = boxLeft + offsetX;
            var rawTop = startYPos + offsetY;
            var clippedLeft = Math.Max(boxLeft, rawLeft);
            var clippedRight = Math.Min(boxRight, rawLeft + drawnWidth);
            var clippedTop = Math.Max(startYPos, rawTop);
            var clippedBottom = Math.Min(startYPos + rowHeight, rawTop + drawnHeight);

            if (clippedRight <= clippedLeft || clippedBottom <= clippedTop)
                return false;

            var sourceX = clippedLeft == rawLeft
                ? placement.SrcX
                : placement.SrcX + (clippedLeft - rawLeft) / drawnWidth * sourceWidth;
            var sourceY = clippedTop == rawTop
                ? placement.SrcY
                : placement.SrcY + (clippedTop - rawTop) / drawnHeight * placement.SrcHeight;
            var clippedSourceWidth = clippedLeft == rawLeft && clippedRight == rawLeft + drawnWidth
                ? sourceWidth
                : (clippedRight - clippedLeft) / drawnWidth * sourceWidth;
            var clippedSourceHeight = clippedTop == rawTop && clippedBottom == rawTop + drawnHeight
                ? placement.SrcHeight
                : (clippedBottom - clippedTop) / drawnHeight * placement.SrcHeight;

            // The shared whole-picture mapping, in pure ratios. rawLeft/rawTop are where THIS
            // strip's source origin lands, so walking back by the source origin itself gives where
            // image pixel (0,0) lands -- the same expression from every row, because rawTop moves
            // by exactly one row as SrcY moves by exactly one row's worth of source.
            var mapScaleX = charWidth / pxPerCellX;
            var mapScaleY = charHeight / pxPerCellY;
            unifiedDest = new Rect(
                rawLeft - placement.SrcX * mapScaleX,
                rawTop - placement.SrcY * mapScaleY,
                run.Image.PixelWidth * mapScaleX,
                run.Image.PixelHeight * mapScaleY);

            var startX = Snap(clippedLeft, scale);
            var endX = Snap(clippedRight, scale);
            var topY = Snap(clippedTop, scale);
            var endY = Snap(clippedBottom, scale);

            destination = new Rect(startX, topY, Math.Max(0, endX - startX), Math.Max(0, endY - topY));
            if (destination.Width <= 0 || destination.Height <= 0)
            {
                destination = default;
                return false;
            }

            source = new Rect(sourceX, sourceY, clippedSourceWidth, clippedSourceHeight);
            return true;
        }

        /// <summary>
        /// Gets the bitmap for a picture, uploading its pixels the first time it is seen.
        /// </summary>
        /// <remarks>
        /// Internal rather than private so the cache rule can be asserted directly. It cannot be
        /// observed through a rendered frame -- the headless platform's recording context throws
        /// from DrawImage -- and "re-uploads when the frame changes, and only then" is exactly the
        /// kind of rule that silently stops holding.
        /// </remarks>
        internal Bitmap? GetOrCreateBitmap(XT.Graphics.TerminalImage image)
        {
            // A cached null is a remembered failure — worth keeping, so a picture that cannot be uploaded is not
            // retried thirty times a second.
            if (_imageBitmaps.TryGetValue(image, out var existing))
            {
                // An animated picture changes under a cache keyed on the image. The emulator bumps a
                // serial whenever the visible pixels move, so comparing that is enough to spot a
                // stale upload without comparing the pixels themselves. A still picture never moves,
                // and its serial stays zero, so this costs it an integer comparison per frame.
                if (existing.FrameSerial == image.FrameSerial)
                    return existing.Bitmap;

                try { existing.Bitmap?.Dispose(); } catch { /* already gone; nothing to salvage */ }

                existing.Bitmap = TryCreateBitmap(image);
                existing.FrameSerial = image.FrameSerial;
                return existing.Bitmap;
            }

            var bitmap = TryCreateBitmap(image);
            _imageBitmaps.Add(image, new CachedBitmap { Bitmap = bitmap, FrameSerial = image.FrameSerial });
            return bitmap;
        }

        /// <summary>Uploads a picture's current pixels, or remembers that it cannot be done.</summary>
        private static Bitmap? TryCreateBitmap(XT.Graphics.TerminalImage image)
        {
            try
            {
                return CreateBitmap(image);
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"[TerminalView] could not upload image {image.Id}: {ex.Message}");
                return null;
            }
        }

        /// <summary>
        /// Disposes every cached bitmap and empties the cache.
        /// </summary>
        /// <remarks>
        /// The weak table drops its entries by itself once the emulator lets go of the pictures, but that only
        /// makes the bitmaps collectable -- it does not free what they hold on the GPU until a finaliser runs.
        /// A terminal being torn down knows it is finished with all of them, and a program animating with Sixel
        /// produces one per frame, so it is worth saying so rather than waiting.
        /// </remarks>
        private void ReleaseImageBitmaps()
        {
            foreach (var entry in _imageBitmaps)
            {
                if (entry.Value is not { } cached)
                    continue;

                cached.Bitmap?.Dispose();
                cached.Bitmap = null;
            }

            _imageBitmaps.Clear();
        }

        /// <summary>
        /// Uploads a decoded picture's pixels into a bitmap.
        /// </summary>
        /// <remarks>
        /// Separated from the caching so the upload itself can be asserted: the byte order and the stride
        /// handling are the two things here that fail silently, as a picture with its colours swapped or its
        /// rows sheared rather than as an error.
        /// </remarks>
        internal static WriteableBitmap CreateBitmap(XT.Graphics.TerminalImage image)
        {
            var writeable = new WriteableBitmap(
                new PixelSize(image.PixelWidth, image.PixelHeight),
                new Vector(96, 96),
                PixelFormat.Bgra8888,
                AlphaFormat.Unpremul);

            using (var locked = writeable.Lock())
            {
                CopyPixels(image, locked.Address, locked.RowBytes);
            }

            return writeable;
        }

        /// <summary>
        /// Draws a cached glyph run at <paramref name="position"/>.
        /// </summary>
        /// <remarks>
        /// Through a TRANSFORM rather than by moving the run. A cached run is replayed at a different
        /// screen row every time the buffer scrolls, so its origin has to change -- and the two ways
        /// to do that are not equivalent. Setting BaselineOrigin measured at 2,914ns and 1,032 bytes
        /// against 1,948ns and 32 for a translate, because assigning it discards what the run had
        /// worked out about itself. It is also a write to an object the context may not have consumed
        /// yet, which a transform never is.
        /// </remarks>
        private static void DrawGlyphs(DrawingContext context, CachedTextRun run, Point position)
        {
            using (context.PushTransform(Matrix.CreateTranslation(position.X, position.Y)))
                context.DrawGlyphRun(run.Foreground ?? Brushes.Transparent, run.Glyphs!);
        }

        /// <summary>
        /// A glyph run for <paramref name="text"/>, or null when this run has to go through
        /// <see cref="FormattedText"/> instead.
        /// </summary>
        /// <remarks>
        /// <para>WHY AT ALL: FormattedText is lazy. Building one costs 33ns because it does nothing;
        /// the shaping happens inside DrawText, on every frame, for every run -- measured at 14,777ns
        /// and 4,032 bytes a call, which is essentially the whole cost of a frame. A terminal does not
        /// need that, because a run's TEXT never changes between frames, only where it is drawn. So
        /// the shaping is done once here and the result blitted: 1,948ns and 32 bytes.</para>
        /// <para>WHY A FAST PATH RATHER THAN A REPLACEMENT: everything FormattedText does that this
        /// does not is real. It picks fallback fonts for characters the primary font lacks, it shapes
        /// clusters, it handles bidi. This takes only the runs where none of that applies and hands
        /// back null for the rest, which is the same division XTerm.NET's print path draws for the
        /// same reason.</para>
        /// <para>The conditions, and what each one is protecting:</para>
        /// <list type="bullet">
        /// <item>ONE CHAR PER CELL. A cluster puts several chars in one cell, so the char count and
        /// the column count stop agreeing and per-cell advances cannot be assigned.</item>
        /// <item>NO SURROGATES. An astral codepoint is two chars and is usually an emoji, which needs
        /// a fallback font and often a colour one.</item>
        /// <item>EVERY GLYPH PRESENT. Glyph 0 is .notdef -- the tofu box. The primary font not having
        /// a character is exactly when fallback is needed, so it is exactly when to decline.</item>
        /// <item>NO DECORATIONS. Those are set on the FormattedText itself.</item>
        /// </list>
        /// <para>Advances are set explicitly to the cell width rather than taken from the font. For a
        /// monospace face the two agree, and pinning them means they agree by construction rather
        /// than by assumption -- a fraction of a pixel of drift per cell would be a hundred and twenty
        /// of them across a line.</para>
        /// </remarks>
        private GlyphRun? TryBuildGlyphRun(string text, int cellCount, FontStyle style, FontWeight weight)
        {
            if (!GlyphRunFastPathEnabled)
                return null;

            if (text.Length == 0 || text.Length != cellCount || _charWidth <= 0)
                return null;

            var glyphTypeface = GlyphTypefaceFor(style, weight);
            if (glyphTypeface is null)
                return null;

            var map = glyphTypeface.CharacterToGlyphMap;
            var glyphs = new GlyphInfo[text.Length];

            for (var i = 0; i < text.Length; i++)
            {
                var c = text[i];
                if (char.IsSurrogate(c))
                    return null;

                if (!map.TryGetGlyph(c, out var glyph) || glyph == 0)
                    return null;

                glyphs[i] = new GlyphInfo(glyph, i, _charWidth, default);
            }

            return new GlyphRun(glyphTypeface, FontSize, text.AsMemory(), glyphs,
                                baselineOrigin: new Point(0, _baseline));
        }

        /// <summary>The glyph typeface for a style and weight, resolved once per font.</summary>
        private GlyphTypeface? GlyphTypefaceFor(FontStyle style, FontWeight weight)
        {
            if (_glyphTypefaces.TryGetValue((style, weight), out var cached))
                return cached;

            GlyphTypeface? resolved;
            try
            {
                resolved = new Typeface(FontFamily, style, weight).GlyphTypeface;
            }
            catch
            {
                // A font that cannot produce a glyph typeface is not an error worth surfacing from a
                // render: it means this run takes the FormattedText path, which is where it would
                // have gone anyway before any of this existed.
                resolved = null;
            }

            _glyphTypefaces[(style, weight)] = resolved;
            return resolved;
        }

        private void RenderHoveredUrl(DrawingContext context, int viewportY, double scale)
        {
            var link = _hoveredLink;
            if (link == null) return;

            Pen? pen = null;
            foreach (var segment in link.Segments)
            {
                int screenRow = segment.Line - viewportY;
                if (screenRow < 0 || screenRow >= _terminal.Rows) continue;

                var cellScale = RowCellScale(segment.Line);
                var startX = Snap(segment.StartCol * _charWidth * cellScale, scale);
                var endX = Snap((segment.EndCol + 1) * _charWidth * cellScale, scale);
                var y = Snap((screenRow + 1) * _charHeight - 1, scale);

                pen ??= new Pen(Foreground, 1);
                context.DrawLine(pen, new Point(startX, y), new Point(endX, y));
            }
        }

        /// <summary>
        /// Draws every OSC 66 block the row pass recorded. Each cell with content inside a run is
        /// its own block (w=0 gives every grapheme one; a single w&gt;0 block is one wide anchor
        /// cell), drawn at <c>scale * n/d</c> times the base size inside a box of the cell's
        /// columns by the run's rows, aligned per the sizing's v and h — the parts of the
        /// protocol the emulator stores but only a renderer can honour.
        /// </summary>
        private void RenderSizedBlocks(DrawingContext context, double scale)
        {
            if (_sizedBlockDraws.Count == 0)
                return;

            // Clipped to the content area, because a sized block is deliberately BIGGER than the
            // cells it was placed in -- that is what OSC 66 is for. A block near the top row extends
            // above it and one on the last row extends below, and both were painted outside the
            // control entirely, over whatever the host had above or below the terminal.
            //
            // Around the whole pass rather than per block: they are drawn together, after every row,
            // so one clip covers all of them for one push.
            var content = new Rect(0, 0, _terminal.Cols * _charWidth, _terminal.Rows * _charHeight);

            using var clip = context.PushClip(content);

            foreach (var draw in _sizedBlockDraws)
            {
                var line = draw.Line;
                var run = draw.Run;
                var sizing = run.Sizing;

                // Once per block, and only when the floor is on — the common frame pays nothing.
                var blockBackdrops = _minimumContrast.Active ? BackdropPlacements(line) : EmptyPlacements;

                var fraction = sizing.Numerator > 0 && sizing.Denominator > 0
                    ? sizing.Numerator / (double)sizing.Denominator
                    : 1.0;
                var magnify = sizing.Scale * fraction;
                if (magnify <= 0)
                    continue;

                for (int x = run.Column; x < run.EndColumn && x < line.Length;)
                {
                    var cell = line[x];
                    // Only a continuation cell is skipped outright -- it has no box of its own.
                    if (cell.Width <= 0)
                    {
                        x++;
                        continue;
                    }

                    var boxX = Snap(x * _charWidth, scale);
                    var boxRight = Snap((x + cell.Width) * _charWidth, scale);
                    var box = new Rect(boxX, draw.StartYPos,
                        Math.Max(0, boxRight - boxX), draw.RowHeight * run.Rows);

                    var background = cell.GetBackgroundBrush(_palette, this.Background);
                    var foreground = cell.GetForegroundBrush(_palette, this.Foreground, _boldIsBright);
                    // The same swap ladder the normal run path applies: inverse, DECSCNM, blink.
                    bool swapped = false;
                    if (cell.Attributes.IsInverse())
                        (foreground, background, swapped) = (background, foreground, !swapped);
                    if (_terminal.ReverseVideo)
                        (foreground, background, swapped) = (background, foreground, !swapped);

                    // The contrast floor applies wherever a cell's text is drawn, in the same slot:
                    // after the swaps, before conceal. A sized block is one cell's glyph, so the
                    // exemption test sees just that. The backdrop check is the run path's rule,
                    // rebuilt from the line because this deferred pass has no running painted list.
                    if (_minimumContrast.Active
                        && !CoveredByBackdrop(blockBackdrops, x, x + cell.Width)
                        && !MinimumContrast.IsExemptRun(cell.Content)
                        && foreground is ISolidColorBrush blockFgSolid
                        && background is ISolidColorBrush blockBgSolid
                        && BufferCellExtensions.IsFullyOpaque(background))
                    {
                        var contrasted = _minimumContrast.Apply(blockFgSolid.Color, blockBgSolid.Color);
                        if (contrasted != blockFgSolid.Color)
                            foreground = new SolidColorBrush(contrasted, blockFgSolid.Opacity);
                    }

                    // And here, the third place a cell's text is drawn. OSC 66 blocks shape their
                    // own runs too.
                    foreground = cell.ApplyConceal(foreground);
                    foreground = cell.ApplyBlinkPhase(foreground, this._cursorBlinkOn);

                    // ReverseVideo for the reason the run path gives: a cancelled double swap leaves
                    // the cell's background differing from the inverted surface.
                    if (swapped || _terminal.ReverseVideo || cell.GetBackgroundColor(_palette).HasValue)
                        context.FillRectangle(background, box);

                    // A blank cell has nothing to shape, but its background belongs to the block and is
                    // already down. This pass is the ONLY thing that paints inside the run -- the row
                    // pass skipped every column of it -- so skipping a space before the fill punched an
                    // unpainted notch between the words of a coloured heading.
                    if (string.IsNullOrEmpty(cell.Content) || cell.Content == " ")
                    {
                        x += cell.Width;
                        continue;
                    }

                    var typeface = new Typeface(FontFamily, cell.GetFontStyle(), cell.GetFontWeight());
                    var formatted = new FormattedText(
                        cell.Content, CultureInfo.CurrentCulture, FlowDirection.LeftToRight,
                        typeface, FontSize, foreground);
                    ApplyLigatureSetting(formatted);

                    // The glyph is drawn at base size under a scale transform, exactly as
                    // DECDWL/DECDHL lines are — the transform is what makes it big, so hinting,
                    // fallback and shaping all behave as they do everywhere else.
                    var drawnWidth = formatted.Width * magnify;
                    var drawnHeight = draw.RowHeight * magnify;

                    var alignX = sizing.HorizontalAlignment switch
                    {
                        XT.Common.TextSizeHorizontalAlignment.Right => box.Right - drawnWidth,
                        XT.Common.TextSizeHorizontalAlignment.Center => box.X + (box.Width - drawnWidth) / 2,
                        _ => box.X,
                    };
                    var alignY = sizing.VerticalAlignment switch
                    {
                        XT.Common.TextSizeVerticalAlignment.Bottom => box.Bottom - drawnHeight,
                        XT.Common.TextSizeVerticalAlignment.Center => box.Y + (box.Height - drawnHeight) / 2,
                        _ => box.Y,
                    };

                    using (context.PushClip(box))
                    {
                        var toOrigin = Matrix.CreateTranslation(-alignX, -alignY);
                        var grow = Matrix.CreateScale(magnify, magnify);
                        var back = Matrix.CreateTranslation(alignX, alignY);
                        using (context.PushTransform(toOrigin * grow * back))
                        {
                            context.DrawText(formatted, new Point(alignX, alignY));
                        }
                    }

                    x += cell.Width;
                }
            }
        }

        /// <summary>
        /// Renders a double-width or double-height line using transforms and clipping.
        /// </summary>
        private void RenderDoubleWidthLine(DrawingContext context, BufferLine line, int screenY, double startYPos, double rowHeight, LineAttribute lineAttr, double scale)
        {
            // Don't cache double-width lines (transform makes caching complex)
            line.Cache = null;

            // Calculate the clip rect for this row
            var clipRect = new Rect(0, startYPos, _terminal.Cols * _charWidth, rowHeight);

            // For double-height lines, we need to clip to show only top or bottom half
            double scaleX = 2.0;
            double scaleY = lineAttr.IsDoubleHeight() ? 2.0 : 1.0;

            // Calculate transform origin and translation
            // We scale from origin (0, startYPos) and then may need to shift for bottom half
            double translateY = 0;
            if (lineAttr == LineAttribute.DoubleHeightBottom)
            {
                // For bottom half, we render at 2x scale but shift up by one row height
                // so the bottom half of the scaled text is visible
                translateY = -rowHeight;
            }

            using (context.PushClip(clipRect))
            {
                // Create transform: scale 2x horizontally (and 2x vertically for double-height)
                // The transform origin is at (0, startYPos)
                var scaleTransform = Matrix.CreateScale(scaleX, scaleY);
                var translateToOrigin = Matrix.CreateTranslation(0, -startYPos);
                var translateBack = Matrix.CreateTranslation(0, startYPos + translateY);
                var combinedTransform = translateToOrigin * scaleTransform * translateBack;

                using (context.PushTransform(combinedTransform))
                {
                    // Render the line content at normal size - the transform will scale it
                    // Only render the first half of the columns since they'll be doubled
                    // Rounded UP, because the division truncates and the cell it truncates away is
                    // the rightmost one on screen. An odd number of columns leaves half a cell of
                    // room at the right edge; a doubled row that reaches the edge -- the border of
                    // a box, which is exactly what vttest draws -- puts its last character there,
                    // and walking Cols / 2 dropped it. The box lost its right-hand side, and only
                    // at odd widths, which is why resizing the window appeared to fix and unfix it.
                    //
                    // Drawing it is safe: the PushClip above trims whatever hangs past the edge, so
                    // the extra cell is clipped rather than spilling.
                    int effectiveCols = (_terminal.Cols + 1) / 2;

                    // Pictures, which this path used to skip entirely -- so a picture on a line a
                    // program had doubled simply disappeared, and the text still stored in those
                    // cells was drawn in its place. Vanishing would have been the lesser bug.
                    //
                    // Inside the transform with everything else, so a doubled picture is doubled by
                    // the same matrix that doubles the text around it. The runs are collected into a
                    // list that is thrown away: this path sets line.Cache = null a few lines up,
                    // because a transform is not something a cached draw list can carry.
                    var dwPlacements = OrderedPlacements(line);
                    var dwPainted = new List<XT.Graphics.LinePlacement>();
                    var dwScratch = new List<CachedTextRun>();
                    var dwNext = 0;

                    for (; dwNext < dwPlacements.Count && dwPlacements[dwNext].ZIndex < 0; dwNext++)
                    {
                        AppendImageRun(line, dwPlacements[dwNext], dwScratch, dwPainted);
                        dwPainted.Add(dwPlacements[dwNext]);
                    }

                    // Drawn on the spot rather than left to a later pass: collecting no longer paints
                    // anything by itself, and these have to go down inside the transform that doubles
                    // them, before the text that sits on top of them.
                    DrawLineRuns(context, dwScratch, startYPos, rowHeight, scale);
                    dwScratch.Clear();

                    for (int x = 0; x < effectiveCols && x < line.Length;)
                    {
                        var cell = line[x];
                        string text = String.Empty;
                        int cellCount = 0;
                        int runStartX = 0;
                        var dwRunHasBackdrop = CoveredByBackdrop(dwPainted, x, x + Math.Max(1, cell.Width));

                        // Skip placeholder cells (width 0) that follow wide characters
                        if (cell.Width == 0)
                        {
                            x++;
                            continue;
                        }
                        else if (cell.Width == 1)
                        {
                            // Collect consecutive cells with same attributes
                            var textBuilder = new StringBuilder();
                            cellCount = 0;
                            runStartX = x;
                            while (x < line.Length && x < effectiveCols)
                            {
                                var currentCell = line[x];
                                if (currentCell.Width != 1 || currentCell.Attributes != cell.Attributes
                                    || CoveredByBackdrop(dwPainted, x, x + 1) != dwRunHasBackdrop)
                                    break;
                                textBuilder.Append(currentCell.Content);
                                cellCount += currentCell.Width;
                                x += currentCell.Width;
                            }
                            text = textBuilder.ToString();
                        }
                        else if (cell.Width == 2)
                        {
                            text = cell.Content;
                            cellCount = cell.Width;
                            runStartX = x;
                            x += cell.Width;
                        }

                        var startX = Snap(runStartX * _charWidth, scale);
                        var endX = Snap((runStartX + cellCount) * _charWidth, scale);
                        var rect = new Rect(startX, startYPos, Math.Max(0, endX - startX), rowHeight);
                        var background = cell.GetBackgroundBrush(_palette, this.Background);
                        var foreground = cell.GetForegroundBrush(_palette, this.Foreground, _boldIsBright);
                        // Apply cell-level inverse attribute
                        bool swapped = false;
                        if (cell.Attributes.IsInverse())
                            (foreground, background, swapped) = (background, foreground, !swapped);
                        // Apply terminal-wide reverse video mode (DECSCNM)
                        if (_terminal.ReverseVideo)
                            (foreground, background, swapped) = (background, foreground, !swapped);

                        // The contrast floor, in the same slot as the run path: after the swaps,
                        // before conceal. Doubled lines draw their own text, so without this a
                        // program's unreadable colour became readable everywhere EXCEPT its
                        // double-width headings -- which are the text it most wanted seen.
                        if (_minimumContrast.Active
                            && !dwRunHasBackdrop
                            && !MinimumContrast.IsExemptRun(text)
                            && foreground is ISolidColorBrush dwFgSolid
                            && background is ISolidColorBrush dwBgSolid
                            && BufferCellExtensions.IsFullyOpaque(background))
                        {
                            var contrasted = _minimumContrast.Apply(dwFgSolid.Color, dwBgSolid.Color);
                            if (contrasted != dwFgSolid.Color)
                                foreground = new SolidColorBrush(contrasted, dwFgSolid.Opacity);
                        }

                        // After the swaps, as everywhere else. A DECDWL/DECDHL row draws its own
                        // text rather than going through the run path, so conceal has to be applied
                        // here too -- otherwise a concealed password shows in full on any line a
                        // program happened to double.
                        foreground = cell.ApplyConceal(foreground);
                        foreground = cell.ApplyBlinkPhase(foreground, this._cursorBlinkOn);

                        var typeface = new Typeface(FontFamily, cell.GetFontStyle(), cell.GetFontWeight());
                        var formattedText = new FormattedText(text, CultureInfo.CurrentCulture, FlowDirection.LeftToRight, typeface, FontSize, foreground);
                        ApplyLigatureSetting(formattedText);
                        var td = cell.GetTextDecorations();
                        if (td != null)
                            formattedText.SetTextDecorations(td);

                        var position = new Point(startX, startYPos);

                        if ((swapped || _terminal.ReverseVideo || cell.GetBackgroundColor(_palette).HasValue)
                            && !dwRunHasBackdrop)
                            context.FillRectangle(background, rect);
                        context.DrawText(formattedText, position);

                        // Underlines are drawn by hand everywhere a cell is painted, and this loop
                        // is one of those places: leaving it out silently un-underlined every
                        // DECDWL/DECDHL line, plain SGR 4 included. Untransformed geometry on
                        // purpose -- the matrix pushed above doubles it along with the glyphs. The
                        // run is per-frame because double-width lines are never cached, so the
                        // geometry cache dies with it; these lines are rare enough not to matter.
                        var dwUnderline = cell.Attributes.GetUnderlineStyle();
                        if (dwUnderline != XT.Common.UnderlineStyle.None)
                        {
                            var dwBrush = cell.GetUnderlineColor(_palette) is { } uc
                                ? new ImmutableSolidColorBrush(uc)
                                : foreground;

                            // Through the blink phase, as on the run path: an SGR 58 colour
                            // resolved opaque here and kept a doubled row's underline lit through
                            // the off half of the phase.
                            dwBrush = cell.ApplyBlinkPhase(dwBrush, this._cursorBlinkOn);
                            var dwRun = new CachedTextRun(null, runStartX, cellCount, null,
                                                          UnderlineStyle: dwUnderline, UnderlineBrush: dwBrush);
                            DrawUnderline(context, dwRun, position, Math.Max(0, endX - startX), rowHeight);
                        }
                    }

                    // And the ones in FRONT of the text, after it, so the layering means the same
                    // thing here as it does on an ordinary row.
                    for (; dwNext < dwPlacements.Count; dwNext++)
                    {
                        AppendImageRun(line, dwPlacements[dwNext], dwScratch, dwPainted);
                        dwPainted.Add(dwPlacements[dwNext]);
                    }

                    DrawLineRuns(context, dwScratch, startYPos, rowHeight, scale);
                }
            }
        }

        /// <summary>
        /// Renders the selection overlay.
        /// </summary>
        private void RenderSelection(DrawingContext context, int viewportY, double scale)
        {
            if (!_terminal.Selection.HasSelection)
                return;

            int viewportLines = _terminal.Rows;

            // The selection API takes a row relative to the LIVE scroll position -- it adds YDisp
            // itself -- while the frame around this was composed against the viewportY the caller
            // snapshotted. Output arriving mid-frame moves YDisp, and the highlight was then drawn
            // over rows the text underneath it no longer occupied: a band of selection sitting one or
            // two lines away from the selected words.
            //
            // Shifting by the difference asks about the snapshot's rows in the API's own terms.
            int toLiveRows = viewportY - _terminal.Buffer.YDisp;

            for (int screenY = 0; screenY < viewportLines; screenY++)
            {
                // Find cells that are selected in this row
                int? selectionStartX = null;
                int? selectionEndX = null;

                for (int x = 0; x < _terminal.Cols; x++)
                {
                    if (_terminal.Selection.IsCellSelected(x, screenY + toLiveRows))
                    {
                        if (!selectionStartX.HasValue)
                            selectionStartX = x;
                        selectionEndX = x;
                    }
                    else if (selectionStartX.HasValue)
                    {
                        // End of a selection run - draw it
                        DrawSelectionRect(context, selectionStartX.Value, selectionEndX!.Value + 1, screenY, scale,
                                          RowCellScale(viewportY + screenY));
                        selectionStartX = null;
                        selectionEndX = null;
                    }
                }

                // Draw remaining selection at end of row
                if (selectionStartX.HasValue)
                {
                    DrawSelectionRect(context, selectionStartX.Value, selectionEndX!.Value + 1, screenY, scale,
                                      RowCellScale(viewportY + screenY));
                }
            }
        }

        /// <summary>How many columns the cell at this position occupies; 1 when there is nothing there.</summary>
        private int CellWidthAt(int absoluteRow, int col)
        {
            var line = _terminal.Buffer.GetLine(absoluteRow);
            if (line == null || col < 0 || col >= line.Length)
                return 1;

            // GetWidth rather than line[col].Width: the indexer hands back a copy of the whole cell
            // to read one field, which this file has paid for before.
            return Math.Max(1, line.GetWidth(col));
        }

        /// <summary>
        /// How many normal cell widths one cell on <paramref name="absoluteRow"/> actually occupies
        /// on screen: 2 on a DECDWL or DECDHL row, 1 everywhere else.
        /// </summary>
        /// <remarks>
        /// <para>The row pass draws doubled rows inside a 2x transform, so the cells themselves come
        /// out right. Everything drawn as an OVERLAY -- the cursor, the selection, the hovered-link
        /// underline -- is drawn afterwards, outside that transform, and so has to double its own
        /// geometry. None of it did.</para>
        /// <para>The result is visible rather than subtle: on a doubled row the selection covered the
        /// left half of what was selected, the link underline stopped halfway along the link, and the
        /// cursor sat at half the column it marked -- so at column 40 it was twenty cells to the left
        /// of its own character.</para>
        /// </remarks>
        private double RowCellScale(int absoluteRow)
        {
            var line = _terminal.Buffer.GetLine(absoluteRow);
            if (line == null)
                return 1.0;

            var attr = line.LineAttribute;
            return attr == LineAttribute.DoubleWidth || attr.IsDoubleHeight() ? 2.0 : 1.0;
        }

        private void DrawSelectionRect(DrawingContext context, int startX, int endX, int screenY, double scale,
                                       double cellScale)
        {
            var x1 = Snap(startX * _charWidth * cellScale, scale);
            var x2 = Snap(endX * _charWidth * cellScale, scale);
            var y1 = Snap(screenY * _charHeight, scale);
            var y2 = Snap((screenY + 1) * _charHeight, scale);

            var rect = new Rect(x1, y1, Math.Max(0, x2 - x1), Math.Max(0, y2 - y1));
            context.FillRectangle(SelectionBrush, rect);
        }

        private void RenderCursor(DrawingContext context, int viewportY, double scale)
        {
            // No process, no cursor. The checks below are all about what the BUFFER says, and a buffer says
            // the same thing whether or not anything is attached to it — so a view that has never launched,
            // or whose process has exited, paints a block cursor in its top-left corner with nothing behind
            // it. A cursor represents a shell waiting for input; when there is no shell there is nothing for
            // it to represent, and offering one to type at is a lie.
            if (!IsLive || SuppressCursor)
                return;

            // Nowhere meaningful to put it — see CaretHidden.
            if (CaretHidden)
                return;

            // Only show cursor if terminal wants it visible (controlled by escape sequences)
            if (!_terminal.CursorVisible)
                return;

            // Only show cursor if in "on" phase of blink cycle (or not blinking)
            if (!_cursorBlinkOn)
                return;

            var (cursorX, absoluteCursorY) = CaretPosition;

            // Check if cursor is visible in current viewport
            if (absoluteCursorY < viewportY || absoluteCursorY >= viewportY + _terminal.Rows)
                return;

            // Calculate screen position
            int screenY = absoluteCursorY - viewportY;

            // A doubled row draws each cell twice as wide, and this pass runs outside the transform
            // that does it -- so the caret has to double its own geometry or it lands half a screen
            // to the left of the character it marks.
            double cellScale = RowCellScale(absoluteCursorY);

            // And a WIDE character occupies two cells. A block caret one cell wide over a two-cell
            // glyph repainted the whole glyph in the background colour and then filled only its left
            // half, so the right half of the character was simply erased.
            int cursorCells = Math.Max(1, CellWidthAt(absoluteCursorY, cursorX));

            double posX = Snap(cursorX * _charWidth * cellScale, scale);
            double posY = Snap(screenY * _charHeight, scale);
            double nextX = Snap((cursorX + cursorCells) * _charWidth * cellScale, scale);
            double nextY = Snap((screenY + 1) * _charHeight, scale);
            double cellWidth = Math.Max(0, nextX - posX);
            double cellHeight = Math.Max(0, nextY - posY);

            var cursorBrush = new SolidColorBrush(CursorColor);

            // Render based on cursor style (use property which syncs with terminal)
            switch (CursorStyle)
            {
                case XT.Common.CursorStyle.Block:
                    // TODO Use ConsoleFontBrush
                    if (IsFocused)
                    {
                        // Filled block when focused
                        context.FillRectangle(cursorBrush, new Rect(posX, posY, cellWidth, cellHeight));

                        // Draw the character under cursor with inverted colors
                        var line = _terminal.Buffer.GetLine(absoluteCursorY);
                        if (line != null && cursorX < line.Length)
                        {
                            var cell = line[cursorX];
                            var charContent = cell.Content ?? " ";
                            var typeface = new Typeface(FontFamily, FontStyle, FontWeight);
                            var invertedBrush = cell.GetBackgroundBrush(_palette, this.Background);
                            var formattedText = new FormattedText(
                                charContent,
                                CultureInfo.CurrentCulture,
                                FlowDirection.LeftToRight,
                                typeface,
                                FontSize,
                                invertedBrush);
                            context.DrawText(formattedText, new Point(posX, posY));
                        }
                    }
                    else
                    {
                        // Outline block when not focused
                        var pen = new Pen(cursorBrush, 1);
                        context.DrawRectangle(pen, new Rect(posX, posY, cellWidth, cellHeight));
                    }
                    break;

                case XT.Common.CursorStyle.Underline:
                    {
                        // Draw underline cursor (2 pixels high at bottom of cell)
                        var underlineHeight = Math.Min(2.0, cellHeight);
                        context.FillRectangle(cursorBrush, new Rect(posX, posY + cellHeight - underlineHeight, cellWidth, underlineHeight));
                    }
                    break;

                case XT.Common.CursorStyle.Bar:
                    {
                        // Draw bar cursor (2 pixels wide at left of cell)
                        var barWidth = Math.Min(2.0, cellWidth);
                        context.FillRectangle(cursorBrush, new Rect(posX, posY, barWidth, cellHeight));
                    }
                    break;
            }
        }

        private static double Snap(double value, double scale)
        {
            return Math.Round(value * scale, MidpointRounding.AwayFromZero) / scale;
        }

        /// <summary>
        /// Renders the IME preedit (composition) text overlay at the cursor position.
        /// This displays the uncommitted text that the IME is composing, with an underline
        /// to indicate it is not yet committed.
        /// </summary>
        private void RenderPreeditText(DrawingContext context, int viewportY, double scale)
        {
            var preeditText = _inputMethodClient?.PreeditText;
            if (string.IsNullOrEmpty(preeditText))
                return;

            int cursorX = _terminal.Buffer.X;
            int cursorY = _terminal.Buffer.Y;
            int absoluteCursorY = _terminal.Buffer.YBase + cursorY;

            // Only render if cursor is visible in current viewport
            if (absoluteCursorY < viewportY || absoluteCursorY >= viewportY + _terminal.Rows)
                return;

            int screenY = absoluteCursorY - viewportY;
            var cellScale = RowCellScale(absoluteCursorY);
            double posX = Snap(cursorX * _charWidth * cellScale, scale);
            double posY = Snap(screenY * _charHeight, scale);
            double cellHeight = Snap((screenY + 1) * _charHeight, scale) - posY;

            var typeface = new Typeface(FontFamily, FontStyle, FontWeight);
            var foreground = GetValue(ForegroundProperty) ?? Brushes.White;

            // The same rule the cell renderer follows, which is not "always the palette": a default
            // background resolves to the emulator's colour only when the host's own brush is fully
            // opaque, and otherwise stays the host's. A translucent or gradient host is asking to be
            // seen through, and no RGB palette entry can express that.
            //
            // Claiming to follow that rule and then using the palette unconditionally was worse than
            // either choice on its own: it made the composition box the one opaque rectangle on an
            // otherwise see-through terminal. Through the same IsFullyOpaque the cell path uses, so
            // there is one rule rather than a copy of it here.
            var styled = GetValue(BackgroundProperty) ?? Brushes.Black;
            var background = BufferCellExtensions.IsFullyOpaque(styled)
                ? new SolidColorBrush(BufferCellExtensions.FromRgb(_palette.Background))
                : styled;

            var formattedText = new FormattedText(
                preeditText,
                CultureInfo.CurrentCulture,
                FlowDirection.LeftToRight,
                typeface,
                FontSize,
                foreground);
            ApplyLigatureSetting(formattedText);

            // Bounded by the right edge, and CLIPPED to it. A composition is as long as the user
            // makes it -- an IME buffers a whole phrase before committing -- and this drew it at its
            // full measured width from the cursor, so a long one ran off the end of the control and
            // painted over whatever the host had beside the terminal.
            //
            // The SCALED width is what gets bounded: on a doubled row the composition is drawn twice
            // as wide, so bounding its unscaled measurement would let the drawn glyphs run past an
            // edge the box stopped at.
            double textWidth = FitWidth(posX, formattedText.Width * cellScale, _terminal.Cols * _charWidth);
            if (textWidth <= 0)
                return;

            using (context.PushClip(new Rect(posX, posY, textWidth, cellHeight)))
            {
                // Draw background behind preedit text to cover existing content
                context.FillRectangle(background, new Rect(posX, posY, textWidth, cellHeight));

                // Draw the preedit text
                if (cellScale == 1.0)
                {
                    context.DrawText(formattedText, new Point(posX, posY));
                }
                else
                {
                    // The row's text is drawn under the same horizontal scale. This overlay is
                    // outside that row transform, so apply it around the preedit origin as well;
                    // scaling only the background geometry would leave the composing glyphs at half
                    // width. Inside the clip, so a doubled composition is still bounded by the edge.
                    var toOrigin = Matrix.CreateTranslation(-posX, -posY);
                    var widen = Matrix.CreateScale(cellScale, 1.0);
                    var back = Matrix.CreateTranslation(posX, posY);
                    using (context.PushTransform(toOrigin * widen * back))
                        context.DrawText(formattedText, new Point(posX, posY));
                }

                // Draw underline to indicate uncommitted composition text
                double underlineY = posY + cellHeight - Math.Max(1.0, scale);
                var pen = new Pen(foreground, Math.Max(1.0, scale));
                context.DrawLine(pen, new Point(posX, underlineY), new Point(posX + textWidth, underlineY));
            }
        }

    }
}
