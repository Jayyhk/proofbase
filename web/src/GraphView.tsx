import { useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react'
import { fetchProofSvg, fetchProofSource, fetchDeclaration, type Declaration } from './api'
import Modal from './Modal'

// https://feathericons.com/?modules=maximize-2
function ExpandIcon() {
  return (
    <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor"
      strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">
      <polyline points="15 3 21 3 21 9" />
      <polyline points="9 21 3 21 3 15" />
      <line x1="21" y1="3" x2="14" y2="10" />
      <line x1="3" y1="21" x2="10" y2="14" />
    </svg>
  )
}

// "Erdos958.counterexample" -> "counterexample"
function shortName(name: string): string {
  return name.split('.').pop() ?? name
}

// severity number -> css class
function severityClass(severity: number): string {
  if (severity >= 2) return 'flag'
  if (severity === 1) return 'flag-trust'
  return ''
}

export default function GraphView({ id, name, onBack }: { id: number; name: string; onBack: () => void }) {
  const [svg, setSvg] = useState<string | null>(null) // the graphviz svg as text, null while loading
  const [notFound, setNotFound] = useState(false) // true when the proof has no graph
  const [error, setError] = useState<string | null>(null) // a failure
  const [detail, setDetail] = useState<Declaration | null>(null) // clicked declaration, null = panel closed
  const [source, setSource] = useState<string | null>(null) // the .lean text

  const viewport = useRef<HTMLDivElement>(null) // the fixed window you look through. the canvas pans and zooms inside it
  const canvas = useRef<HTMLDivElement>(null) // the div holding the svg
  const view = useRef({ x: 0, y: 0, zoom: 1 }) // pan offset x/y and zoom scale

  // load the svg and .lean file for this proof.
  // cancelled stops a slow response from a previous proof overwriting this one.
  useEffect(() => {
    let cancelled = false
    setSvg(null)
    setNotFound(false)
    setSource(null)
    fetchProofSvg(id)
      .then((text) => {
        if (cancelled) return
        if (text === null) setNotFound(true)
        else setSvg(text)
      })
      .catch((e) => setError(String(e)))
    fetchProofSource(id)
      .then((text) => {
        if (!cancelled) setSource(text)
      })
      .catch(() => {})
    return () => {
      cancelled = true
    }
  }, [id])

  // highlight the selected node and its neighbors.
  // the svg was injected as raw html so react can't set classes on it, super annoying to do it by hand
  useEffect(() => {
    const graph = canvas.current?.querySelector('svg')
    if (!graph) return
    const nodes = graph.querySelectorAll('.node')
    const edges = graph.querySelectorAll('.edge')
    if (!detail) {
      graph.classList.remove('has-selection')
      nodes.forEach((node) => node.classList.remove('hl', 'selected'))
      edges.forEach((edge) => edge.classList.remove('hl'))
      return
    }
    const selectedId = String(detail.id)
    const highlighted = new Set([
      selectedId,
      ...detail.dependencies.map((dep) => String(dep.id)),
      ...detail.dependents.map((dep) => String(dep.id)),
    ])
    graph.classList.add('has-selection')
    nodes.forEach((node) => {
      const nodeId = node.getAttribute('data-id') ?? ''
      node.classList.toggle('hl', highlighted.has(nodeId))
      node.classList.toggle('selected', nodeId === selectedId)
    })
    edges.forEach((edge) =>
      edge.classList.toggle(
        'hl',
        edge.getAttribute('data-from') === selectedId || edge.getAttribute('data-to') === selectedId
      )
    )
  }, [detail, svg])

  // esc closes the side panel. the listener goes on window as panel isn't focusable.
  useEffect(() => {
    if (!detail) return
    function onKey(e: KeyboardEvent) {
      if (e.key === 'Escape') setDetail(null)
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [detail])

  // write the pan/zoom straight to the DOM.
  // since view is a ref, every place that changes view has to call this.
  function apply() {
    const current = view.current
    if (canvas.current)
      canvas.current.style.transform = `translate(${current.x}px, ${current.y}px) scale(${current.zoom})`
  }

  // fetch one declaration and open the side panel.
  // setDetail does the blue highlight on the declaration and dims non-neighbors.
  function openDecl(declId: number) {
    fetchDeclaration(declId).then(setDetail).catch((err) => setError(String(err)))
  }

  // pan a node into the middle of the viewport
  function centerOn(declId: number) {
    const frame = viewport.current
    const node = canvas.current?.querySelector(`.node[data-id="${declId}"]`)
    if (!frame || !node) return
    const nodeRect = node.getBoundingClientRect()
    view.current.x += frame.clientWidth / 2 - (nodeRect.left + nodeRect.width / 2) // frame middle minus node centre, horizontally
    view.current.y += frame.clientHeight / 2 - (nodeRect.top + nodeRect.height / 2) // frame middle minus node centre, vertically
    apply()
  }

  // zoom for +/- buttons
  function zoomBy(factor: number) {
    const frame = viewport.current
    if (!frame) return
    const centerX = frame.clientWidth / 2
    const centerY = frame.clientHeight / 2
    const old = view.current
    const zoom = Math.min(Math.max(old.zoom * factor, 0.05), 4)
    // s = screen point to hold still, g = the graph coord under it, x/k = old pan/zoom, x'/k' = new pan/zoom
    // s = x  + g*k
    // s = x' + g*k'
    // g  = (s - x)/k
    // x' = s - (s - x)*k'/k
    view.current = {
      zoom,
      x: centerX - (centerX - old.x) * (zoom / old.zoom),
      y: centerY - (centerY - old.y) * (zoom / old.zoom),
    }
    apply()
  }

  // fit the graph to the viewport when a new svg arrives. unfitted graph is not shown
  useLayoutEffect(() => {
    const frame = viewport.current
    const graph = canvas.current?.querySelector('svg')
    if (!svg || !frame || !graph) return

    const graphWidth = graph.viewBox.baseVal.width
    const graphHeight = graph.viewBox.baseVal.height
    const zoom = Math.min(frame.clientWidth / graphWidth, frame.clientHeight / graphHeight, 1) * 0.9
    view.current = {
      zoom,
      x: (frame.clientWidth - graphWidth * zoom) / 2,
      y: (frame.clientHeight - graphHeight * zoom) / 2,
    }
    apply()
  }, [svg])

  // wheel zoom. same math as zoomBy but s is the cursor
  useEffect(() => {
    const frame = viewport.current
    if (!frame) return

    function onWheel(e: WheelEvent) {
      e.preventDefault() // don't scroll up/down
      const rect = frame!.getBoundingClientRect()
      const mouseX = e.clientX - rect.left
      const mouseY = e.clientY - rect.top
      const old = view.current
      const zoom = Math.min(Math.max(old.zoom * Math.exp(-e.deltaY * 0.003), 0.05), 4)
      view.current = {
        zoom,
        x: mouseX - (mouseX - old.x) * (zoom / old.zoom),
        y: mouseY - (mouseY - old.y) * (zoom / old.zoom),
      }
      apply()
    }
    frame.addEventListener('wheel', onWheel, { passive: false }) // react's onWheel prop is passive, so the page would scroll up/down while zooming if passive was true
    return () => frame.removeEventListener('wheel', onWheel)
  }, [])

  // drag to pan, click to open a declaration. over 5px of movement makes it a pan
  function onPointerDown(e: React.PointerEvent) {
    const frame = viewport.current
    const startX = e.clientX
    const startY = e.clientY
    const target = e.target
    let lastX = e.clientX
    let lastY = e.clientY
    let panning = false

    // once it's a pan, shift the view by the delta since the last move
    function onMove(ev: PointerEvent) {
      if (!panning && Math.hypot(ev.clientX - startX, ev.clientY - startY) > 5) {
        panning = true
        if (frame) frame.style.cursor = 'grabbing'
      }
      if (panning) {
        view.current.x += ev.clientX - lastX
        view.current.y += ev.clientY - lastY
        apply()
      }
      lastX = ev.clientX
      lastY = ev.clientY
    }

    // if it never became a pan, treat it as a click on whatever we pressed
    function onUp() {
      window.removeEventListener('pointermove', onMove)
      window.removeEventListener('pointerup', onUp)
      if (frame) frame.style.cursor = 'grab'
      if (panning) return
      const node = (target as Element).closest?.('.node')
      const nodeId = node?.getAttribute('data-id')
      if (nodeId) openDecl(Number(nodeId))
      else setDetail(null)
    }

    window.addEventListener('pointermove', onMove)
    window.addEventListener('pointerup', onUp)
  }

  // the graphviz svg, injected as raw html.
  // clicking a node calls setDetail, which re-renders and would re-inject the same svg if we didn't useMemo.
  const graphCanvas = useMemo(
    () =>
      svg ? <div className="graph-canvas" ref={canvas} dangerouslySetInnerHTML={{ __html: svg }} /> : null,
    [svg]
  )

  // no graph to show: 404 (no such proof, or one still compiling), or a failure before the svg loaded
  if (notFound || (error && !svg)) {
    return (
      <div className="graph-full">
        <div className="graph-notfound">
          <h2>{!notFound ? 'Could not load proof' : name ? 'No graph yet' : 'Proof not found'}</h2>
          <p>
            {notFound ? (
              name ? (
                <>
                  <code>{name}</code> has no graph. It may still be compiling, or the compile failed.
                </>
              ) : (
                'This proof could not be found.'
              )
            ) : (
              error
            )}
          </p>
          <button className="add" onClick={onBack}>← back to library</button>
        </div>
      </div>
    )
  }

  // the graph page
  return (
    <div className="graph-full">
      <button className="add graph-back" onClick={onBack}>← back</button>
      <h1 className="graph-title">{name}</h1>
      {error && <p className="error graph-error">{error}</p>}
      {/* the fixed frame */}
      <div className="graph-viewport" ref={viewport} onPointerDown={onPointerDown}>
        {graphCanvas}
      </div>
      <div className="graph-zoom">
        <button onClick={() => zoomBy(1.6)}>+</button>
        <button onClick={() => zoomBy(1 / 1.6)}>−</button>
      </div>
      {/* overlays the viewport rather than shrinking it so centering math is ok */}
      {detail && (
        <DeclarationPanel
          decl={detail}
          source={source}
          onClose={() => setDetail(null)}
          onNavigate={(declId) => {
            openDecl(declId)
            centerOn(declId)
          }}
        />
      )}
    </div>
  )
}

// side panel for the clicked declaration
function DeclarationPanel({
  decl,
  source,
  onClose,
  onNavigate,
}: {
  decl: Declaration
  source: string | null
  onClose: () => void
  onNavigate: (declId: number) => void
}) {
  const [expanded, setExpanded] = useState(false)

  // cut this declaration out of the whole .lean file
  const snippet =
    source != null && decl.line_start != null
      ? source.split('\n').slice(decl.line_start - 1, decl.line_end ?? decl.line_start).join('\n')
      : null

  // the side panel box: name, kind, lines, source button, axioms, then the two neighbor lists
  return (
    <aside className="graph-panel">
      <button className="panel-close" onClick={onClose}>×</button>
      <h2>{shortName(decl.name)}</h2>
      {/* the namespaced name if present */}
      {decl.name !== shortName(decl.name) && <p className="panel-full">{decl.name}</p>}
      <dl>
        <dt>kind</dt>
        <dd>{decl.kind}</dd>
        {decl.line_start != null && (
          <>
            <dt>lines</dt>
            <dd>{decl.line_start}–{decl.line_end}</dd>
          </>
        )}
      </dl>
      {/* button to see .lean source in a modal */}
      {snippet && (
        <>
          <button className="source-btn" onClick={() => setExpanded(true)}>
            source <ExpandIcon />
          </button>
          {expanded && (
            <Modal onClose={() => setExpanded(false)}>
              <h2>{shortName(decl.name)}</h2>
              <pre className="source-full">{snippet}</pre>
            </Modal>
          )}
        </>
      )}
      {/* every axiom this declaration transitively depends on, not just direct ones */}
      <h3>axioms ({decl.axioms.length})</h3>
      <ul className="panel-axioms">
        {decl.axioms.map((axiom) => (
          <li key={axiom.name} className={severityClass(axiom.severity)}>
            <span>{axiom.name}</span>
            <span className="axiom-kind">{axiom.kind}</span>
          </li>
        ))}
      </ul>
      <NeighborList title="dependencies" items={decl.dependencies} onNavigate={onNavigate} />
      <NeighborList title="dependents" items={decl.dependents} onNavigate={onNavigate} />
    </aside>
  )
}

// one neighbor list, with declarations colored by severity
function NeighborList({
  title,
  items,
  onNavigate,
}: {
  title: string
  items: { id: number; name: string; severity: number }[]
  onNavigate: (declId: number) => void
}) {
  return (
    <>
      <h3>{title} ({items.length})</h3>
      <ul className="panel-neighbors">
        {items.map((neighbor) => (
          <li key={neighbor.id}>
            <button className={severityClass(neighbor.severity)} onClick={() => onNavigate(neighbor.id)}>
              {shortName(neighbor.name)}
            </button>
          </li>
        ))}
      </ul>
    </>
  )
}
