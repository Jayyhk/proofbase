import { useEffect, useState } from 'react'
import { fetchProofs, fetchVersions, compileProof, deleteProof, renameProof, type Proof } from './api'
import GraphView from './GraphView'
import Modal from './Modal'

// https://feathericons.com/?modules=trash-2
function TrashIcon() {
  return (
    <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor"
      strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">
      <polyline points="3 6 5 6 21 6" />
      <path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2" />
      <line x1="10" y1="11" x2="10" y2="17" />
      <line x1="14" y1="11" x2="14" y2="17" />
    </svg>
  )
}

// https://feathericons.com/?modules=settings
function GearIcon() {
  return (
    <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor"
      strokeWidth="2" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">
      <circle cx="12" cy="12" r="3" />
      <path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83-2.83l.06-.06a1.65 1.65 0 0 0 .33-1.82 1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 2.83-2.83l.06.06a1.65 1.65 0 0 0 1.82.33H9a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 2.83l-.06.06a1.65 1.65 0 0 0-.33 1.82V9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z" />
    </svg>
  )
}

// left side col headers, each 2 rows tall
const LEFT_COLUMNS = [
  { key: 'name', top: '', bottom: 'proof' },
  { key: 'added', top: 'date', bottom: 'added' },
  { key: 'lean_version', top: 'lean', bottom: 'version' },
  { key: 'roots', top: 'top-level', bottom: 'declarations' },
  { key: 'declarations', top: 'total', bottom: 'declarations' },
  { key: 'edges', top: 'dependency', bottom: 'edges' },
] as const

// the 5 axiom risk cols under the "nonstandard axiom usage" banner
const AXIOM_COLUMNS = [
  { key: 'trust', label: 'trust' },
  { key: 'custom', label: 'custom' },
  { key: 'sorry', label: 'sorry' },
  { key: 'unsafe', label: 'unsafe' },
  { key: 'flagged', label: 'total' },
] as const

// all cols of a row
const COLUMNS = [
  ...LEFT_COLUMNS.slice(1).map((header) => header.key),
  ...AXIOM_COLUMNS.map((axiom) => axiom.key),
]

// strip the toolchain prefix for display: "leanprover/lean4:v4.33.0" -> "4.33.0"
function leanVersion(version: string): string {
  return version ? version.replace(/^leanprover\/lean4:v?/, '') : ''
}

// assign a color to a table cell: yellow for trust only, red for custom/sorry/unsafe, plain otherwise
function severityClass(column: keyof Proof, proof: Proof): string {
  const isAxiomColumn = AXIOM_COLUMNS.some((axiom) => axiom.key === column)
  if (!isAxiomColumn || Number(proof[column]) === 0) return ''
  if (column === 'trust') return 'flag-trust'
  if (column === 'flagged') {
    return Number(proof.custom) + Number(proof.sorry) + Number(proof.unsafe) > 0 ? 'flag' : 'flag-trust'
  }
  return 'flag'
}

// read the selected proof id out of the url /proof/<id>
function proofFromUrl(): number | null {
  const match = window.location.pathname.match(/^\/proof\/(\d+)$/)
  return match ? Number(match[1]) : null
}

function App() {
  // all of the app's state
  const [proofs, setProofs] = useState<Proof[]>([]) // the table rows
  const [error, setError] = useState<string | null>(null) // red message, null = none
  const [sortKey, setSortKey] = useState<keyof Proof>('added') // column being sorted
  const [sortDir, setSortDir] = useState<1 | -1>(-1) // 1 ascending, -1 descending
  const [hovered, setHovered] = useState<keyof Proof | null>(null) // table header the mouse is over
  const [selected, setSelected] = useState<number | null>(proofFromUrl) // open proof, null = show the table
  const [failLog, setFailLog] = useState<Proof | null>(null) // proof whose error popup is open
  const [adding, setAdding] = useState(false) // is the add proof popup open?
  const [versions, setVersions] = useState<string[]>([]) // lean versions for the dropdown
  const [version, setVersion] = useState('') // the version picked
  const [file, setFile] = useState<File | null>(null) // the chosen .lean file
  const [checkedIds, setCheckedIds] = useState<Set<number>>(new Set()) // ticked rows, for bulk delete
  const [renaming, setRenaming] = useState<Proof | null>(null) // proof whose options popup is open
  const [renameValue, setRenameValue] = useState('') // text in the rename box

  // runs once at startup: load the proofs and versions, and keep the view in sync with back/forward
  useEffect(() => {
    fetchProofs().then(setProofs).catch((e) => setError(String(e)))
    fetchVersions().then((list) => {
      setVersions(list)
      setVersion((current) => current || list[0] || '')
    }).catch((e) => setError(String(e)))
    const onPop = () => setSelected(proofFromUrl())
    window.addEventListener('popstate', onPop)
    return () => window.removeEventListener('popstate', onPop)
  }, [])

  // while any proof is compiling, refetch the list every 3s so the status updates
  const anyInProgress = proofs.some((proof) => proof.status === 'compiling' || proof.status === 'queued')
  useEffect(() => {
    if (!anyInProgress) return
    const timer = setInterval(() => {
      fetchProofs().then(setProofs).catch(() => {})
    }, 3000)
    return () => clearInterval(timer)
  }, [anyInProgress])

  // escape closes whichever popup is open
  useEffect(() => {
    if (!failLog && !adding && !renaming) return
    function onKey(e: KeyboardEvent) {
      if (e.key === 'Escape') {
        setFailLog(null)
        setAdding(false)
        setRenaming(null)
      }
    }
    window.addEventListener('keydown', onKey)
    return () => window.removeEventListener('keydown', onKey)
  }, [failLog, adding, renaming])

  // show a proof's graph, updating the url so back works
  function openProof(id: number | null) {
    window.history.pushState({}, '', id != null ? `/proof/${id}` : '/')
    setSelected(id)
  }

  // check/uncheck one row. copy the set so react sees a new object and re-renders
  function toggleChecked(id: number) {
    setCheckedIds((prev) => {
      const next = new Set(prev)
      if (next.has(id)) next.delete(id)
      else next.add(id)
      return next
    })
  }

  // open the rename popup with the current name pre-filled
  function openRename(proof: Proof) {
    setRenameValue(proof.name)
    setRenaming(proof)
  }

  // download the .lean source: make a temporary link, point it at the file endpoint, click it
  function downloadFile(proof: Proof) {
    const link = document.createElement('a')
    link.href = `/proofs/${proof.id}/file`
    link.download = `${proof.name}.lean`
    link.click()
  }

  // save the new name, then reload the list so the table shows it
  async function submitRename() {
    const name = renameValue.trim()
    if (!renaming || !name) return
    try {
      await renameProof(renaming.id, name)
      setProofs(await fetchProofs())
      setRenaming(null)
      setError(null)
    } catch (err) {
      setError(String(err))
    }
  }

  // delete every checked proof in parallel, then reload the list and clear the selection
  async function deleteChecked() {
    const ids = [...checkedIds]
    if (ids.length === 0) return
    try {
      await Promise.all(ids.map((id) => deleteProof(id)))
      setProofs(await fetchProofs())
      setCheckedIds(new Set())
      setError(null)
    } catch (err) {
      setError(String(err))
    }
  }

  // read the chosen .lean file, send it to compile, then reload the list (it shows up as queued)
  async function submitProof() {
    if (!file) return
    try {
      const contents = await file.text()
      const name = file.name.replace(/\.lean$/, '')
      await compileProof(name, contents, version)
      setProofs(await fetchProofs())
      setError(null)
      setAdding(false)
      setFile(null)
    } catch (err) {
      setError(String(err))
    }
  }

  // click a header: same column flips direction, a new column sorts ascending
  function sortBy(key: keyof Proof) {
    if (key === sortKey) setSortDir((dir) => (dir === 1 ? -1 : 1))
    else {
      setSortKey(key)
      setSortDir(1)
    }
  }

  // the four props each sortable header needs: styling, click to sort, and the two hover handlers
  function thProps(key: keyof Proof) {
    return {
      className: hovered === key ? 'sortable on' : 'sortable',
      onClick: () => sortBy(key),
      onMouseEnter: () => setHovered(key),
      onMouseLeave: () => setHovered(null),
    }
  }

  // the rows in display order. copies first since sort mutates, and sorts dates by the full timestamp
  const sorted = [...proofs].sort((a, b) => {
    const key = sortKey === 'added' ? 'created_at' : sortKey
    const first = a[key]
    const second = b[key]
    const order =
      typeof first === 'number' && typeof second === 'number'
        ? first - second
        : String(first).localeCompare(String(second))
    return order * sortDir
  })

  // header checkbox boolean: true only when there's at least one proof and all are checked
  const allChecked = proofs.length > 0 && proofs.every((proof) => checkedIds.has(proof.id))

  // header checkbox: clear everything, or select every proof
  function toggleAll() {
    setCheckedIds(allChecked ? new Set() : new Set(proofs.map((proof) => proof.id)))
  }

  // the checkbox cell that starts every row.
  // stopPropagation keeps its clicks from reaching the row, which would open the proof
  function checkCell(proof: Proof) {
    return (
      <td className="check-cell" onClick={(e) => e.stopPropagation()}>
        <input type="checkbox" checked={checkedIds.has(proof.id)} onChange={() => toggleChecked(proof.id)} />
      </td>
    )
  }

  // the gear cell that ends every row, opens the rename/download popup.
  // stopPropagation keeps its clicks from reaching the row, which would open the proof
  function gearCell(proof: Proof) {
    return (
      <td className="gear-cell" onClick={(e) => e.stopPropagation()}>
        <button className="gear-btn" onClick={() => openRename(proof)}>
          <GearIcon />
        </button>
      </td>
    )
  }

  // if a proof is selected, show its graph instead of the table
  if (selected != null) {
    const proof = proofs.find((row) => row.id === selected)
    return <GraphView id={selected} name={proof?.name ?? ''} onBack={() => openProof(null)} />
  }

  return (
    <main>
      {/* page header: title, delete button, add proof button */}
      <header>
        <h1>proofbase.</h1>
        <div className="header-actions">
          {/* the trash button only appears once rows are checked */}
          {checkedIds.size > 0 && (
            <button className="add trash-btn" onClick={deleteChecked} title="Delete selected">
              <TrashIcon />
              {checkedIds.size}
            </button>
          )}
          <button className="add" onClick={() => { setError(null); setAdding(true) }}>+ Add proof</button>
        </div>
      </header>

      {error && <p className="error">{error}</p>}

      {/* the proof table */}
      <table>
        {/* column widths: checkbox, the left columns, the 5 axiom columns, gear */}
        <colgroup>
          <col className="check-col" />
          {LEFT_COLUMNS.map((header) => (
            <col key={header.key} className={header.key === 'name' ? 'name-col' : 'data-col'} />
          ))}
          {AXIOM_COLUMNS.map((axiom) => (
            <col key={axiom.key} className="axiom-col" />
          ))}
          <col className="gear-col" />
        </colgroup>
        <thead>
          {/* first header row. rowSpan=2 lets the checkbox and the empty gear header fill both rows */}
          <tr>
            <th rowSpan={2} className="check-th">
              <input type="checkbox" checked={allChecked} onChange={toggleAll} />
            </th>
            {LEFT_COLUMNS.map((header) => (
              <th key={header.key} {...thProps(header.key)}>{header.top}</th>
            ))}
            <th className="band divider" colSpan={5}>nonstandard axiom usage</th>
            <th rowSpan={2} className="gear-th" />
          </tr>
          {/* second header row: the bottom text of each left header, then the axiom headers */}
          <tr>
            {LEFT_COLUMNS.map((header) => (
              <th key={header.key} {...thProps(header.key)}>{header.bottom}</th>
            ))}
            {AXIOM_COLUMNS.map((axiom, i) => {
              const props = thProps(axiom.key)
              return (
                <th key={axiom.key} {...props} className={i === 0 ? `${props.className} divider` : props.className}>
                  {axiom.label}
                </th>
              )
            })}
          </tr>
        </thead>
        <tbody>
          {/* one row per proof. status row until it's ready, then the full stats row */}
          {sorted.map((proof) => {
            const inProgress = proof.status === 'compiling' || proof.status === 'queued'
            const failed = proof.status === 'failed'

            // not ready. one wide message cell instead of the stat columns
            if (inProgress || failed) {
              return (
                <tr
                  key={proof.id}
                  className={failed ? 'status-row failed' : 'status-row'}
                  onClick={failed ? () => setFailLog(proof) : undefined}
                >
                  {checkCell(proof)}
                  <td className="name-cell">{proof.name}</td>
                  <td>{proof.added}</td>
                  <td>{leanVersion(proof.lean_version)}</td>
                  <td colSpan={COLUMNS.length - 2}>
                    {failed && 'compile failed (click to view log)'}
                    {proof.status === 'queued' && 'queued'}
                    {proof.status === 'compiling' && (
                      <>
                        <span className="spinner" /> compiling…
                      </>
                    )}
                  </td>
                  {gearCell(proof)}
                </tr>
              )
            }

            // ready. one cell per column. cells are colored by severity
            return (
              <tr key={proof.id} onClick={() => openProof(proof.id)}>
                {checkCell(proof)}
                <td className="name-cell">{proof.name}</td>
                {COLUMNS.map((column) => {
                  const color = severityClass(column, proof)
                  const divider = column === AXIOM_COLUMNS[0].key ? 'divider' : ''
                  return (
                    <td key={column} className={`${color} ${divider}`.trim()}>
                      {column === 'lean_version' ? leanVersion(proof.lean_version) : proof[column]}
                    </td>
                  )
                })}
                {gearCell(proof)}
              </tr>
            )
          })}
        </tbody>
      </table>

      {/* add proof popup */}
      {adding && (
        <Modal onClose={() => setAdding(false)}>
          <h2>Add a proof</h2>
          <label className="field">
            <span>Lean version</span>
            <select value={version} onChange={(e) => setVersion(e.target.value)}>
              {versions.map((toolchain) => (
                <option key={toolchain} value={toolchain}>{toolchain}</option>
              ))}
            </select>
          </label>
          <label className="field">
            <span>Proof file (.lean)</span>
            <input type="file" accept=".lean" onChange={(e) => setFile(e.target.files?.[0] ?? null)} />
          </label>
          {error && <p className="error">{error}</p>}
          <button className="add compile-btn" disabled={!file} onClick={submitProof}>Compile</button>
        </Modal>
      )}

      {/* compiler failure popup */}
      {failLog && (
        <Modal onClose={() => setFailLog(null)}>
          <h2 className="fail-title">{failLog.name}: compile failed</h2>
          <pre className="compile-log">{failLog.error}</pre>
        </Modal>
      )}

      {/* proof options popup */}
      {renaming && (
        <Modal onClose={() => setRenaming(null)}>
          <h2>Proof options</h2>
          <label className="field">
            <span>Name</span>
            <input
              type="text"
              value={renameValue}
              autoFocus
              onChange={(e) => setRenameValue(e.target.value)}
              onKeyDown={(e) => { if (e.key === 'Enter') submitRename() }}
            />
          </label>
          <div className="modal-actions">
            <button className="add" disabled={!renameValue.trim()} onClick={submitRename}>Save name</button>
            <button className="add" onClick={() => downloadFile(renaming)}>Download .lean</button>
          </div>
        </Modal>
      )}
    </main>
  )
}

export default App
