// shape of a proof as returned by GET /proofs
export type Proof = {
  id: number
  name: string
  lean_version: string
  added: string
  created_at: string
  declarations: number
  roots: number
  edges: number
  flagged: number
  sorry: number
  trust: number
  unsafe: number
  custom: number
  status: string
  error: string | null
}

// shape of what GET /declarations/:id returns
export type Declaration = {
  id: number
  name: string
  kind: string
  line_start: number | null
  line_end: number | null
  axioms: { name: string; kind: string; severity: number }[]
  dependencies: { id: number; name: string; severity: number }[]
  dependents: { id: number; name: string; severity: number }[]
}

// GET /proofs -> the list of proofs for the table
export async function fetchProofs(): Promise<Proof[]> {
  const res = await fetch('/proofs')
  if (!res.ok) throw new Error(`GET /proofs failed: ${res.status}`)
  const body = await res.json()
  return body.proofs
}

// GET /versions -> lean versions for the upload dropdown (newest first)
export async function fetchVersions(): Promise<string[]> {
  const res = await fetch('/versions')
  if (!res.ok) throw new Error(`GET /versions failed: ${res.status}`)
  const body = await res.json()
  return body.versions
}

// POST /compile -> upload a proof. shows the backend's error message on failure
export async function compileProof(name: string, file: string, version: string): Promise<void> {
  const res = await fetch('/compile', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name, file, version }),
  })
  if (!res.ok) {
    const body = await res.json().catch(() => null)
    throw new Error(body?.error ?? `compile request failed: ${res.status}`)
  }
}

// DELETE /proofs/:id -> remove a proof
export async function deleteProof(id: number): Promise<void> {
  const res = await fetch(`/proofs/${id}`, { method: 'DELETE' })
  if (!res.ok) throw new Error(`DELETE proof failed: ${res.status}`)
}

// PATCH /proofs/:id -> change a proof's name
export async function renameProof(id: number, name: string): Promise<void> {
  const res = await fetch(`/proofs/${id}`, {
    method: 'PATCH',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ name }),
  })
  if (!res.ok) throw new Error(`rename failed: ${res.status}`)
}

// GET /proofs/:id/graph -> the rendered svg as text
export async function fetchProofSvg(id: number): Promise<string | null> {
  const res = await fetch(`/proofs/${id}/graph`)
  if (res.status === 404) return null
  if (!res.ok) throw new Error(`GET graph failed: ${res.status}`)
  return res.text()
}

// GET /proofs/:id/file -> the raw .lean source as text
export async function fetchProofSource(id: number): Promise<string | null> {
  const res = await fetch(`/proofs/${id}/file`)
  if (res.status === 404) return null
  if (!res.ok) throw new Error(`GET file failed: ${res.status}`)
  return res.text()
}

// GET /declarations/:id -> one declaration with its axioms and neighbors
export async function fetchDeclaration(id: number): Promise<Declaration> {
  const res = await fetch(`/declarations/${id}`)
  if (!res.ok) throw new Error(`GET declaration failed: ${res.status}`)
  return res.json()
}
