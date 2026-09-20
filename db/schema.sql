DROP TABLE IF EXISTS edge, axiom_dependency, axiom_policy, declaration, proof CASCADE;

-- one row per proof
CREATE TABLE proof (
    id bigserial PRIMARY KEY,
    name text NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now(),
    lean_version text,
    declarations integer NOT NULL DEFAULT 0,
    roots integer NOT NULL DEFAULT 0,
    edges integer NOT NULL DEFAULT 0,
    flagged integer NOT NULL DEFAULT 0,
    sorry integer NOT NULL DEFAULT 0,
    trust integer NOT NULL DEFAULT 0,
    unsafe integer NOT NULL DEFAULT 0,
    custom integer NOT NULL DEFAULT 0,
    graph_svg text,
    status text NOT NULL DEFAULT 'ready',
    error text,
    file text
);

-- each theorem, def, axiom in a proof
CREATE TABLE declaration (
    id bigserial PRIMARY KEY,
    proof_id bigint NOT NULL REFERENCES proof(id) ON DELETE CASCADE,
    name text NOT NULL,
    kind text NOT NULL,
    is_generated boolean NOT NULL DEFAULT false,
    is_instance boolean NOT NULL DEFAULT false,
    is_simp boolean NOT NULL DEFAULT false,
    line_start integer,
    line_end integer,
    UNIQUE (proof_id, name)
);

-- which axioms each declaration ends up relying on
CREATE TABLE axiom_dependency (
    declaration_id bigint NOT NULL REFERENCES declaration(id) ON DELETE CASCADE,
    axiom_id bigint NOT NULL REFERENCES declaration(id) ON DELETE CASCADE,
    PRIMARY KEY (declaration_id, axiom_id)
);

-- axioms grouped by how risky they are (standard, sorry, trust, unsafe)
CREATE TABLE axiom_policy (
    name text PRIMARY KEY,
    kind text NOT NULL
);

-- known axioms, anything not here is 'custom'
INSERT INTO axiom_policy (name, kind) VALUES
    ('propext', 'standard'),
    ('Classical.choice', 'standard'),
    ('Quot.sound', 'standard'),
    ('sorryAx', 'sorry'),
    ('Lean.ofReduceBool', 'trust'),
    ('Lean.ofReduceNat', 'trust'),
    ('Lean.trustCompiler', 'trust'),
    ('lcProof', 'unsafe'),
    ('lcCast', 'unsafe'),
    ('lcErased', 'unsafe'),
    ('lcUnreachable', 'unsafe'),
    ('lcAny', 'unsafe'),
    ('lcVoid', 'unsafe'),
    ('lcRealWorld', 'unsafe'),
    ('isScalarObj', 'unsafe'),
    ('Quot.lcInv', 'unsafe');

-- edges between declarations. arrows point from a declaration to its dependencies
-- what does X depend on: WHERE from_id = X
-- what depends on X: WHERE to_id = X
CREATE TABLE edge (
    proof_id bigint NOT NULL REFERENCES proof(id) ON DELETE CASCADE,
    from_id bigint NOT NULL REFERENCES declaration(id) ON DELETE CASCADE,
    to_id bigint NOT NULL REFERENCES declaration(id) ON DELETE CASCADE,
    PRIMARY KEY (from_id, to_id),
    CHECK (from_id <> to_id) -- no self loops
);

-- the above primary key covers from_id lookups. this index makes the reverse (to_id) fast too
CREATE INDEX ON edge (to_id);
-- re-ingesting a proof deletes its edges by proof_id alone, which neither of the above can serve
CREATE INDEX ON edge (proof_id);

-- classifies every axiom each declaration uses by how risky it is
-- "this declaration uses this specific axiom, whose risk is X"
CREATE VIEW axiom_use AS
SELECT d.proof_id,
       d.id AS declaration_id,
       d.name AS declaration,
       ax.name AS axiom,
       CASE
           WHEN pol.kind IS NOT NULL THEN pol.kind -- use the axiom_policy kind
           WHEN ax.name LIKE '%.\_native.%' ESCAPE '\' THEN 'trust' -- if axiom name has this pattern, it's a trust axiom
           ELSE 'custom'
       END AS kind
FROM declaration d
JOIN axiom_dependency ad ON ad.declaration_id = d.id
JOIN declaration ax ON ax.id = ad.axiom_id
LEFT JOIN axiom_policy pol ON pol.name = ax.name;

-- declarations to include in the graph view
CREATE VIEW graph_declaration AS
-- columns are listed rather than SELECT *: a view freezes its column list at creation, so
-- `SELECT *` silently hides any column added to declaration later
SELECT d.id, d.proof_id, d.name, d.kind, d.is_generated, d.is_instance, d.is_simp,
       d.line_start, d.line_end
FROM declaration d
WHERE NOT d.is_generated -- extract.lean decides this
  AND d.kind IN ('theorem', 'axiom') -- no defs
  AND d.name NOT IN (SELECT name FROM axiom_policy); -- skip known axioms

-- edges to draw. a dependency can pass through a declaration that graph_declaration hides, so step over those to the next visible one
-- ex: A -> foo._proof_6 -> B becomes A -> B
-- a function rather than a view: postgres cannot push a proof_id filter into a recursive term,
-- so a view walks every proof in the table and throws away all but one
CREATE FUNCTION graph_edges(pid bigint)
RETURNS TABLE (proof_id bigint, from_id bigint, to_id bigint) AS $$
WITH RECURSIVE visible AS (
    SELECT d.id, d.kind FROM graph_declaration d WHERE d.proof_id = pid
), step (from_id, to_id) AS (
        SELECT e.from_id, e.to_id
        FROM edge e
        JOIN visible f ON f.id = e.from_id
        WHERE e.proof_id = pid AND f.kind <> 'axiom' -- axioms depend on nothing
    UNION -- not UNION ALL, so a cycle can't loop forever
        SELECT s.from_id, e.to_id
        FROM step s
        JOIN edge e ON e.from_id = s.to_id AND e.proof_id = pid
        WHERE NOT EXISTS (SELECT 1 FROM visible g WHERE g.id = s.to_id) -- only step over hidden ones
)
SELECT DISTINCT pid, from_id, to_id
FROM step
WHERE EXISTS (SELECT 1 FROM visible g WHERE g.id = to_id) -- has to land on a visible one
  AND from_id <> to_id; -- stepping over can lead back to the source
$$ LANGUAGE sql STABLE; -- stepping over can lead back to the source
