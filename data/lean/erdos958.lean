/-

This is a Lean formalization of a solution to Erdős Problem 958.
https://www.erdosproblems.com/958

This proof was written by Aristotle.  It found the proof given only
the formal statement.

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

set_option linter.style.longLine false
set_option linter.style.refine false

namespace Erdos958

/-- The Euclidean plane `ℝ²`. -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/-- Distance of an unordered pair `{p,q}` (modeled as `Sym2 Point`). -/
noncomputable def pairDist : Sym2 Point → ℝ :=
  Sym2.lift ⟨(fun p q : Point => dist p q), (fun p q => dist_comm p q)⟩

/-- Distance between two explicit points in `ℝ²`. -/
lemma dist_euclidean_two (a b c d : ℝ) :
    dist (!₂[a, b] : Point) (!₂[c, d]) = Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Real.dist_eq, sq_abs]

/-- Two explicit points in `ℝ²` are equal iff their coordinates agree. -/
lemma pt_eq_iff (a b c d : ℝ) : (!₂[a, b] : Point) = !₂[c, d] ↔ a = c ∧ b = d := by
  rw [WithLp.ext_iff, WithLp.ofLp_toLp, WithLp.ofLp_toLp, funext_iff, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Unordered pairs of **distinct** points from `A` (diagonal `{p,p}` removed). -/
noncomputable def unorderedPairs (A : Finset Point) : Finset (Sym2 Point) :=
  (A.sym2).filter (fun z => ¬ z.IsDiag)

/-- The finset of distances determined by `A`, using unordered pairs of distinct points. -/
noncomputable def distances (A : Finset Point) : Finset ℝ :=
  (unorderedPairs A).image pairDist

/-- Multiplicity of a distance `d`: number of unordered **distinct** pairs `{p,q}` in `A`
with `dist p q = d`.

Named differently to avoid clashing with existing `multiplicity` in mathlib. -/
noncomputable def distMultiplicity (A : Finset Point) (d : ℝ) : ℕ :=
  ((unorderedPairs A).filter (fun z => pairDist z = d)).card

/-- Equally spaced points on a line: an affine arithmetic progression `p₀ + i • v`. -/
def EquallySpacedOnLine (A : Finset Point) : Prop :=
  ∃ p₀ v : Point,
    v ≠ 0 ∧
      A = (Finset.range A.card).image (fun i : ℕ => p₀ + (i : ℝ) • v)

/-- The unit-circle parametrization `θ ↦ (cos θ, sin θ)` as a `Point`. -/
noncomputable def unitCircle (θ : ℝ) : Point :=
  !₂[Real.cos θ, Real.sin θ]

/-- The unit-circle parametrization has unit norm. -/
lemma norm_unitCircle (θ : ℝ) : ‖unitCircle θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  unfold unitCircle
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Real.norm_eq_abs, sq_abs, Real.cos_sq_add_sin_sq, Real.sqrt_one]

/--
Equally spaced points on a circle **with constant angular step**:

There exist a center `c`, radius `r > 0`, starting angle `θ₀`, and step `Δθ`
such that `A` is exactly the image of `i ↦ c + r • unitCircle (θ₀ + i * Δθ)`
for `i = 0,1,...,n-1` where `n = A.card`.

This is the “arithmetic progression in the angle” version (not necessarily a full regular `n`-gon).
-/
def EquallySpacedOnCircle (A : Finset Point) : Prop :=
  ∃ c : Point, ∃ r θ₀ Δθ : ℝ,
    0 < r ∧
      A =
        (Finset.range A.card).image (fun i : ℕ =>
          c + r • unitCircle (θ₀ + (i : ℝ) * Δθ))

/-- The profile condition from the prompt:
* `k = n - 1`, where `k` is the number of distinct distances, and
* `{ f(d) | d ∈ D } = {1,2,...,n-1}` as finsets. -/
def HasProfile (A : Finset Point) : Prop :=
  let n := A.card
  let D := distances A
  D.card = n - 1 ∧ D.image (distMultiplicity A) = Finset.Icc 1 (n - 1)

/-
The counterexample set {(0,0), (1,0), (0,1), (0,-1)}.
-/
noncomputable def counterexample_set : Finset Point :=
  let p0 : Point := !₂[0, 0]
  let p1 : Point := !₂[1, 0]
  let p2 : Point := !₂[0, 1]
  let p3 : Point := !₂[0, -1]
  {p0, p1, p2, p3}

/-
The counterexample set satisfies the profile condition.
-/
lemma counterexample_has_profile : HasProfile counterexample_set := by
  unfold HasProfile;
  -- Let's calculate the set of distances and their multiplicities.
  have h_dist : distances counterexample_set = {1, Real.sqrt 2, 2} := by
    unfold distances counterexample_set;
    -- Let's calculate the distances between the points in the counterexample set.
    ext d
    simp [pairDist, unorderedPairs];
    constructor <;> intro h;
    · rcases h with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; rcases a with ⟨ p, q ⟩ ; simp_all +decide [ EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons ];
      rcases ha₁ with ⟨ rfl | rfl | rfl | rfl, rfl | rfl | rfl | rfl ⟩ <;> norm_num [ Real.sqrt_eq_iff_mul_self_eq_of_pos ];
      · contradiction;
      · contradiction;
      · contradiction;
      · contradiction;
    · rcases h with ( rfl | rfl | rfl );
      · refine' ⟨ Sym2.mk (!₂[0, 0] : Point) (!₂[1, 0] : Point), _, _ ⟩ <;> norm_num [ EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons ];
      · refine' ⟨ Sym2.mk (!₂[0, 1] : Point) (!₂[1, 0] : Point), _, _ ⟩ <;> norm_num [ EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons ];
      · refine' ⟨ Sym2.mk (!₂[0, 1] : Point) (!₂[0, -1] : Point), _, _ ⟩ <;> norm_num [ EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons ];
  -- Let's calculate the multiplicities of the distances.
  have h_mult : distMultiplicity counterexample_set 1 = 3 ∧ distMultiplicity counterexample_set (Real.sqrt 2) = 2 ∧ distMultiplicity counterexample_set 2 = 1 := by
    unfold distMultiplicity;
    erw [ show unorderedPairs counterexample_set = { Sym2.mk (!₂[0, 0] : Point) (!₂[1, 0] : Point), Sym2.mk (!₂[0, 0] : Point) (!₂[0, 1] : Point), Sym2.mk (!₂[0, 0] : Point) (!₂[0, -1] : Point), Sym2.mk (!₂[1, 0] : Point) (!₂[0, 1] : Point), Sym2.mk (!₂[1, 0] : Point) (!₂[0, -1] : Point), Sym2.mk (!₂[0, 1] : Point) (!₂[0, -1] : Point) } from ?_ ];
    · unfold pairDist
      have s2a : Real.sqrt 2 ≠ 1 := by
        intro h; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      have s2b : Real.sqrt 2 ≠ 2 := by
        intro h; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      have s4 : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      refine ⟨?_, ?_, ?_⟩ <;>
        norm_num [Finset.filter_insert, Finset.filter_singleton, Sym2.lift_mk,
          EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.toLp_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, WithLp.ofLp_toLp,
          Real.sqrt_one, s4, s2a, s2b, s2a.symm, s2b.symm,
          Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton,
          Finset.card_singleton, pt_eq_iff, Sym2.mk_eq_mk_iff, Prod.mk.injEq, Prod.swap_prod_mk]
    · unfold counterexample_set unorderedPairs; simp +decide [ Finset.ext_iff ] ;
      intro a; constructor <;> intro ha <;> rcases a with ⟨ x, y ⟩ <;> simp_all +decide [ Sym2.eq_swap ] ;
      · grind;
      · rcases ha with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> norm_num [ ← List.ofFn_inj ];
        all_goals intro h; have := congr_fun h 0; norm_num at this;
        all_goals have := congr_fun h 1; norm_num at this;
  -- Let's calculate the cardinality of the set of distances.
  have h_card : (distances counterexample_set).card = 3 := by
    rw [ h_dist, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
  simp_all +decide [ Finset.ext_iff ];
  have hcard : counterexample_set.card = 4 := by
    unfold counterexample_set
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton] <;>
      norm_num [pt_eq_iff, Finset.mem_insert, Finset.mem_singleton]
  rw [hcard]
  refine ⟨by norm_num, fun a => ?_⟩
  omega

/-
The counterexample set is not equally spaced on a line.
-/
lemma counterexample_not_line : ¬ EquallySpacedOnLine counterexample_set := by
  rintro ⟨ p₀, v, hv, h ⟩;
  -- By definition of `counterexample_set`, we know that `(0,0)`, `(1,0)`, `(0,1)`, and `(0,-1)` are in `counterexample_set`.
  have h_points : (!₂[0, 0] : Point) ∈ counterexample_set ∧ (!₂[1, 0] : Point) ∈ counterexample_set ∧ (!₂[0, 1] : Point) ∈ counterexample_set ∧ (!₂[0, -1] : Point) ∈ counterexample_set := by
    exact ⟨ Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ), Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ), Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_singleton_self _ ) ) ) ⟩;
  simp_all +decide [ Finset.ext_iff ];
  obtain ⟨ ⟨ a, ha, ha' ⟩, ⟨ b, hb, hb' ⟩, ⟨ c, hc, hc' ⟩, ⟨ d, hd, hd' ⟩ ⟩ := h_points;
  simp only [WithLp.ext_iff, funext_iff, Fin.forall_fin_two, WithLp.ofLp_add, WithLp.ofLp_smul,
    WithLp.ofLp_zero, WithLp.ofLp_toLp, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at ha' hb' hc' hd'
  obtain ⟨ha0, ha1⟩ := ha'
  obtain ⟨hb0, hb1⟩ := hb'
  obtain ⟨hc0, hc1⟩ := hc'
  obtain ⟨hd0, hd1⟩ := hd'
  have e1 : ((b : ℝ) - a) * v.ofLp 0 = 1 := by linear_combination hb0 - ha0
  have e2 : ((c : ℝ) - a) * v.ofLp 0 = 0 := by linear_combination hc0 - ha0
  have e3 : ((b : ℝ) - a) * v.ofLp 1 = 0 := by linear_combination hb1 - ha1
  have e4 : ((c : ℝ) - a) * v.ofLp 1 = 1 := by linear_combination hc1 - ha1
  have contra : ((b : ℝ) - a) * v.ofLp 0 * (((c : ℝ) - a) * v.ofLp 1)
      = ((c : ℝ) - a) * v.ofLp 0 * (((b : ℝ) - a) * v.ofLp 1) := by ring
  rw [e1, e2, e3, e4] at contra
  norm_num at contra

/-
The counterexample set is not equally spaced on a circle.
-/
lemma counterexample_not_circle : ¬ EquallySpacedOnCircle counterexample_set := by
  rintro ⟨ c, r, θ₀, Δθ, hr, ha ⟩;
  -- From the equality of sets, we know that the points (0,0), (1,0), (0,1), and (0,-1) must lie on the circle with center `c` and radius `r`.
  have h_points_on_circle : ∀ p ∈ (({(!₂[0, 0] : Point), (!₂[1, 0] : Point), (!₂[0, 1] : Point), (!₂[0, -1] : Point)}) : Finset Point), dist p c = r := by
    intro p hp
    have h_eq : p ∈ Finset.image (fun i : ℕ => c + r • unitCircle (θ₀ + (i : ℝ) * Δθ)) (Finset.range counterexample_set.card) := by
      exact ha ▸ by simpa [ counterexample_set ] using hp;
    rw [ Finset.mem_image ] at h_eq; obtain ⟨ i, hi, rfl ⟩ := h_eq
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_unitCircle, mul_one,
      Real.norm_eq_abs, abs_of_pos hr]
  norm_num [ EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons ] at h_points_on_circle;
  norm_num [ Real.sqrt_eq_iff_mul_self_eq_of_pos hr ] at h_points_on_circle ; nlinarith


/-- **Erdős Problem 958** (Erdős conjectured "no"; proved by Clemen–Dumitrescu–Liu 2025).
It is **not** the case that for every finite set `A ⊂ ℝ²` with distance profile
`(k = n - 1, {f(d_i)} = {n - 1, …, 1})`, `A` must be equally spaced on a line
or on a circle. Counterexample: equally spaced points on a short circular arc
together with the centre. -/
theorem erdos_958 : ¬ ∀ A : Finset Point,
    HasProfile A ↔ (EquallySpacedOnLine A ∨ EquallySpacedOnCircle A) := by
  have h_not_line : ¬ EquallySpacedOnLine counterexample_set := by
    exact counterexample_not_line
  have h_not_circle : ¬ EquallySpacedOnCircle counterexample_set := by
    exact counterexample_not_circle
  have h_has_profile : HasProfile counterexample_set := by
    exact counterexample_has_profile
  exact fun h => by have := h counterexample_set; aesop;

#print axioms erdos_958
-- 'Erdos958.erdos_958' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos958
