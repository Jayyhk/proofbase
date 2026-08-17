/-

This is a Lean formalization of a solution to Erdős Problem 418.
https://www.erdosproblems.com/418

The original human proof was found by Browkin and Schinzel:
[BrSc95] Browkin, J. and Schinzel, A., _On integers not of the form {$n-\phi(n)$}_.
Colloq. Math. (1995), 55-58.

Their proof was explained by ChatGPT 5.1 Pro from OpenAI.

The LaTeX file output from the previous step was auto-formalized into
Lean by Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind, with this statement originally written
by Salvatore Mercuri.

The proof is verified by Lean.  The original used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

Ported to leanprover/lean4:v4.33.0.  Five changes were needed:

  * ZMod.eq_iff_modEq_nat is now ZMod.natCast_eq_natCast_iff
  * Finset.prod_eq_mul_prod_diff_singleton is now
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
  * `bound` no longer leaves goals in phi_mod_4_eq_2_iff_of_even, so the
    substitute/split/intro steps it used to do are written out
  * `convert ... using 1` in n_le_four_m now tries to congruence the LE
    instance as well, so the totient side is rewritten directly instead
  * chunksOK_correct needs a larger maxRecDepth

Note also that v4.24.0 discharged `native_decide` with the global
Lean.ofReduceBool and Lean.trustCompiler axioms.  As of v4.33.0 it emits one
axiom per computation instead (RFC 12216), which is the `._native.` name below.

-/

import Mathlib

set_option linter.style.cdot false
set_option linter.style.commandStart false
set_option linter.style.induction false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000 -- chunksOK_correct recurses 510 deep

namespace Erdos418


def IsCototient (m : ℕ) : Prop := ∃ n, m = n - n.totient

def IsNoncototient (m : ℕ) : Prop := ¬ IsCototient m

def m_BS : ℕ := 509203

def Composite (n : ℕ) : Prop := ∃ a b, 1 < a ∧ 1 < b ∧ n = a * b

theorem riesel_number (k : ℕ) (hk : 1 ≤ k) : Composite (2^k * m_BS - 1) := by
  -- By definition of $m_BS$, we know that $2^k * m_BS - 1$ is divisible by at least one prime from the set {3, 5, 7, 13, 17, 241}.
  have h_div : ∃ p ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), p ∣ (2^k * m_BS - 1) := by
    -- For each prime q in the set {3, 5, 7, 13, 17, 241}, we find an integer a such that 509203 ≡ 2^a (mod q).
    have h_cong : ∀ k ≥ 1, (∃ q ∈ ({3, 5, 7, 13, 17, 241} : Finset ℕ), 2 ^ k * m_BS ≡ 1 [MOD q]) := by
      aesop;
      rw [ ← Nat.mod_add_div k_1 24 ] ; norm_num [ Nat.ModEq, Nat.mul_mod, Nat.pow_add, Nat.pow_mul, Nat.pow_mod ] ; have := Nat.mod_lt k_1 ( by decide : 0 < 24 ) ; interval_cases k_1 % 24 <;> (unfold m_BS; decide);
    obtain ⟨ q, hq₁, hq₂ ⟩ := h_cong k hk; use q; erw [ ← Nat.modEq_zero_iff_dvd ] ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub ( show 0 < 2 ^ k * m_BS from mul_pos ( pow_pos ( by decide ) _ ) ( by decide ) ) ] ;
  -- Since $p$ is a prime and $p \leq 241$, it follows that $2^k * m_BS - 1$ is composite.
  obtain ⟨p, hp_prime, hp_div⟩ := h_div
  have h_gt : 1 < 2^k * m_BS - 1 := by
    exact lt_tsub_iff_left.mpr ( by nlinarith [ Nat.pow_le_pow_right two_pos hk, show m_BS > 1 from by decide ] );
  -- Since $p$ divides $2^k * m_BS - 1$ and $2^k * m_BS - 1 > p$, it follows that $2^k * m_BS - 1$ is composite.
  have h_composite : p < 2^k * m_BS - 1 := by
    exact lt_of_le_of_lt ( Finset.mem_insert.mp hp_prime |> fun x => by aesop_cat ) ( show 241 < 2 ^ k * m_BS - 1 from lt_tsub_iff_left.mpr <| by nlinarith [ Nat.pow_le_pow_right ( show 1 ≤ 2 by decide ) hk, show m_BS > 241 by unfold m_BS; decide ] );
  exact ⟨ p, ( 2 ^ k * m_BS - 1 ) / p, by aesop, by nlinarith [ Nat.div_mul_cancel hp_div ], by rw [ Nat.mul_div_cancel' hp_div ] ⟩


lemma lemma_half_n (n : ℕ) (h : 4 ∣ n) : (n / 2).totient = n.totient / 2 := by
  rcases h with ⟨ k, rfl ⟩;
  -- Apply the property of the totient function for even numbers: φ(2n) = 2φ(n) if n is even.
  have h_totient_even : Nat.totient (2 * (2 * k)) = 2 * Nat.totient (2 * k) := by
    -- Since $2$ is prime and divides $2k$, we can apply the lemma Nat.totient_mul_of_prime_of_dvd.
    have h_prime_div : Nat.Prime 2 ∧ 2 ∣ 2 * k := by
      norm_num;
    rw [ Nat.totient_mul_of_prime_of_dvd ] <;> tauto;
  grind


lemma phi_mod_4_eq_2_iff_of_even (n : ℕ) (h_even : Even n) (h_gt : 4 < n) :
  n.totient % 4 = 2 ↔ ∃ p k, p.Prime ∧ p % 4 = 3 ∧ n = 2 * p^k := by
    -- Let's consider the prime factorization of $n$. Since $n$ is even, it must have at least one factor of $2$. Let's write $n$ as $2^a \cdot m$, where $m$ is odd.
    obtain ⟨a, m, ha, hm⟩ : ∃ a m, n = 2^a * m ∧ Odd m := by
      -- By definition of prime factorization, every integer can be expressed as $2^a \cdot m$ where $m$ is odd.
      use Nat.factorization n 2, n / 2^Nat.factorization n 2;
      exact ⟨ Eq.symm ( Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ), Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h₃ => absurd ( Nat.dvd_of_mod_eq_zero h₃ ) ( Nat.not_dvd_ordCompl ( by norm_num ) ( by linarith ) ) ) ⟩;
    subst ha
    have fwd : 4 ≤ 2 ^ a * m := le_of_lt h_gt
    constructor
    · intro a_1
      rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.totient_mul, Nat.totient_prime_pow ];
      · -- Since $m$ is both even and odd, this is a contradiction.
        exfalso; exact absurd h_even (by simpa using hm);
      · -- Since $m$ is odd and its totient is $2 \mod 4$, $m$ must have exactly one prime factor $p$.
        obtain ⟨p, k, hp, hk⟩ : ∃ p k : ℕ, Nat.Prime p ∧ m = p^k := by
          -- If $m$ has more than one prime factor, then $\phi(m)$ would be divisible by 4, contradicting $\phi(m) \equiv 2 \pmod{4}$.
          by_contra h_contra
          have h_div4 : 4 ∣ Nat.totient m := by
            -- If $m$ has more than one prime factor, then $\phi(m)$ would be divisible by 4, contradicting $\phi(m) \equiv 2 \pmod{4}$. Hence, $m$ must have exactly one prime factor.
            have h_prime_factors : (Nat.primeFactors m).card ≥ 2 := by
              by_cases h_prime_factors : (Nat.primeFactors m).card = 1;
              · rw [ Finset.card_eq_one ] at h_prime_factors ; aesop;
                exact h_contra w ( Nat.prime_of_mem_primeFactors ( h.symm ▸ Finset.mem_singleton_self _ ) ) ( Nat.factorization m w ) ( by nth_rw 1 [ ← Nat.factorization_prod_pow_eq_self hm.pos.ne' ] ; rw [ Finsupp.prod ] ; aesop );
              · exact Nat.lt_of_le_of_ne ( Finset.card_pos.mpr ⟨ Nat.minFac m, Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime ( by linarith ), Nat.minFac_dvd m, by linarith ⟩ ⟩ ) ( Ne.symm h_prime_factors );
            have h_div4 : ∀ p ∈ Nat.primeFactors m, 2 ∣ Nat.totient p := by
              intro p hp; rw [ Nat.totient_prime ( Nat.prime_of_mem_primeFactors hp ) ] ; aesop;
              exact even_iff_two_dvd.mp ( left.even_sub_one <| by rintro rfl; exact absurd ( hm.of_dvd_nat left_1 ) ( by norm_num ) );
            have h_div4 : 2 ^ (Nat.primeFactors m).card ∣ Nat.totient m := by
              rw [ Nat.totient_eq_prod_factorization ] <;> aesop;
              exact dvd_mul_of_dvd_right ( by simpa [ Finsupp.prod ] using Finset.prod_dvd_prod_of_dvd _ _ fun p hp => show 2 ∣ p - 1 from by simpa [ Nat.totient_prime ( Nat.prime_of_mem_primeFactors hp ) ] using h_div4 p ( Nat.prime_of_mem_primeFactors hp ) ( Nat.dvd_of_mem_primeFactors hp ) ( by aesop ) ) _;
            exact dvd_trans ( pow_dvd_pow _ h_prime_factors ) h_div4;
          omega;
        rcases k with ( _ | k ) <;> simp_all +decide [ Nat.totient_prime_pow ];
        rcases Nat.even_or_odd' p with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
        · exact absurd hm ( by norm_num [ Nat.even_pow ] );
        · rcases Nat.even_or_odd' c with ⟨ d, rfl | rfl ⟩ <;> ring_nf at * <;> norm_num [ Nat.add_mod, Nat.mul_mod ] at *;
          exact ⟨ 3 + d * 4, hp, by norm_num [ Nat.add_mod, Nat.mul_mod ], k + 1, by ring ⟩;
      · rcases a with ( _ | _ | a ) <;> norm_num [ Nat.pow_succ', ← mul_assoc, Nat.mul_mod ] at *;
        -- Since $m$ is odd and greater than 1, we have $\phi(m) \equiv 0 \pmod{2}$.
        have h_phi_m_even : 2 ∣ Nat.totient m := by
          exact even_iff_two_dvd.mp ( Nat.totient_even <| Nat.le_of_not_lt fun contra => by interval_cases m ; contradiction );
        grind;
    · rintro ⟨ w, w_1, left, left_1, right ⟩
      -- Since $m$ is odd and $2^a * m = 2 * w^{w_1}$, we must have $a = 1$.
      have ha_one : a = 1 := by
        rcases a with ( _ | _ | a ) <;> simp_all +decide [ Nat.pow_succ', mul_assoc ];
        · exact absurd hm ( by norm_num );
        · have := congr_arg ( · % 2 ) right; norm_num [ Nat.mul_mod, Nat.pow_mod, left.eq_two_or_odd.resolve_left ( by aesop_cat ) ] at this;
      simp_all +decide [ Nat.totient_mul, Nat.totient_prime_pow ];
      rw [ Nat.totient_prime_pow left ];
      · rw [ ← Nat.mod_add_div w 4, left_1 ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ;
        rcases Nat.even_or_odd' ( w_1 - 1 ) with ⟨ k, hk | hk ⟩ <;> norm_num [ Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hk ];
      · contrapose! h_gt; aesop


lemma m_BS_prime : m_BS.Prime := by
  unfold m_BS; norm_num

lemma m_BS_plus_one_not_power_of_two (k : ℕ) : 2^k ≠ m_BS + 1 := by
  intro h;
  exact absurd ( h.symm ▸ pow_dvd_pow _ ( show k ≥ 23 by contrapose! h; interval_cases k <;> (unfold m_BS; decide) ) ) ( by decide )

lemma composite_implies_not_prime {n : ℕ} (h : Composite n) : ¬ n.Prime := by
  obtain ⟨ a, b, ha, hb, rfl ⟩ := h; exact Nat.not_prime_mul ( by linarith ) ( by linarith ) ;


lemma inductive_step (k : ℕ) (hk : 2 ≤ k) (h_ind : IsNoncototient (2^(k-1) * m_BS)) : IsNoncototient (2^k * m_BS) := by
  -- Assume for contradiction that $2^k * m_BS$ is a cototient.
  by_contra h_contra
  obtain ⟨n, hn⟩ : ∃ n, 2^k * m_BS = n - n.totient := by
    -- By definition of noncototient, if 2^k * m_BS is not a noncototient, then it must be a cototient.
    unfold IsNoncototient at h_contra; aesop;
  -- Since $k \geq 2$, $2^k * m_BS$ is divisible by 4. So $n - \phi(n)$ is divisible by 4.
  have h_div4 : 4 ∣ n - n.totient := by
    exact hn ▸ dvd_mul_of_dvd_left ( pow_dvd_pow _ hk ) _;
  -- Consider two cases: when $\phi(n)$ is divisible by 4 and when it is not.
  by_cases h_phi_div4 : 4 ∣ n.totient;
  · -- By lemma_half_n, we have $\phi(n/2) = \phi(n)/2$.
    have h_phi_half : n.totient / 2 = (n / 2).totient := by
      rw [ ← lemma_half_n ];
      rw [ eq_tsub_iff_add_eq_of_le ] at hn;
      · exact hn ▸ dvd_add ( dvd_mul_of_dvd_left ( dvd_trans ( by decide ) ( pow_dvd_pow _ hk ) ) _ ) h_phi_div4;
      · exact Nat.totient_le n;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ pow_succ', mul_assoc ];
    exact h_ind ⟨ n / 2, by omega ⟩;
  · -- Since $\phi(n)$ is not divisible by 4 and $n > 4$, we have $\phi(n) = 2 \mod 4$. By the lemma, this implies $n = 2 * p^a$ where $p$ is a prime congruent to $3 \mod 4$.
    obtain ⟨p, a, hp_prime, hp_mod, hn_eq⟩ : ∃ p a, Nat.Prime p ∧ p % 4 = 3 ∧ n = 2 * p^a := by
      have h_phi_mod4 : n.totient % 4 = 2 := by
        -- Since $\phi(n)$ is even and not divisible by 4, we have $\phi(n) \equiv 2 \mod 4$.
        have h_phi_even : Even n.totient := by
          rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ Nat.totient_prime ];
          exact Nat.totient_even <| by linarith;
        rw [ Nat.even_iff ] at h_phi_even; omega;
      apply phi_mod_4_eq_2_iff_of_even n (by
      rw [ Nat.even_iff ] ; replace hn := congr_arg Even hn ; simp_all +decide [ Nat.even_sub ( show n.totient ≤ n from Nat.totient_le n ), parity_simps ] ;
      cases k <;> simp_all +decide [ Nat.even_iff ];
      omega) (by
      rcases n with ( _ | _ | _ | _ | _ | n ) <;> simp +arith +decide at *) |>.1 h_phi_mod4;
    -- Substitute $n = 2 * p^a$ into the equation $2^k * m_BS = n - n.totient$ and simplify.
    have h_eq : 2^k * m_BS = p^(a-1) * (p + 1) := by
      rcases a with ( _ | a ) <;> simp_all +decide [ Nat.totient_prime_pow ];
      rw [ Nat.totient_mul, Nat.totient_prime_pow ] <;> norm_num [ hp_prime ];
      · exact Nat.sub_eq_of_eq_add <| by cases p <;> norm_num [ pow_succ' ] at * ; linarith;
      · exact hp_prime.odd_of_ne_two <| by aesop_cat;
    -- Consider two subcases: $a = 1$ and $a > 1$.
    by_cases ha : a = 1;
    · -- Substitute $a = 1$ into the equation $2^k * m_BS = p^(a-1) * (p + 1)$ and simplify.
      subst ha
      have h_eq_simplified : 2^k * m_BS = p + 1 := by
        simpa using h_eq;
      -- By the lemma, $2^k * m_BS - 1$ is composite.
      have h_composite : ¬Nat.Prime (2^k * m_BS - 1) := by
        apply composite_implies_not_prime;
        convert riesel_number k ( by linarith ) using 1;
      exact h_composite ( by simpa [ h_eq_simplified ] using hp_prime );
    · -- Since $a > 1$, we have $p \mid 2^k * m_BS$. Since $p$ is odd, $p \mid m_BS$.
      have hp_div_m_BS : p ∣ m_BS := by
        have hp_div_m_BS : p ∣ 2^k * m_BS := by
          exact h_eq.symm ▸ dvd_mul_of_dvd_left ( dvd_pow_self _ ( Nat.sub_ne_zero_of_lt ( lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ( Ne.symm ha ) ) ) ) _;
        exact Or.resolve_left ( hp_prime.dvd_mul.mp hp_div_m_BS ) ( by intro t; have := Nat.Prime.dvd_of_dvd_pow hp_prime t; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] );
      -- Since $p$ is prime and $p \mid m_BS$, we have $p = m_BS$.
      have hp_eq_m_BS : p = m_BS := by
        have := Nat.prime_dvd_prime_iff_eq hp_prime m_BS_prime ; aesop;
      -- Substitute $p = m_BS$ into the equation $2^k * m_BS = p^(a-1) * (p + 1)$ and simplify.
      have h_eq_simplified : 2^k = m_BS^(a-2) * (m_BS + 1) := by
        -- Substitute $p = m_BS$ into the equation $2^k * m_BS = p^(a-1) * (p + 1)$ and simplify by dividing both sides by $m_BS$.
        rw [hp_eq_m_BS] at h_eq;
        rcases a with ( _ | _ | a ) <;> simp +decide [ pow_succ' ] at *;
        · grind;
        · nlinarith [ show 0 < m_BS by unfold m_BS; decide ];
      -- Since $m_BS$ is prime and $m_BS + 1$ is not a power of 2, we have a contradiction.
      have h_contradiction : ¬∃ k, m_BS + 1 = 2^k := by
        exact fun ⟨ k, hk ⟩ => by have := m_BS_plus_one_not_power_of_two k; aesop;
      have h_contradiction : m_BS + 1 ∣ 2^k := by
        exact h_eq_simplified.symm ▸ dvd_mul_left _ _;
      rw [ Nat.dvd_prime_pow ] at h_contradiction <;> norm_num at * ; aesop


lemma totient_le_half_of_even (n : ℕ) (h_even : Even n) (h_pos : 0 < n) : n.totient ≤ n / 2 := by
  -- Since $n$ is even, we can write $n = 2k$ for some integer $k$.
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := even_iff_two_dvd.mp h_even;
  -- Since $k$ is even, the set of numbers coprime with $2k$ is a subset of the odd numbers up to $2k$.
  have h_subset : Finset.filter (fun a => Nat.Coprime (2 * k) a) (Finset.range (2 * k)) ⊆ Finset.image (fun a => 2 * a + 1) (Finset.range k) := by
    intro a ha; aesop;
    exact ⟨ a / 2, by linarith [ Nat.mod_add_div a 2, show a % 2 = 1 from Nat.mod_two_ne_zero.mp fun h => by have := Nat.dvd_gcd ( dvd_mul_right 2 k ) ( Nat.dvd_of_mod_eq_zero h ) ; aesop ], by linarith [ Nat.mod_add_div a 2, show a % 2 = 1 from Nat.mod_two_ne_zero.mp fun h => by have := Nat.dvd_gcd ( dvd_mul_right 2 k ) ( Nat.dvd_of_mod_eq_zero h ) ; aesop ] ⟩;
  exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_image_le.trans ( by norm_num ) )

lemma n_le_four_m (n : ℕ) (h : n - n.totient = 2 * m_BS) : n ≤ 4 * m_BS := by
  -- Assume n is odd. Then φ(n) is even (for n > 2), so n - φ(n) is odd - even = odd.
  by_cases h_odd : Odd n;
  · -- If n is odd, then φ(n) is even (for n > 2), so n - φ(n) is odd - even = odd.
    have h_phi_even : Even (Nat.totient n) := by
      rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ Nat.totient_even ];
    rw [ Nat.sub_eq_iff_eq_add ] at h;
    · obtain ⟨ k, hk ⟩ := h_phi_even; replace h := congr_arg Even h; simp_all +decide [ parity_simps ] ;
      exact absurd h ( by simpa using h_odd );
    · exact Nat.totient_le n;
  · -- If n is even, then φ(n) ≤ n / 2.
    have h_phi_even : n.totient ≤ n / 2 := by
      -- Since n is even, the numbers coprime to n are exactly the odd numbers less than n. There are n/2 such numbers.
      have h_odd_count : Finset.card (Finset.filter (fun x => Nat.gcd x n = 1) (Finset.range n)) ≤ Finset.card (Finset.filter (fun x => x % 2 = 1) (Finset.range n)) := by
        exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_filter.mp hx |>.1, Nat.mod_two_ne_zero.mp fun contra => by have := Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero contra ) ( even_iff_two_dvd.mp ( by simpa using h_odd ) ) ; aesop ⟩;
      -- The set of odd numbers less than n has cardinality n / 2.
      have h_odd_card : Finset.card (Finset.filter (fun x => x % 2 = 1) (Finset.range n)) = n / 2 := by
        rw [ Finset.card_eq_of_bijective ];
        use fun i hi => 2 * i + 1;
        · aesop;
          exact ⟨ a / 2, by linarith [ Nat.mod_add_div a 2, Nat.div_mul_cancel ( even_iff_two_dvd.mp h_odd ) ], by linarith [ Nat.mod_add_div a 2 ] ⟩;
        · exact fun i hi => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Nat.div_mul_le_self n 2 ] ), by norm_num [ Nat.add_mod ] ⟩;
        ·
          -- If $2i + 1 = 2j + 1$, then subtracting 1 from both sides gives $2i = 2j$, and dividing by 2 gives $i = j$.
          intros i j hi hj h_eq
          linarith
      have key : Nat.totient n
          = ( Finset.filter ( fun x => Nat.gcd x n = 1 ) ( Finset.range n ) ).card := by
        rw [ Nat.totient_eq_card_coprime ]
        exact congr_arg Finset.card ( Finset.filter_congr fun x _ => Nat.coprime_comm )
      rw [ key ]
      exact h_odd_count.trans h_odd_card.le
    omega


lemma not_dvd_four (n : ℕ) (h : n - n.totient = 2 * m_BS) : ¬ 4 ∣ n := by
  -- Assume for contradiction that 4 divides n.
  by_contra h_div4
  have h_even : Even n := by
    -- If 4 divides n, then n is even because 4 is even.
    exact even_iff_two_dvd.mpr ( dvd_trans ( by decide ) h_div4 );
  have h_phi_div4 : 4 ∣ n.totient := by
    -- Since $n$ is divisible by 4, we can write $n = 4k$ for some integer $k$.
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k := h_div4;
    -- Since $4k$ is divisible by 4, we have $\phi(4k) = \phi(4) \cdot \phi(k) = 2 \cdot \phi(k)$.
    have h_phi_4k : Nat.totient (4 * k) = 2 * Nat.totient (2 * k) := by
      rw [ show 4 * k = 2 * ( 2 * k ) by ring, Nat.totient_mul_of_prime_of_dvd ] <;> norm_num;
    rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.totient_prime ];
    exact mul_dvd_mul_left 2 ( even_iff_two_dvd.mp ( Nat.totient_even <| by linarith ) );
  -- Since $4 \mid n$ and $4 \mid n.totient$, their difference $n - n.totient$ must also be divisible by 4.
  have h_diff_div4 : 4 ∣ (n - n.totient) := by
    exact Nat.dvd_sub h_div4 h_phi_div4;
  exact absurd h_diff_div4 ( by rw [ h ] ; unfold m_BS; decide )


lemma base_case_reduction : IsCototient (2 * m_BS) ↔ ∃ m, Odd m ∧ 2 * m - m.totient = 2 * m_BS := by
  -- Assume 2 * m_BS is a cototient. Then there exists an n such that 2 * m_BS = n - phi(n).
  apply Iff.intro
  intro h_cototient
  obtain ⟨n, hn⟩ := h_cototient
  have hn_even : Even n := by
    -- Since $2 * m_BS$ is even, $n - n.totient$ must also be even. If $n$ were odd, then $n.totient$ would be even (as the totient of an odd number is even), making $n - n.totient$ odd, which contradicts $2 * m_BS$ being even. Hence, $n$ must be even.
    have h_even : Even (n - n.totient) := by
      exact hn ▸ even_two_mul _;
    cases le_total n ( n.totient ) <;> simp_all +decide [ parity_simps ];
    by_contra h_odd;
    exact h_odd <| Nat.totient_even <| Nat.le_of_not_lt fun h => by interval_cases n <;> contradiction;
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := by
    exact even_iff_two_dvd.mp hn_even
  have hm_odd : Odd m := by
    -- Since $2 * m - 2 * m_BS$ is even and $2 * m_BS$ is even, $2 * m$ must be even. Therefore, $m$ must be odd.
    by_contra hm_even
    have h_div_four : 4 ∣ 2 * m := by
      exact mul_dvd_mul_left 2 ( even_iff_two_dvd.mp ( by simpa using hm_even ) );
    exact not_dvd_four ( 2 * m ) ( by omega ) h_div_four
  use m
  aesop;
  · rw [ Nat.totient_mul ] <;> norm_num [ hm_odd ];
  · aesop;
    -- Let $n = 2m$. Then, $\phi(n) = \phi(2m) = \phi(2) \cdot \phi(m) = 1 \cdot \phi(m) = \phi(m)$.
    use 2 * w;
    rw [ ← right, Nat.totient_mul ] <;> aesop


def IsSolution (m : ℕ) : Prop := Odd m ∧ 2 * m - m.totient = 2 * m_BS

lemma solution_bounds (m : ℕ) (h : IsSolution m) : m_BS < m ∧ m < 2 * m_BS := by
  cases h;
  -- Since $m$ is odd and greater than 1, we have $\varphi(m) \geq 1$.
  have h_phi_ge_one : 1 ≤ m.totient := by
    -- Since $m$ is a positive integer, the totient function $\phi(m)$ is always at least 1.
    apply Nat.pos_of_ne_zero
    intro h_zero
    aesop;
  -- Since $m$ is odd and greater than 1, we have $\varphi(m) < m$.
  have h_phi_lt_m : m.totient < m := by
    -- Since $m$ is odd and greater than 1, we can apply the lemma that states $\varphi(m) < m$ for any $m > 1$.
    have h_phi_lt_m : 1 < m → m.totient < m := by
      exact fun h => Nat.totient_lt m h;
    rcases m with ( _ | _ | m ) <;> simp_all +arith +decide;
  omega


lemma solution_squarefree (m : ℕ) (h : IsSolution m) : Squarefree m := by
  -- Assume m is not squarefree. Then there exists a prime p such that p² divides m.
  by_contra h_not_squarefree
  obtain ⟨p, hp_prime, hp_sq⟩ : ∃ p, Nat.Prime p ∧ p^2 ∣ m := by
    simpa only [ pow_two ] using by rw [ Nat.squarefree_iff_prime_squarefree ] at *; aesop;
  -- Since $p$ is odd and $p^2 \mid m$, we have $p \mid m$ and $p \mid \phi(m)$.
  have hp_div_m : p ∣ m := by
    exact dvd_of_mul_left_dvd hp_sq
  have hp_div_phi : p ∣ m.totient := by
    refine' Nat.dvd_trans _ ( Nat.totient_dvd_of_dvd hp_sq );
    norm_num [ Nat.totient_prime_pow hp_prime ];
  -- Since $p$ divides $2 * m_BS$ and $m_BS$ is prime, $p$ must be either $2$ or $m_BS$. However, $m$ is odd, so $p$ cannot be $2$. Thus, $p = m_BS$.
  have hp_eq_m_BS : p = m_BS := by
    -- Since $p$ divides $2 * m_BS$ and $p$ is prime, $p$ must divide either $2$ or $m_BS$. However, $m$ is odd, so $p$ cannot be $2$. Thus, $p$ must divide $m_BS$.
    have hp_div_m_BS : p ∣ m_BS := by
      have hp_div_2m_BS : p ∣ 2 * m_BS := by
        -- Since $p \mid m$ and $p \mid \phi(m)$, we have $p \mid 2m - \phi(m) = 2m_BS$ by the properties of divisibility.
        have hp_div_2m_BS : p ∣ 2 * m - m.totient := by
          exact Nat.dvd_sub ( dvd_mul_of_dvd_right hp_div_m _ ) hp_div_phi;
        cases h ; aesop;
      -- Since $p$ is odd and $p \mid 2 * m_BS$, it must divide $m_BS$ because $p$ cannot divide $2$.
      have hp_div_m_BS : p ∣ 2 * m_BS → p ≠ 2 → p ∣ m_BS := by
        -- Since $p$ is a prime and $p \neq 2$, it must divide $m_BS$ because $p$ divides $2 * m_BS$ and $p$ cannot divide $2$.
        intros hp_div_2m_BS hp_ne_2
        have hp_div_m_BS : p ∣ 2 * m_BS → p ≠ 2 → p ∣ m_BS := by
          intro hp_div_2m_BS hp_ne_2
          have hp_div_factor : p ∣ 2 ∨ p ∣ m_BS := by
            exact hp_prime.dvd_mul.mp hp_div_2m_BS
          exact hp_div_factor.resolve_left fun h => hp_ne_2 <| by have := Nat.le_of_dvd ( by decide ) h; interval_cases p <;> trivial;
        -- Apply the lemma that if p divides 2*m_BS and p is not 2, then p divides m_BS.
        apply hp_div_m_BS hp_div_2m_BS hp_ne_2;
      cases h ; aesop;
      exact hp_div_m_BS ( by rintro rfl; exact absurd ( left.of_dvd_nat hp_div_m ) ( by norm_num ) );
    have := Nat.prime_dvd_prime_iff_eq hp_prime m_BS_prime; aesop;
  -- Since $m_BS^2 \mid m$, we have $m \geq m_BS^2$.
  have hm_ge_m_BS_sq : m ≥ m_BS^2 := by
    exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by rintro rfl; cases h; aesop ) ) ( hp_eq_m_BS ▸ hp_sq );
  exact not_lt_of_ge hm_ge_m_BS_sq ( by nlinarith only [ solution_bounds m h ] )


lemma totient_mod_3_of_squarefree_not_dvd_3 (n : ℕ) (h_sq : Squarefree n) (h_nd : ¬ 3 ∣ n) : n.totient % 3 ≠ 2 := by
  -- Since $n$ is squarefree and not divisible by 3, each prime factor $p$ of $n$ is either 1 or 2 modulo 3.
  have h_prime_factors : ∀ p ∈ Nat.primeFactors n, p % 3 = 1 ∨ p % 3 = 2 := by
    intro p hp; have := Nat.mod_lt p three_pos; interval_cases _ : p % 3 <;> simp_all +decide [ ← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq ] ;
  -- Since $n$ is squarefree and not divisible by 3, each prime factor $p$ of $n$ is either 1 or 2 modulo 3. Therefore, $\phi(n)$ is the product of $(p-1)$ for each prime factor $p$ of $n$.
  have h_phi_factors : n.totient = ∏ p ∈ Nat.primeFactors n, (p - 1) := by
    rw [ Nat.totient_eq_prod_factorization ];
    · exact Finset.prod_congr rfl fun p hp => by rw [ Nat.factorization_eq_one_of_squarefree ] <;> aesop;
    · aesop_cat;
  -- Since each term (p-1) is either 0 or 1 modulo 3, the product of these terms can only be 0 or 1 modulo 3.
  have h_prod_mod : ∀ p ∈ Nat.primeFactors n, (p - 1) % 3 = 0 ∨ (p - 1) % 3 = 1 := by
    intro p hp; specialize h_prime_factors p hp; omega;
  -- If there exists a prime factor $p$ such that $(p - 1) \equiv 0 \pmod{3}$, then the product is $0 \pmod{3}$.
  by_cases h_zero : ∃ p ∈ Nat.primeFactors n, (p - 1) % 3 = 0;
  · obtain ⟨ p, hp₁, hp₂ ⟩ := h_zero; rw [ h_phi_factors, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hp₁ ] ; norm_num [ Nat.mul_mod, hp₂ ] ;
  · rw [ h_phi_factors, Finset.prod_nat_mod ];
    rw [ Finset.prod_congr rfl fun x hx => Or.resolve_left ( h_prod_mod x hx ) fun hx' => h_zero ⟨ x, hx, hx' ⟩ ] ; norm_num


lemma n_not_div_3 (m : ℕ) (h : IsSolution m) : ¬ 3 ∣ 2 * m := by
  -- Since $m$ is not divisible by 3, $2m$ cannot be divisible by 3 either.
  have h_not_div_3 : ¬(3 ∣ m) := by
    -- Suppose for contradiction that 3 divides m. Then m = 3k for some integer k.
    by_contra h_div_3
    obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := h_div_3;
    -- Since m is squarefree, k is not divisible by 3.
    have h_k_not_div_3 : ¬(3 ∣ k) := by
      have := solution_squarefree ( 3 * k ) h; rw [ Nat.squarefree_mul_iff ] at this; aesop;
      exact absurd ( Nat.dvd_gcd ( by decide : 3 ∣ 3 ) a ) ( by aesop );
    -- Since $m$ is squarefree, $k$ is not divisible by 3, and thus $\phi(k) \neq 2 \mod 3$.
    have h_phi_k_ne_2_mod_3 : (Nat.totient k) % 3 ≠ 2 := by
      -- Since $k$ is squarefree and not divisible by 3, we can apply the lemma totient_mod_3_of_squarefree_not_dvd_3.
      have h_k_squarefree : Squarefree k := by
        have := solution_squarefree ( 3 * k ) h;
        rw [ Nat.squarefree_mul_iff ] at this ; aesop;
      exact?;
    unfold IsSolution at h;
    rw [ Nat.totient_mul ] at h <;> simp_all +arith +decide [ Nat.totient_prime ];
    · unfold m_BS at h; omega;
    · exact Nat.prime_three.coprime_iff_not_dvd.mpr h_k_not_div_3;
  -- Since 3 is a prime number, if it divides 2m, it must divide either 2 or m. But 3 doesn't divide 2, so it must divide m. However, we have h_not_div_3 which states that 3 does not divide m. Therefore, 3 cannot divide 2m.
  exact fun h_div => h_not_div_3 (Nat.prime_three.dvd_mul.mp h_div |> Or.resolve_left <| by norm_num)

lemma n_mod_12_eq_2 (m : ℕ) (h : IsSolution m) : 2 * m % 12 = 2 := by
  -- Assume 3 | 2m. Since m is odd, 3 | m.
  by_cases h3 : 3 ∣ m;
  · -- Since m is squarefree (by solution_squarefree), m = 3k with gcd(3,k)=1.
    obtain ⟨k, hk⟩ : ∃ k, m = 3 * k ∧ Nat.gcd 3 k = 1 := by
      obtain ⟨ k, rfl ⟩ := h3;
      have := solution_squarefree ( 3 * k ) h; simp_all +decide [ Nat.squarefree_mul_iff ] ;
    -- Since $k$ is not divisible by 3, $\phi(k)$ is even. Therefore, $3k - \phi(k) \equiv 1 \mod 3$ implies $\phi(k) \equiv 2 \mod 3$, which contradicts $\phi(k)$ being even.
    have h_contra : Nat.totient k % 3 = 2 := by
      have h_contra : 3 * k - Nat.totient k = m_BS := by
        cases h ; aesop;
        rw [ Nat.totient_mul ] at right;
        · norm_num [ Nat.totient_prime ] at * ; omega;
        · assumption;
      rw [ Nat.sub_eq_iff_eq_add ] at h_contra;
      · have := congr_arg ( · % 3 ) h_contra; norm_num [ Nat.add_mod, Nat.mul_mod ] at this; have := Nat.mod_lt ( Nat.totient k ) zero_lt_three; interval_cases Nat.totient k % 3 <;> trivial;
      · exact le_trans ( Nat.totient_le _ ) ( by linarith );
    exact absurd ( totient_mod_3_of_squarefree_not_dvd_3 k ( by
      have := solution_squarefree m h; aesop;
      exact this.squarefree_of_dvd ( dvd_mul_left _ _ ) ) ( by
      exact fun h => by have := Nat.dvd_gcd ( by decide : 3 ∣ 3 ) h; simp_all +decide ; ) ) ( by aesop );
  · -- Since m is odd and not divisible by 3, m % 3 must be 1 or 2. But if m % 3 = 2, then 2m % 6 = 4, which contradicts 2m % 12 = 2. Therefore, m % 3 must be 1.
    have h_mod3 : m % 3 = 1 := by
      unfold IsSolution at h;
      rw [ Nat.sub_eq_iff_eq_add ] at h;
      · have := congr_arg ( · % 3 ) h.2; norm_num [ Nat.add_mod, Nat.mul_mod ] at this; ( have := Nat.mod_lt m zero_lt_three; interval_cases _ : m % 3 <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ; );
        -- Since $m$ is odd and $m \equiv 2 \pmod{3}$, we have $\phi(m) \equiv 2 \pmod{3}$.
        have h_phi_mod3 : m.totient % 3 = 2 := by
          norm_num [ Nat.add_mod, Nat.mul_mod ] at this; have := Nat.mod_lt ( Nat.totient m ) three_pos; interval_cases Nat.totient m % 3 <;> trivial;
        have h_squarefree : Squarefree m := by
          have h_solution : IsSolution m := by
            exact ⟨ h.1, by omega ⟩
          exact?;
        exact absurd ( totient_mod_3_of_squarefree_not_dvd_3 m h_squarefree ( by omega ) ) ( by norm_num [ h_phi_mod3 ] );
      · exact le_trans ( Nat.totient_le m ) ( by linarith );
    rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> ring_nf at *;
    · exact absurd ( h.1 ) ( by norm_num [ Nat.even_iff ] );
    · omega

lemma m_mod_6_eq_1 (m : ℕ) (h : IsSolution m) : m % 6 = 1 := by
  -- Assume 3 | 2m. Since m is odd, 3 | m.
  by_cases h3 : 3 ∣ m;
  · -- Since m is squarefree (by solution_squarefree), m = 3k with gcd(3,k)=1.
    obtain ⟨k, hk⟩ : ∃ k, m = 3 * k ∧ Nat.gcd 3 k = 1 := by
      obtain ⟨ k, rfl ⟩ := h3;
      have := solution_squarefree ( 3 * k ) h; simp_all +decide [ Nat.squarefree_mul_iff ] ;
    -- Since $k$ is not divisible by 3, $\phi(k)$ is even. Therefore, $3k - \phi(k) \equiv 1 \mod 3$ implies $\phi(k) \equiv 2 \mod 3$, which contradicts $\phi(k)$ being even.
    have h_contra : Nat.totient k % 3 = 2 := by
      have h_contra : 3 * k - Nat.totient k = m_BS := by
        cases h ; aesop;
        rw [ Nat.totient_mul ] at right;
        · norm_num [ Nat.totient_prime ] at * ; omega;
        · assumption;
      rw [ Nat.sub_eq_iff_eq_add ] at h_contra;
      · have := congr_arg ( · % 3 ) h_contra; norm_num [ Nat.add_mod, Nat.mul_mod ] at this; have := Nat.mod_lt ( Nat.totient k ) zero_lt_three; interval_cases Nat.totient k % 3 <;> trivial;
      · exact le_trans ( Nat.totient_le _ ) ( by linarith );
    exact absurd ( totient_mod_3_of_squarefree_not_dvd_3 k ( by
      have := solution_squarefree m h; aesop;
      exact this.squarefree_of_dvd ( dvd_mul_left _ _ ) ) ( by
      exact fun h => by have := Nat.dvd_gcd ( by decide : 3 ∣ 3 ) h; simp_all +decide ; ) ) ( by aesop );
  · -- Since m is odd and not divisible by 3, m % 3 must be 1 or 2. But if m % 3 = 2, then 2m % 6 = 4, which contradicts 2m % 12 = 2. Therefore, m % 3 must be 1.
    have h_mod3 : m % 3 = 1 := by
      unfold IsSolution at h;
      rw [ Nat.sub_eq_iff_eq_add ] at h;
      · have := congr_arg ( · % 3 ) h.2; norm_num [ Nat.add_mod, Nat.mul_mod ] at this; ( have := Nat.mod_lt m zero_lt_three; interval_cases _ : m % 3 <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ; );
        -- Since $m$ is odd and $m \equiv 2 \pmod{3}$, we have $\phi(m) \equiv 2 \pmod{3}$.
        have h_phi_mod3 : m.totient % 3 = 2 := by
          norm_num [ Nat.add_mod, Nat.mul_mod ] at this; have := Nat.mod_lt ( Nat.totient m ) three_pos; interval_cases Nat.totient m % 3 <;> trivial;
        have h_squarefree : Squarefree m := by
          have h_solution : IsSolution m := by
            exact ⟨ h.1, by omega ⟩
          exact?;
        exact absurd ( totient_mod_3_of_squarefree_not_dvd_3 m h_squarefree ( by omega ) ) ( by norm_num [ h_phi_mod3 ] );
      · exact le_trans ( Nat.totient_le m ) ( by linarith );
    rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> ring_nf at *;
    · exact absurd ( h.1 ) ( by norm_num [ Nat.even_iff ] );
    · omega


lemma phi_k_mod_3_contra (k : ℕ) (h_sq : Squarefree k) (h_nd : ¬ 3 ∣ k) (h_eq : 3 * k - k.totient = m_BS) : False := by
  have h_mod3 : k.totient % 3 = 2 := by
    rw [ Nat.sub_eq_iff_eq_add ] at h_eq;
    · have := congr_arg ( · % 3 ) h_eq; norm_num [ Nat.add_mod, Nat.mul_mod ] at this ⊢; have := Nat.mod_lt k.totient zero_lt_three; interval_cases k.totient % 3 <;> trivial;
    · exact le_trans ( Nat.totient_le _ ) ( by linarith );
  exact absurd h_mod3 ( by have := totient_mod_3_of_squarefree_not_dvd_3 k h_sq h_nd; aesop )


/-! ### Custom kernel-reducible factorization

Mathlib's `Nat.minFac` and friends use well-founded recursion, which doesn't reduce in the
kernel. The following definitions use structural recursion on a fuel parameter so they
DO reduce, enabling `decide` to verify the computation. -/

/-- Trial division. Returns the smallest `k' ≥ k` dividing `m` (with `k' * k' ≤ m`),
    or 0 if no such `k'` exists in `[k, sqrt m]`. -/
def smallestDivisorFrom : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, m, k =>
    if k * k > m then 0
    else if m % k = 0 then k
    else smallestDivisorFrom fuel m (k + 1)

/-- Smallest prime factor of `m`. Returns `m` itself if `m` is prime, `0` if `m ≤ 1`. -/
def spf (m : ℕ) : ℕ :=
  if m ≤ 1 then 0
  else if smallestDivisorFrom 1100 m 2 = 0 then m
  else smallestDivisorFrom 1100 m 2

/-- Iterative prime factorization with multiplicity. -/
def factorList : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, m =>
    if m ≤ 1 then []
    else if spf m ≤ 1 then []
    else spf m :: factorList fuel (m / spf m)

/-- Kernel-reducible check: returns `true` if `m` doesn't satisfy the bad condition. -/
def isOK (m : ℕ) : Bool :=
  if m % 2 = 0 then true
  else if m % 3 = 0 then true
  else if (factorList 25 m).foldr (· * ·) 1 ≠ m then true
  else if ¬ (factorList 25 m).Nodup then true
  else if (factorList 25 m).any (fun p => p < 5) then true
  else if (factorList 25 m).any (fun p => spf p ≠ p) then true
  else 2 * m - (factorList 25 m).foldr (fun p acc => (p - 1) * acc) 1 ≠ 2 * 509203

/-- `smallestDivisorFrom` returns 0 or a value in `[k, sqrt m]`. -/
lemma smallestDivisorFrom_dvd (fuel m k : ℕ) (h : smallestDivisorFrom fuel m k ≠ 0) :
    smallestDivisorFrom fuel m k ∣ m := by
  induction fuel generalizing k with
  | zero => simp [smallestDivisorFrom] at h
  | succ n ih =>
    unfold smallestDivisorFrom at h ⊢
    split_ifs at h ⊢ with h1 h2
    · exact absurd rfl h
    · exact Nat.dvd_of_mod_eq_zero h2
    · exact ih (k + 1) h

lemma smallestDivisorFrom_ge (fuel m k : ℕ) (h : smallestDivisorFrom fuel m k ≠ 0) :
    smallestDivisorFrom fuel m k ≥ k := by
  induction fuel generalizing k with
  | zero => simp [smallestDivisorFrom] at h
  | succ n ih =>
    unfold smallestDivisorFrom at h ⊢
    split_ifs at h ⊢ with h1 h2
    · exact absurd rfl h
    · exact le_refl _
    · exact le_trans (Nat.le_succ k) (ih (k + 1) h)

/-- `smallestDivisorFrom` returns the smallest divisor of `m` ≥ `k` (if any). -/
lemma smallestDivisorFrom_minimal (fuel m k : ℕ)
    (h : smallestDivisorFrom fuel m k ≠ 0) :
    ∀ k', k ≤ k' → k' < smallestDivisorFrom fuel m k → ¬ k' ∣ m := by
  induction fuel generalizing k with
  | zero => simp [smallestDivisorFrom] at h
  | succ n ih =>
    intro k' hkk' hk'd
    unfold smallestDivisorFrom at h hk'd
    split_ifs at h hk'd with h1 h2
    · exact absurd rfl h
    · omega
    · rcases Nat.lt_or_ge k' (k + 1) with hk1 | hk1
      · have hkk : k' = k := by omega
        subst hkk
        intro h_dvd
        exact h2 (Nat.dvd_iff_mod_eq_zero.mp h_dvd)
      · exact ih (k + 1) h k' hk1 hk'd

/-- If `smallestDivisorFrom` returns 0, then no `k' ∈ [k, sqrt m]` divides `m` (assuming sufficient fuel). -/
lemma smallestDivisorFrom_eq_zero (fuel m k : ℕ) (hfuel : k + fuel > Nat.sqrt m + 1)
    (h : smallestDivisorFrom fuel m k = 0) :
    ∀ d, k ≤ d → d ∣ m → d ≥ 2 → d > Nat.sqrt m := by
  induction fuel generalizing k with
  | zero =>
    intro d hd hdvd hd2
    by_contra h_le
    push_neg at h_le
    omega
  | succ n ih =>
    unfold smallestDivisorFrom at h
    split_ifs at h with h1 h2
    · -- k * k > m, so any divisor d ≥ k must have d > sqrt m
      intro d hd hdvd hd2
      by_contra h_le
      push_neg at h_le
      have hk : Nat.sqrt m < k := Nat.sqrt_lt.mpr h1
      omega
    · -- branch 2: h : k = 0. So m % 0 = 0 means m = 0
      intro d hd hdvd hd2
      have hk0 : k = 0 := h
      subst hk0
      have hm0 : m = 0 := by
        have : m % 0 = m := Nat.mod_zero m
        omega
      subst hm0
      simp [Nat.sqrt_zero]
      omega
    · intro d hd hdvd hd2
      rcases Nat.lt_or_ge d (k + 1) with hd' | hd'
      · have hdk : d = k := by omega
        subst hdk
        exact absurd (Nat.dvd_iff_mod_eq_zero.mp hdvd) h2
      · exact ih (k + 1) (by omega) h d hd' hdvd hd2

/-- The smallest divisor ≥ 2 of `m` (if it exists) is prime. -/
lemma smallestDivisorFrom_prime_aux (m k : ℕ) (hk : k ≥ 2)
    (hmin : ∀ d, 2 ≤ d → d < k → ¬ d ∣ m)
    (hdvd : k ∣ m) : Nat.Prime k := by
  rw [Nat.prime_def]
  refine ⟨hk, fun d hd => ?_⟩
  have hk_pos : 0 < k := by omega
  rcases Nat.lt_or_ge d 2 with hd' | hd'
  · interval_cases d
    · simp at hd; omega
    · left; rfl
  · right
    have hd_le : d ≤ k := Nat.le_of_dvd hk_pos hd
    rcases Nat.lt_or_eq_of_le hd_le with hlt | heq
    · exact absurd (hd.trans hdvd) (hmin d hd' hlt)
    · exact heq

/-- `spf m` divides `m` when `m ≥ 2`. -/
lemma spf_dvd (m : ℕ) (hm : m ≥ 2) : spf m ∣ m := by
  unfold spf
  rw [if_neg (by omega : ¬ m ≤ 1)]
  split_ifs with h
  · exact dvd_refl m
  · exact smallestDivisorFrom_dvd 1100 m 2 h

/-- `spf m ≥ 2` when `m ≥ 2`. -/
lemma spf_ge_two (m : ℕ) (hm : m ≥ 2) : spf m ≥ 2 := by
  unfold spf
  rw [if_neg (by omega : ¬ m ≤ 1)]
  split_ifs with h
  · exact hm
  · exact smallestDivisorFrom_ge 1100 m 2 h

/-- For `m ≥ 2` and `m < 10^6`, `spf m` is prime. -/
lemma spf_prime (m : ℕ) (hm : m ≥ 2) (hm_bound : m < 1210000) : Nat.Prime (spf m) := by
  unfold spf
  rw [if_neg (by omega : ¬ m ≤ 1)]
  split_ifs with hd
  · -- smallestDivisorFrom returned 0: m has no factor ≤ sqrt(m), so m is prime
    have h_no_small : ∀ d, 2 ≤ d → d ∣ m → d ≥ 2 → d > Nat.sqrt m := by
      apply smallestDivisorFrom_eq_zero 1100 m 2 _ hd
      have h1 : Nat.sqrt m ≤ Nat.sqrt 1210000 := Nat.sqrt_le_sqrt (le_of_lt hm_bound)
      have h_sqrt : Nat.sqrt 1210000 ≤ 1100 := by
        by_contra h
        push_neg at h
        have : 1101 * 1101 ≤ 1210000 := Nat.le_sqrt.mp h
        omega
      omega
    rw [Nat.prime_def]
    refine ⟨hm, fun d hd_dvd => ?_⟩
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · interval_cases d
      · simp at hd_dvd; rw [hd_dvd] at hm; omega
      · left; rfl
    · right
      -- d ≥ 2, d ∣ m. Need: d = m.
      have hm_pos : 0 < m := by omega
      have hd_le_m : d ≤ m := Nat.le_of_dvd hm_pos hd_dvd
      have h_md_dvd : m / d ∣ m := Nat.div_dvd_of_dvd hd_dvd
      have h_eq : d * (m / d) = m := Nat.mul_div_cancel' hd_dvd
      rcases Nat.lt_or_ge (m / d) 2 with hmd1 | hmd2
      · -- m / d = 0 or 1
        rcases Nat.eq_zero_or_pos (m / d) with hmd0 | hmd_pos
        · -- m / d = 0: contradicts h_eq since d * 0 = 0 ≠ m
          rw [hmd0, Nat.mul_zero] at h_eq; omega
        · -- m / d = 1: d * 1 = m, so d = m
          have hmd_eq : m / d = 1 := by omega
          rw [hmd_eq, Nat.mul_one] at h_eq
          exact h_eq
      · -- m / d ≥ 2 and m / d ∣ m. Then m / d > sqrt m. And d > sqrt m.
        -- So m = d * (m/d) > sqrt m * sqrt m ≥ m. Contradiction.
        exfalso
        have h_d_gt : d > Nat.sqrt m := h_no_small d hd2 hd_dvd hd2
        have h_md_gt : m / d > Nat.sqrt m := h_no_small (m / d) hmd2 h_md_dvd hmd2
        have h_mul : (Nat.sqrt m + 1) * (Nat.sqrt m + 1) ≤ d * (m / d) := by
          apply Nat.mul_le_mul <;> omega
        rw [h_eq] at h_mul
        have h_lt : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
        omega
  · -- smallestDivisorFrom returned d ≠ 0, so d is the smallest divisor ≥ 2 of m
    set d := smallestDivisorFrom 1100 m 2 with hd_def
    have hd_dvd : d ∣ m := smallestDivisorFrom_dvd 1100 m 2 hd
    have hd_ge : d ≥ 2 := smallestDivisorFrom_ge 1100 m 2 hd
    have h_min : ∀ k, 2 ≤ k → k < d → ¬ k ∣ m := by
      intro k hk2 hkd
      exact smallestDivisorFrom_minimal 1100 m 2 hd k hk2 hkd
    exact smallestDivisorFrom_prime_aux m d hd_ge h_min hd_dvd

/-- `spf m` equals `m.minFac` when `m ≥ 2` and `m < 10^6`. -/
lemma spf_eq_minFac (m : ℕ) (hm : m ≥ 2) (hm_bound : m < 1210000) :
    spf m = m.minFac := by
  have hspf_dvd : spf m ∣ m := spf_dvd m hm
  have hspf_ge : spf m ≥ 2 := spf_ge_two m hm
  have hspf_prime : Nat.Prime (spf m) := spf_prime m hm hm_bound
  -- m.minFac ≤ spf m (minFac is smallest)
  have h1 : m.minFac ≤ spf m := Nat.minFac_le_of_dvd hspf_ge hspf_dvd
  -- spf m ≤ m.minFac
  have hmf_dvd : m.minFac ∣ m := Nat.minFac_dvd m
  have hmf_prime : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
  have hmf_ge : m.minFac ≥ 2 := hmf_prime.two_le
  -- Use spf's minimality via smallestDivisorFrom_minimal
  unfold spf
  rw [if_neg (by omega : ¬ m ≤ 1)]
  split_ifs with hd
  · -- spf returned m (no factor ≤ sqrt m). So m is prime (proven in spf_prime).
    have : Nat.Prime m := by
      have hp := spf_prime m hm hm_bound
      unfold spf at hp
      rw [if_neg (by omega : ¬ m ≤ 1)] at hp
      rw [if_pos hd] at hp
      exact hp
    rw [this.minFac_eq]
  · -- spf returned d = smallestDivisorFrom 1100 m 2, which is the smallest divisor ≥ 2.
    set d := smallestDivisorFrom 1100 m 2 with hd_def
    -- We want m.minFac = d
    have hd_dvd : d ∣ m := smallestDivisorFrom_dvd 1100 m 2 hd
    have hd_ge : d ≥ 2 := smallestDivisorFrom_ge 1100 m 2 hd
    -- m.minFac ≤ d
    have h_le : m.minFac ≤ d := Nat.minFac_le_of_dvd hd_ge hd_dvd
    -- d ≤ m.minFac (using minimality of d)
    by_contra h_ne
    have h_lt : m.minFac < d := lt_of_le_of_ne h_le (fun h => h_ne h.symm)
    have h_min := smallestDivisorFrom_minimal 1100 m 2 hd m.minFac hmf_ge h_lt
    exact h_min hmf_dvd

/-- `factorList fuel m` equals `m.primeFactorsList` for sufficient fuel. -/
lemma factorList_eq_primeFactorsList (fuel m : ℕ) (h_bound : m < 1210000)
    (h_fuel : m < 2 ^ fuel) :
    factorList fuel m = m.primeFactorsList := by
  induction fuel generalizing m with
  | zero =>
    interval_cases m
    simp [factorList, Nat.primeFactorsList]
  | succ n ih =>
    unfold factorList
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · simp [Nat.primeFactorsList]
      · simp [Nat.primeFactorsList]
    · rw [if_neg (by omega : ¬ m ≤ 1)]
      have hspf : spf m = m.minFac := spf_eq_minFac m hm h_bound
      rw [hspf]
      have hmf_prime : Nat.Prime m.minFac := Nat.minFac_prime (by omega)
      have hmf_ge : m.minFac ≥ 2 := hmf_prime.two_le
      rw [if_neg (by omega : ¬ m.minFac ≤ 1)]
      -- primeFactorsList m = minFac m :: primeFactorsList (m / minFac m) when m ≥ 2
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      rw [Nat.primeFactorsList_add_two]
      congr 1
      apply ih
      · have : (k + 2) / (k + 2).minFac ≤ (k + 2) := Nat.div_le_self _ _
        omega
      · -- (k+2) / minFac (k+2) < 2^n
        -- minFac (k+2) ≥ 2, so (k+2) / minFac (k+2) ≤ (k+2) / 2
        have h1 : (k + 2) / (k + 2).minFac ≤ (k + 2) / 2 :=
          Nat.div_le_div_left hmf_ge (by omega)
        have h2 : (k + 2) / 2 * 2 ≤ k + 2 := Nat.div_mul_le_self _ _
        -- 2^(n+1) > k+2 → 2 * 2^n > k+2 → 2^n > (k+2)/2
        have h3 : 2 * 2^n > k + 2 := by
          have : 2^(n + 1) = 2 * 2^n := by ring
          omega
        omega

/-- Helper: `l.foldr (fun p acc => (p - 1) * acc) 1 = ∏ p ∈ l.toFinset, (p - 1)` when `l.Nodup`. -/
lemma foldr_eq_finset_prod (l : List ℕ) (hl : l.Nodup) :
    l.foldr (fun p acc => (p - 1) * acc) 1 = ∏ p ∈ l.toFinset, (p - 1) := by
  induction l with
  | nil => simp [List.toFinset]
  | cons hd tl ih =>
    rw [List.foldr_cons, List.toFinset_cons]
    have h_notin : hd ∉ tl.toFinset := by
      rw [List.mem_toFinset]
      exact List.nodup_cons.mp hl |>.1
    rw [Finset.prod_insert h_notin]
    rw [ih (List.nodup_cons.mp hl).2]

/-- `List.prod = List.foldr (· * ·) 1`. -/
lemma list_prod_eq_foldr (l : List ℕ) : l.prod = l.foldr (· * ·) 1 := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [List.prod_cons, ih]

/-- `Nat.totient m` equals our totient computation when `m` is squarefree. -/
lemma totient_eq_foldr_minus_one (m : ℕ) (hm : m ≥ 2) (h_sqf : Squarefree m) :
    Nat.totient m = m.primeFactorsList.foldr (fun p acc => (p - 1) * acc) 1 := by
  have hm_ne : m ≠ 0 := by omega
  -- Use totient_mul_prod_primeFactors and prod_primeFactors_of_squarefree
  have h1 : Nat.totient m * (∏ p ∈ m.primeFactors, p) = m * (∏ p ∈ m.primeFactors, (p - 1)) :=
    Nat.totient_mul_prod_primeFactors m
  have h2 : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree h_sqf
  rw [h2] at h1
  -- So φ(m) * m = m * ∏(p-1). Since m ≠ 0, φ(m) = ∏(p-1).
  have h3 : Nat.totient m = ∏ p ∈ m.primeFactors, (p - 1) := by
    have := h1
    rw [mul_comm (Nat.totient m) m] at this
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  rw [h3]
  -- Now convert ∏ p ∈ m.primeFactors, (p-1) = primeFactorsList.foldr ...
  have h_nd : m.primeFactorsList.Nodup := h_sqf.nodup_primeFactorsList
  rw [show m.primeFactors = m.primeFactorsList.toFinset from rfl]
  rw [foldr_eq_finset_prod m.primeFactorsList h_nd]

/-- Correctness: if `isOK m = true` and the bad conditions hold, contradiction. -/
lemma isOK_correct (m : ℕ) (hm_bound : m < 1210000)
    (h_odd : Odd m) (h_sqf : Squarefree m) (h_nd3 : ¬(3 ∣ m))
    (h_isOK : isOK m = true) : 2 * m - Nat.totient m ≠ 2 * m_BS := by
  have hm_ne : m ≠ 0 := h_sqf.ne_zero
  have hm_ge : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm_ne
  have hm2 : ¬ m % 2 = 0 := by
    intro h
    have := Nat.odd_iff.mp h_odd
    omega
  have hm3 : ¬ m % 3 = 0 := fun h => h_nd3 (Nat.dvd_iff_mod_eq_zero.mpr h)
  -- For m = 1: 2*1 - 1 = 1 ≠ 2*m_BS = 1018406
  rcases Nat.lt_or_ge m 2 with hm1 | hm_ge2
  · interval_cases m
    simp [Nat.totient_one]
    unfold m_BS; decide
  -- m ≥ 2
  have h_factor : factorList 25 m = m.primeFactorsList := by
    apply factorList_eq_primeFactorsList 25 m hm_bound
    have : (2 : ℕ) ^ 25 = 33554432 := by decide
    omega
  unfold isOK at h_isOK
  rw [if_neg hm2, if_neg hm3] at h_isOK
  set l := factorList 25 m with hl_def
  have hl_eq : l = m.primeFactorsList := h_factor
  -- l is Nodup (squarefree)
  have hl_nodup : l.Nodup := by rw [hl_eq]; exact h_sqf.nodup_primeFactorsList
  -- l.foldr (· * ·) 1 = m
  have hl_prod : l.foldr (· * ·) 1 = m := by
    rw [← list_prod_eq_foldr, hl_eq]
    exact Nat.prod_primeFactorsList hm_ne
  -- Each p ∈ l is prime
  have hl_prime : ∀ p ∈ l, Nat.Prime p := by
    intro p hp
    rw [hl_eq] at hp
    exact Nat.prime_of_mem_primeFactorsList hp
  -- Each p ∈ l satisfies p ≥ 5
  have hl_ge5 : ∀ p ∈ l, p ≥ 5 := by
    intro p hp
    have hp_prime : Nat.Prime p := hl_prime p hp
    have hp_dvd : p ∣ m := by
      rw [hl_eq] at hp
      exact Nat.dvd_of_mem_primeFactorsList hp
    have hp_ne2 : p ≠ 2 := fun h => by
      have h2dvd : 2 ∣ m := h ▸ hp_dvd
      have hmod := Nat.odd_iff.mp h_odd
      have : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2dvd
      omega
    have hp_ne3 : p ≠ 3 := fun h => h_nd3 (h ▸ hp_dvd)
    have hp_ge2 : p ≥ 2 := hp_prime.two_le
    -- p prime, p ≠ 2, p ≠ 3, so p ≥ 5
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p
      · exact (hp_ne2 rfl).elim  -- p = 2
      · exact (hp_ne3 rfl).elim  -- p = 3
      · exact absurd hp_prime (by decide)  -- p = 4
    · exact h
  -- Each p ∈ l satisfies spf p = p (since prime)
  have hl_spf : ∀ p ∈ l, spf p = p := by
    intro p hp
    have hp_prime : Nat.Prime p := hl_prime p hp
    have hp_ge5 : p ≥ 5 := hl_ge5 p hp
    have hp_ge2 : p ≥ 2 := by omega
    have hp_bound : p < 1210000 := by
      -- p ∣ m, m < 1210000, so p ≤ m < 1210000
      have hp_dvd : p ∣ m := by
        rw [hl_eq] at hp
        exact Nat.dvd_of_mem_primeFactorsList hp
      exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) hp_dvd) hm_bound
    -- spf p = p.minFac (by spf_eq_minFac) = p (since p prime)
    rw [spf_eq_minFac p hp_ge2 hp_bound, hp_prime.minFac_eq]
  -- Now simplify h_isOK
  -- The branches: if l.foldr (·*·) 1 ≠ m then true; else if ¬l.Nodup then true; else if l.any (·<5) then true; else if l.any (spf p ≠ p) then true; else final.
  rw [if_neg (by simp [hl_prod] : ¬ l.foldr (· * ·) 1 ≠ m)] at h_isOK
  rw [if_neg (by simp [hl_nodup] : ¬ ¬ l.Nodup)] at h_isOK
  rw [if_neg (by
    simp only [List.any_eq_true, not_exists, not_and]
    intro p hp hp_lt
    have h_ge := hl_ge5 p hp
    have h_lt := decide_eq_true_eq.mp hp_lt
    omega)] at h_isOK
  rw [if_neg (by
    simp only [List.any_eq_true, not_exists, not_and]
    intro p hp hp_ne
    have h_eq := hl_spf p hp
    have h_ne := decide_eq_true_eq.mp hp_ne
    exact h_ne h_eq)] at h_isOK
  -- h_isOK now: decide (2 * m - l.foldr (...) 1 ≠ 2 * 509203) = true
  have h_prop : 2 * m - l.foldr (fun p acc => (p - 1) * acc) 1 ≠ 2 * 509203 :=
    of_decide_eq_true h_isOK
  intro h_contra
  apply h_prop
  have h_totient_eq : l.foldr (fun p acc => (p - 1) * acc) 1 = Nat.totient m := by
    rw [totient_eq_foldr_minus_one m hm_ge2 h_sqf, hl_eq]
  have h_bs_def : (m_BS : ℕ) = 509203 := rfl
  omega

/-- Bool-valued check: all `m ∈ [lo, hi)` satisfy `isOK m = true`. Uses fuel-bounded recursion. -/
def allIsOK : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, lo, hi =>
    if lo ≥ hi then true
    else if isOK lo = false then false
    else allIsOK fuel (lo + 1) hi

lemma allIsOK_correct (fuel lo hi : ℕ) (h_fuel : hi ≤ lo + fuel) (h : allIsOK fuel lo hi = true) :
    ∀ m, lo ≤ m → m < hi → isOK m = true := by
  induction fuel generalizing lo with
  | zero => intro m hm1 hm2; omega
  | succ n ih =>
    intro m hm1 hm2
    rw [allIsOK] at h
    by_cases h1 : lo ≥ hi
    · omega
    · rw [if_neg h1] at h
      by_cases h2 : isOK lo = false
      · rw [if_pos h2] at h
        exact absurd h (by decide)
      · rw [if_neg h2] at h
        by_cases hm_eq : m = lo
        · rw [hm_eq]
          -- isOK lo ≠ false → isOK lo = true
          match hOK : isOK lo with
          | true => rfl
          | false => exact absurd hOK h2
        · exact ih (lo + 1) (by omega) h m (by omega) hm2

/-- Chunked Bool check: ANDs `allIsOK` over consecutive 1000-element windows. -/
def chunksOK : ℕ → Bool
  | 0 => true
  | k + 1 =>
    let lo := 509204 + 1000 * k
    let hi := if k + 1 = 510 then 1018406 else lo + 1000
    allIsOK 1000 lo hi && chunksOK k

lemma chunksOK_correct (n : ℕ) (hn : n ≤ 510) (h : chunksOK n = true) :
    ∀ m, 509204 ≤ m → m < (if n = 510 then 1018406 else 509204 + 1000 * n) → isOK m = true := by
  induction n with
  | zero => intro m _ hm2; simp at hm2; omega
  | succ k ih =>
    intro m hm1 hm2
    unfold chunksOK at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h_chunk, h_rest⟩ := h
    have hk_le : k ≤ 510 := by omega
    by_cases hm_in_chunk : 509204 + 1000 * k ≤ m
    · have h_endpt : m < (if k + 1 = 510 then 1018406 else 509204 + 1000 * (k + 1)) := hm2
      have h_chunk_end : m < if k + 1 = 510 then 1018406 else 509204 + 1000 * k + 1000 := by
        split_ifs at h_endpt with hk_eq
        · simp [hk_eq]; exact h_endpt
        · simp [hk_eq]; omega
      exact allIsOK_correct 1000 (509204 + 1000 * k)
        (if k + 1 = 510 then 1018406 else 509204 + 1000 * k + 1000)
        (by split_ifs <;> omega) h_chunk m hm_in_chunk h_chunk_end
    · push_neg at hm_in_chunk
      have h_m_in_prev : m < if k = 510 then 1018406 else 509204 + 1000 * k := by
        split_ifs with hk_eq
        · omega
        · exact hm_in_chunk
      exact ih hk_le h_rest m hm1 h_m_in_prev

/-! ### `computation_lemma`

For m ∈ (m_BS, 2*m_BS) with m odd, squarefree, not divisible by 3, all prime factors are ≥ 5.
Let r = |primeFactors m|. Since 5·7·11·13·17·19 = 1616615 > 2*m_BS, we have r ≤ 5.
For each r ∈ {1,…,5}, the equation `2m - φ(m) = 2*m_BS` either has no solution or
contradicts other constraints.

-/

lemma computation_lemma : ¬ ∃ m, IsSolution m := by
  -- We'll use the fact that if the conditions hold, then m must be in the range (509203, 1018406) and satisfy the equation.
  have h_check : ∀ m ∈ Finset.Ico (m_BS + 1) (2 * m_BS), Odd m → Squarefree m → ¬(3 ∣ m) → 2 * m - Nat.totient m ≠ 2 * m_BS := by
    intro m hm h_odd h_sqf h_nd3 h_eq
    have hm_lt : m < 1210000 := by
      have := Finset.mem_Ico.mp hm
      unfold m_BS at this
      omega
    have h_isOK_correct := isOK_correct m hm_lt h_odd h_sqf h_nd3
    have h_chunks : chunksOK 510 = true := by native_decide
    have h_all : ∀ m', 509204 ≤ m' → m' < 1018406 → isOK m' = true := by
      intro m' hm1 hm2
      have := chunksOK_correct 510 (le_refl _) h_chunks m' hm1
      simp at this
      exact this hm2
    have hm_bds : 509204 ≤ m ∧ m < 1018406 := by
      have := Finset.mem_Ico.mp hm
      unfold m_BS at this
      omega
    exact h_isOK_correct (h_all m hm_bds.1 hm_bds.2) h_eq
  contrapose! h_check;
  exact ⟨ h_check.choose, Finset.mem_Ico.mpr ⟨ by linarith [ solution_bounds h_check.choose h_check.choose_spec ], by linarith [ solution_bounds h_check.choose h_check.choose_spec ] ⟩, h_check.choose_spec.1, solution_squarefree h_check.choose h_check.choose_spec, by have := n_not_div_3 h_check.choose h_check.choose_spec; omega, h_check.choose_spec.2 ⟩


lemma base_case : IsNoncototient (2 * m_BS) := by
  -- We have proven that 2 * m_BS is a cototient if and only if there exists a solution m (base_case_reduction). We have also proven that there is no solution m (computation_lemma).
  have h_base : IsCototient (2 * m_BS) ↔ ∃ m, IsSolution m := by
    -- Apply the base_case_reduction lemma to conclude the equivalence.
    apply base_case_reduction;
  exact fun h => computation_lemma.elim <| h_base.mp h


theorem browkin_schinzel (k : ℕ) (hk : 1 ≤ k) : IsNoncototient (2^k * m_BS) := by
  -- We proceed by induction on $k$.
  induction' hk with k ih;
  · -- Apply the base_case lemma to conclude the proof for the base case.
    apply base_case;
  · -- Apply the inductive step to $k+1$.
    apply inductive_step (k + 1) (by linarith [Nat.succ_le_iff.mp ih]) (by assumption)

/--
Are there infinitely many integers not of the form $n - \phi(n)$?

This is true, as shown by Browkin and Schinzel [BrSc95].

[BrSc95] Browkin, J. and Schinzel, A., _On integers not of the form {$n-\phi(n)$}_.
Colloq. Math. (1995), 55-58.
-/
theorem erdos_418 : { (n - n.totient : ℕ) | n }ᶜ.Infinite := by
  -- Since the set {2^k * m_BS | k ≥ 1} is infinite, the set of noncototients must also be infinite.
  have h_infinite : Set.Infinite {x : ℕ | ∃ k ≥ 1, x = 2^k * m_BS} := by
    -- To prove the set is infinite, we show that the function $k \mapsto 2^k \cdot m_BS$ is injective.
    have h_inj : Function.Injective (fun k : ℕ => 2^k * m_BS) := by
      -- To prove injectivity, assume $2^a * m_BS = 2^b * m_BS$. Since $m_BS$ is non-zero, we can divide both sides by $m_BS$, yielding $2^a = 2^b$. The exponential function with base 2 is injective, so $a = b$.
      intro a b hab
      have h_exp : 2^a = 2^b := by
        exact mul_right_cancel₀ ( show m_BS ≠ 0 by unfold m_BS; decide ) hab;
      -- Since the exponential function with base 2 is injective, if $2^a = 2^b$, then $a = b$.
      apply Nat.pow_right_injective (by norm_num) h_exp;
    exact Set.infinite_of_injective_forall_mem ( fun a b h => by simpa using h_inj h ) fun k => ⟨ k + 1, by linarith, rfl ⟩;
  -- By Lemma~\ref{lem:browkin_schinzel}, each element of this set is a noncototient.
  have h_noncototient : ∀ k ≥ 1, IsNoncototient (2^k * m_BS) := by
    -- Apply the lemma browkin_schinzel to conclude that 2^k * m_BS is a noncototient for any k ≥ 1.
    intros k hk
    apply browkin_schinzel k hk;
  exact h_infinite.mono fun x hx => by obtain ⟨ k, hk, rfl ⟩ := hx; exact fun h => h_noncototient k hk <| by obtain ⟨ n, hn ⟩ := h; exact ⟨ n, hn.symm ⟩ ;

#print axioms erdos_418
-- 'Erdos418.erdos_418' depends on axioms: [propext, Classical.choice, Quot.sound,
--  computation_lemma._native.native_decide.ax_1_2]

end Erdos418
