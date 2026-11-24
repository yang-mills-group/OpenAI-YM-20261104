import YM.Integration.ActualRunPacketRetuning
import YM.Extra.ITERATION_NO_LOSS.Sums

/-!
Finite copies of every original marked packet row. Each copy keeps the
original Option token, mode, rank and geometric data, while its coefficient
is scaled and its integer coupling power is increased by an even number.
The complete rootwise triangle bill is explicit. Signed-power regrouping
is asserted only away from zero; it supplies no cleared-jet identity.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualPacketFiniteCopies
open Lattice Wilson RG Marker Precision
open Push.AbsoluteSums
open Comparison.Density.RenderM LocalComparison ActualRunPacketRetuning
open scoped BigOperators

variable {G : Gauge} {n : Side} {V : Type}
    {D : V → ComparisonDensity.Address.Orbit}

def index (r : ℕ) : ℕ ≃ ℕ × Fin (r + 1) := Nat.divModEquiv (r + 1)

private theorem scaled_touch {q : ℕ} (c : ℂ)
    (T : Token G n (fun v => (D v).Mood) q) (x : TestSpace D)
    (A : Fin q → G.Color) :
    (scaleToken c T).touch x A = c * T.touch x A := by
  unfold Token.touch scaleToken
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private theorem scaled_read {q : ℕ} (c : ℂ)
    (T : Token G n (fun v => (D v).Mood) q)
    (x : TestSpace D) (U : Config G n) :
    (scaleToken c T).read x U = c * T.read x U :=
  scaled_touch c T x _

variable [DecidableEq V] {S : Census V}

def copies (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) : MarkedPackets D G n S where
  mode k := P.mode (index r k).1
  rank k := P.rank (index r k).1
  power k := P.power (index r k).1 + (2 * (index r k).2.val : ℕ)
  packet k := (P.packet (index r k).1).map
    (scaleToken (c (P.power (index r k).1) (index r k).2))
  marked k T h := by
    cases he : P.packet (index r k).1 with
    | none => simp [he] at h
    | some Q => exact P.marked _ Q he
  rankCap := P.rankCap
  powerCap := P.powerCap + 2 * r
  rank_bounded k T h := by
    cases he : P.packet (index r k).1 with
    | none => simp [he] at h
    | some Q => exact P.rank_bounded _ Q he
  power_bounded k T h := by
    cases he : P.packet (index r k).1 with
    | none => simp [he] at h
    | some Q =>
        calc
          (P.power (index r k).1 + (2 * (index r k).2.val : ℕ)).natAbs
              ≤ (P.power (index r k).1).natAbs + 2 * (index r k).2.val := by
                simpa only [Int.natAbs_natCast] using Int.natAbs_add_le (P.power (index r k).1)
                  ((2 * (index r k).2.val : ℕ) : ℤ)
          _ ≤ P.powerCap + 2 * r :=
            Nat.add_le_add (P.power_bounded _ Q he)
              (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ (index r k).2.isLt))
  nonnegative_grade k T h := by
    cases he : P.packet (index r k).1 with
    | none => simp [he] at h
    | some Q =>
        have hp := P.nonnegative_grade _ Q he
        have hj : (0 : ℤ) ≤ (2 * (index r k).2.val : ℕ) := by positivity
        linarith

/-- Original modes/ranks survive every copy; only the explicit even power
shift and corresponding finite power cap are new. -/
theorem copies_layout (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (k : ℕ) :
    (copies P r c).mode k = P.mode (index r k).1 ∧
    (copies P r c).rank k = P.rank (index r k).1 ∧
    (copies P r c).power k =
      P.power (index r k).1 + (2 * (index r k).2.val : ℕ) ∧
    (copies P r c).rankCap = P.rankCap ∧
    (copies P r c).powerCap = P.powerCap + 2 * r :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The actual token in each copy is the original token with only its
coefficient tensor and its coefficient cost rescaled. -/
theorem copies_packet (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (k : ℕ)
    (T : Token G n (fun v => (D v).Mood) (P.rank (index r k).1))
    (hT : P.packet (index r k).1 = some T) :
    (copies P r c).packet k =
      some (scaleToken (c (P.power (index r k).1) (index r k).2) T) := by
  simp only [copies, hT, Option.map_some]

/-- Signed powers are regrouped only at a nonzero coupling. -/
theorem copies_term (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) (hg : g ≠ 0)
    (x : TestSpace D) (U : Config G n) (k : ℕ) :
    (copies P r c).term x g U k =
      (c (P.power (index r k).1) (index r k).2 *
        (g : ℂ) ^ (2 * (index r k).2.val)) *
      P.term x g U (index r k).1 := by
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  cases he : P.packet (index r k).1 with
  | none => simp only [MarkedPackets.term, copies, he, Option.map_none, mul_zero]
  | some T =>
      simp only [MarkedPackets.term, copies, he, Option.map_some, scaled_read]
      rw [zpow_add₀ hgc, zpow_natCast]
      ring

def coefficientMass (cap r : ℕ) (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc (-(cap : ℤ)) (cap : ℤ),
    ∑ j, ‖c e j‖ * ‖(g : ℂ) ^ (2 * j.val)‖

/-- An explicit finite, nonnegative cost before any scalar uniform bound. -/
theorem coefficientMass_nonneg (cap r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) :
    0 ≤ coefficientMass cap r c g := by
  unfold coefficientMass
  exact Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))

def copyWeight (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) (i : ℕ) (j : Fin (r + 1)) : ℝ :=
  match P.packet i with
  | none => 0
  | some _ => ‖c (P.power i) j‖ * ‖(g : ℂ) ^ (2 * j.val)‖

private theorem power_abs_le (P : MarkedPackets D G n S) (i : ℕ)
    (T : Token G n (fun v => (D v).Mood) (P.rank i))
    (hT : P.packet i = some T) : |P.power i| ≤ (P.powerCap : ℤ) := by
  have h : ((P.power i).natAbs : ℤ) ≤ (P.powerCap : ℤ) := by
    exact_mod_cast P.power_bounded i T hT
  simpa only [Int.natCast_natAbs] using h

private theorem weight_budget_bound (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g bound : ℝ) (hbound : 0 ≤ bound)
    (hc : ∀ e : ℤ, |e| ≤ (P.powerCap : ℤ) →
      (∑ j : Fin (r + 1), ‖c e j‖ * ‖(g : ℂ) ^ (2 * j.val)‖) ≤ bound)
    (i : ℕ) : SumBudget (copyWeight P r c g i) bound := by
  classical
  refine ⟨?_, (hasSum_fintype _).summable, ?_⟩
  · intro j
    cases he : P.packet i <;> simp only [copyWeight, he]
    · exact le_rfl
    · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · rw [tsum_fintype]
    cases he : P.packet i with
    | none =>
        simpa only [copyWeight, he, Finset.sum_const_zero] using
          hbound
    | some T =>
        simp only [copyWeight, he]
        exact hc (P.power i) (power_abs_le P i T he)

def rowCharge (P : MarkedPackets D G n S) (w : V → ℝ)
    (g width : ℝ) (v : V) (i : ℕ) : ℝ :=
  if v ∈ (P.mode i).val then
    match P.packet i with
    | none => 0
    | some T => Poly.toll w (P.mode i) * ‖(g : ℂ) ^ P.power i‖ *
        T.coin * Real.exp (width * T.fall)
  else 0

/-- Exact rootwise charge of a copy, with no geometric or width loss. -/
theorem copies_charge (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) (hg : g ≠ 0)
    (w : V → ℝ) (width : ℝ) (v : V) (k : ℕ) :
    rowCharge (copies P r c) w g width v k =
      rowCharge P w g width v (index r k).1 *
        copyWeight P r c g (index r k).1 (index r k).2 := by
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  unfold rowCharge
  dsimp only [copies]
  split_ifs with hv
  · cases he : P.packet (index r k).1 with
    | none => simp only [he, Option.map_none, copyWeight, zero_mul]
    | some T =>
        simp only [he, Option.map_some, copyWeight]
        dsimp only [scaleToken]
        rw [zpow_add₀ hgc, zpow_natCast, norm_mul]
        ring
  · simp only [zero_mul]

/-- A uniform bound for each finite power fibre pays every original Paid
field directly. There is no extra factor counting the possible powers. -/
theorem copies_paid_of_bound (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) (hg : g ≠ 0)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hc : ∀ e : ℤ, |e| ≤ (P.powerCap : ℤ) →
      (∑ j : Fin (r + 1), ‖c e j‖ * ‖(g : ℂ) ^ (2 * j.val)‖) ≤ bound)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w g width budget coverOffset coverSlope) :
    (copies P r c).Paid B address region w g width
      (budget * bound) coverOffset coverSlope := by
  refine
    { width_pos := hP.width_pos
      positive := hP.positive
      coefficient := ?_
      paths := ?_
      addresses := ?_
      symmetry := ?_
      reads := ?_
      multilinear := ?_
      roots := ?_
      cover := ?_
      width_reserved := hP.width_reserved }
  · intro k Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    refine ⟨mul_nonneg (norm_nonneg _) (hP.coefficient _ T hT).1, ?_⟩
    intro x
    change (∑ j, ‖c (P.power (index r k).1) (index r k).2 *
      T.gem j (testInclusion D x)‖) ≤
      ‖c (P.power (index r k).1) (index r k).2‖ * T.coin
    simp only [norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((hP.coefficient _ T hT).2 x) (norm_nonneg _)
  · intro k Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.paths _ T hT
  · intro k Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.addresses _ T hT
  · intro k Q hQ x U a
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    change (scaleToken (c (P.power (index r k).1) (index r k).2) T).touch x
        (fun j => G.adjoint a (U j)) =
      (scaleToken (c (P.power (index r k).1) (index r k).2) T).touch x U
    exact (scaled_touch (c (P.power (index r k).1) (index r k).2) T x _).trans
      ((congrArg (fun z : ℂ => c (P.power (index r k).1) (index r k).2 * z)
        (hP.symmetry _ T hT x U a)).trans
          (scaled_touch (c (P.power (index r k).1) (index r k).2) T x U).symm)
  · intro k Q hQ j x y hxy
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact congrArg (fun z : ℂ => c (P.power (index r k).1) (index r k).2 * z)
      (hP.reads _ T hT j x y hxy)
  · intro k Q hQ j
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact RG3.Held.Letter.cmul (c (P.power (index r k).1) (index r k).2)
      (hP.multilinear _ T hT j)
  · intro v
    have hroot : SumBudget (rowCharge P w g width v) budget := by
      convert hP.roots v using 2
      simp only [rowCharge]
      rename_i i
      split_ifs with hmem
      · cases P.packet i <;> rfl
      · rfl
    have hprod := Extra.Iteration.Cost.prod
      (f := rowCharge P w g width v)
      (g := copyWeight P r c g)
      hroot (weight_budget_bound P r c g bound hbound hc) hbound
    have hindex := Extra.Iteration.Cost.equiv (index r) hprod
    have he : rowCharge (copies P r c) w g width v =
        fun k => rowCharge P w g width v (index r k).1 *
          copyWeight P r c g (index r k).1 (index r k).2 :=
      funext (copies_charge P r c g hg w width v)
    have hrow : SumBudget (rowCharge (copies P r c) w g width v) (budget * bound) := by
      rw [he]
      exact hindex
    convert hrow using 2
    simp only [rowCharge]
    rename_i i
    split_ifs with hmem
    · cases (copies P r c).packet i <;> rfl
    · rfl
  · intro k Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.cover _ T hT

/-- The explicit finite coefficientMass remains a sufficient cost when
no sharper scalar bound has yet been attached. -/
theorem copies_paid (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) (hg : g ≠ 0)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w g width budget coverOffset coverSlope) :
    (copies P r c).Paid B address region w g width
      (budget * coefficientMass P.powerCap r c g) coverOffset coverSlope := by
  apply copies_paid_of_bound P r c g hg _
    (coefficientMass_nonneg P.powerCap r c g) _ hP
  intro e he
  exact Finset.single_le_sum
    (f := fun z : ℤ => ∑ j : Fin (r + 1), ‖c z j‖ * ‖(g : ℂ) ^ (2 * j.val)‖)
    (fun z _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (Finset.mem_Icc.mpr (abs_le.mp he))

private theorem finite_fibre_sum {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {J : Type*} [Fintype J]
    (e : ℕ ≃ ℕ × J) (f : ℕ → E) (h : ℕ → J → E)
    (hs : Summable f) (he : ∀ k, f k = h (e k).1 (e k).2) :
    (∑' k, f k) = ∑' i, ∑ j, h i j := by
  let F : ℕ × J → E := fun ij => h ij.1 ij.2
  have hF : Summable F := e.summable_iff.mp (hs.congr he)
  calc
    (∑' k, f k) = ∑' k, F (e k) := tsum_congr he
    _ = ∑' ij, F ij := e.tsum_eq F
    _ = ∑' i, ∑' j, F (i, j) := hF.tsum_prod
    _ = _ := tsum_congr (fun i => tsum_fintype (fun j => h i j))

/-- Exact regrouping of the literal copy series. The summability is for
that same series; no formal rearrangement without it is asserted. -/
theorem copies_read [Fintype V] (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) (hg : g ≠ 0)
    (x : TestSpace D) (U : Config G n)
    (hs : Summable (fun k =>
      Poly.send ((copies P r c).mode k) ((copies P r c).term x g U k))) :
    (copies P r c).read x g U =
      ∑' i, ∑ j : Fin (r + 1),
        Poly.send (P.mode i)
          ((c (P.power i) j * (g : ℂ) ^ (2 * j.val)) * P.term x g U i) := by
  apply finite_fibre_sum (index r)
    (fun k => Poly.send ((copies P r c).mode k)
      ((copies P r c).term x g U k))
    (fun i j => Poly.send (P.mode i)
      ((c (P.power i) j * (g : ℂ) ^ (2 * j.val)) * P.term x g U i)) hs
  intro k
  exact congrArg (Poly.send (P.mode (index r k).1))
    (copies_term P r c g hg x U k)

/-- A rowwise scalar identity gives the full original read, with all
independent tests and full fields unchanged. Actual applications pay hs
from their literal packet summability supplier. -/
theorem copies_read_of_scalar [Fintype V] (P : MarkedPackets D G n S) (r : ℕ)
    (c : ℤ → Fin (r + 1) → ℂ) (g : ℝ) (hg : g ≠ 0)
    (hscalar : ∀ e : ℤ, |e| ≤ (P.powerCap : ℤ) →
      (∑ j : Fin (r + 1), c e j * (g : ℂ) ^ (2 * j.val)) = 1)
    (x : TestSpace D) (U : Config G n)
    (hs : Summable (fun k =>
      Poly.send ((copies P r c).mode k) ((copies P r c).term x g U k))) :
    (copies P r c).read x g U = P.read x g U := by
  rw [copies_read P r c g hg x U hs]
  apply tsum_congr
  intro i
  cases he : P.packet i with
  | none => simp only [MarkedPackets.term, he, mul_zero, Poly.send_zero,
      Finset.sum_const_zero]
  | some T =>
      apply Marker.Poly.ext
      intro a
      simp only [Poly.part_sum, Poly.part_send]
      by_cases ha : a = P.mode i
      · simp only [ha, if_pos]
        rw [← Finset.sum_mul, hscalar (P.power i) (power_abs_le P i T he), one_mul]
      · simp only [if_neg ha, Finset.sum_const_zero]

end YM.Integration.ActualPacketFiniteCopies
end
