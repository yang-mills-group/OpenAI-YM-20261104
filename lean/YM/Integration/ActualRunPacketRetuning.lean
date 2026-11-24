import YM.Integration.LocalComparisonPackets
import YM.Integration.ActualRunCouplingComposition

/-!
Literal fixed-ratio retuning of every original marked packet row. Only its
coefficient tensor and its corresponding nonnegative cost are rescaled.
The countable Option layout, mode, rank, power, root, paths, support and
length remain unchanged. The Paid bill transfers exactly between the two
physical couplings, without an extra ratio factor.

This finite packet is a fixed-ratio re-expression. Its analytic germ is
not asserted to equal the nonlinear beta-reset germ. Prescribed jets and
next-input admission remain separate duties.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunPacketRetuning
open Lattice Wilson RG Marker Precision
open Push.AbsoluteSums
open Comparison.Density.RenderM LocalComparison
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open MatchingLedger.Compass.Income
open scoped BigOperators

variable {G : Gauge} {n : Side} {V : Type}
    {D : V → ComparisonDensity.Address.Orbit} {q : ℕ}

def scaleToken (c : ℂ) (T : Token G n (fun v => (D v).Mood) q) :
    Token G n (fun v => (D v).Mood) q :=
  { T with
    gem := fun j x => c * T.gem j x
    coin := ‖c‖ * T.coin }

private theorem scaleToken_touch (c : ℂ)
    (T : Token G n (fun v => (D v).Mood) q) (x : TestSpace D)
    (A : Fin q → G.Color) :
    (scaleToken c T).touch x A = c * T.touch x A := by
  unfold Token.touch scaleToken
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem scaleToken_read (c : ℂ)
    (T : Token G n (fun v => (D v).Mood) q)
    (x : TestSpace D) (U : Config G n) :
    (scaleToken c T).read x U = c * T.read x U := by
  exact scaleToken_touch c T x _

variable [DecidableEq V] {S : Census V}

def retune (P : MarkedPackets D G n S) (a : ℝ) : MarkedPackets D G n S where
  mode := P.mode
  rank := P.rank
  power := P.power
  packet i := (P.packet i).map (scaleToken ((a : ℂ) ^ P.power i))
  marked i T h := by
    cases he : P.packet i with
    | none => simp [he] at h
    | some Q => exact P.marked i Q he
  rankCap := P.rankCap
  powerCap := P.powerCap
  rank_bounded i T h := by
    cases he : P.packet i with
    | none => simp [he] at h
    | some Q => exact P.rank_bounded i Q he
  power_bounded i T h := by
    cases he : P.packet i with
    | none => simp [he] at h
    | some Q => exact P.power_bounded i Q he
  nonnegative_grade i T h := by
    cases he : P.packet i with
    | none => simp [he] at h
    | some Q => exact P.nonnegative_grade i Q he

/-- Every nonempty original row has exactly its rescaled original token. -/
theorem retune_packet (P : MarkedPackets D G n S) (a : ℝ) (i : ℕ)
    (T : Token G n (fun v => (D v).Mood) (P.rank i)) (hT : P.packet i = some T) :
    (retune P a).packet i = some (scaleToken ((a : ℂ) ^ P.power i) T) := by
  simp only [retune, hT, Option.map_some]

/-- The original countable layout and both finite caps are retained. -/
theorem retune_layout (P : MarkedPackets D G n S) (a : ℝ) :
    (retune P a).mode = P.mode ∧ (retune P a).rank = P.rank ∧
    (retune P a).power = P.power ∧ (retune P a).rankCap = P.rankCap ∧
    (retune P a).powerCap = P.powerCap :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Full row values, including the original nonlinear curvature completion. -/
theorem retune_term (P : MarkedPackets D G n S) (a g : ℝ)
    (x : TestSpace D) (U : Config G n) (i : ℕ) :
    (retune P a).term x g U i = P.term x (a * g) U i := by
  cases he : P.packet i with
  | none => simp only [MarkedPackets.term, retune, he, Option.map_none]
  | some T =>
      simp only [MarkedPackets.term, retune, he, Option.map_some, scaleToken_read]
      rw [Complex.ofReal_mul, mul_zpow]
      ring

/-- The totalized identity holds for all real couplings, with every row
and every independent test retained. No summability premise is needed for
this termwise equality of the two identical series. -/
theorem retune_read [Fintype V] (P : MarkedPackets D G n S) (a g : ℝ)
    (x : TestSpace D) (U : Config G n) :
    (retune P a).read x g U = P.read x (a * g) U := by
  apply tsum_congr
  intro i
  exact congrArg (Poly.send (P.mode i)) (retune_term P a g x U i)

private def charge (P : MarkedPackets D G n S) (w : V → ℝ)
    (g width : ℝ) (v : V) (i : ℕ) : ℝ :=
  if v ∈ (P.mode i).val then
    match P.packet i with
    | none => 0
    | some T => Poly.toll w (P.mode i) * ‖(g : ℂ) ^ P.power i‖ *
        T.coin * Real.exp (width * T.fall)
  else 0

private theorem charge_retune (P : MarkedPackets D G n S) (a g : ℝ)
    (w : V → ℝ) (width : ℝ) (v : V) (i : ℕ) :
    charge (retune P a) w g width v i = charge P w (a * g) width v i := by
  unfold charge
  dsimp only [retune]
  split_ifs with hv
  · cases P.packet i with
    | none => simp only [Option.map_none]
    | some T =>
        simp only [Option.map_some]
        dsimp only [scaleToken]
        rw [Complex.ofReal_mul, mul_zpow, norm_mul]
        ring
  · rfl

/-- Actual Paid data transfer with the exact same budget, width, test
regions, addresses, rootwise sums and cover reserves. -/
theorem retune_paid (P : MarkedPackets D G n S) (a g : ℝ)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w (a * g) width budget coverOffset coverSlope) :
    (retune P a).Paid B address region w g width budget coverOffset coverSlope := by
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
  · intro i Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    refine ⟨mul_nonneg (norm_nonneg _) (hP.coefficient i T hT).1, ?_⟩
    intro x
    change (∑ j, ‖((a : ℂ) ^ P.power i) * T.gem j (testInclusion D x)‖) ≤
      ‖(a : ℂ) ^ P.power i‖ * T.coin
    simp only [norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((hP.coefficient i T hT).2 x) (norm_nonneg _)
  · intro i Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.paths i T hT
  · intro i Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.addresses i T hT
  · intro i Q hQ x U k
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    change (scaleToken ((a : ℂ) ^ P.power i) T).touch x
        (fun j => G.adjoint k (U j)) =
      (scaleToken ((a : ℂ) ^ P.power i) T).touch x U
    exact (scaleToken_touch ((a : ℂ) ^ P.power i) T x _).trans
      ((congrArg (fun z : ℂ => ((a : ℂ) ^ P.power i) * z)
        (hP.symmetry i T hT x U k)).trans
          (scaleToken_touch ((a : ℂ) ^ P.power i) T x U).symm)
  · intro i Q hQ j x y hxy
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact congrArg (fun z : ℂ => ((a : ℂ) ^ P.power i) * z)
      (hP.reads i T hT j x y hxy)
  · intro i Q hQ j
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact RG3.Held.Letter.cmul ((a : ℂ) ^ P.power i) (hP.multilinear i T hT j)
  · intro v
    convert hP.roots v using 1
    funext i
    dsimp only [retune]
    split_ifs
    · cases P.packet i with
      | none => simp only [Option.map_none]
      | some T =>
          simp only [Option.map_some]
          dsimp only [scaleToken]
          rw [Complex.ofReal_mul, mul_zpow, norm_mul]
          ring
    · rfl
  · intro i Q hQ
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp hQ
    exact hP.cover i T hT

variable (A : Run G) (N period start length : ℕ)

/-- The ratio uses two original positive couplings from one retained Run. -/
def actualRatio : ℝ :=
  regulatorRun A.family N period (start + length) /
    regulatorRun A.family N period start

def along (P : MarkedPackets D G n S) : MarkedPackets D G n S :=
  retune P (actualRatio A N period start length)

private theorem ratio_mul (hN : start + length ≤ N) :
    actualRatio A N period start length * regulatorRun A.family N period start =
      regulatorRun A.family N period (start + length) := by
  have hs : start ≤ N := by omega
  exact div_mul_cancel₀ _ (Weather.runs_pos A.family A.makes hs period).ne'

/-- This fixed ratio equals the nonlinear interval unit at the one actual
starting coupling. No equality of the two germs is asserted. -/
theorem actualRatio_eq_unit (hN : start + length ≤ N) :
    actualRatio A N period start length =
      NonAffineCouplingReset.unit
        (ActualRunCouplingComposition.betaGap A N period start length)
        (regulatorRun A.family N period start) := by
  have hs : start ≤ N := by omega
  have hc := Weather.runs_pos A.family A.makes hs period
  symm
  apply (eq_div_iff hc.ne').2
  simpa only [NonAffineCouplingReset.reset, mul_comm] using
    ActualRunCouplingComposition.reset_actual A N period start length hN

/-- Exact all-test re-expression of the original packet at the actual two
couplings. The packet still acts on the same full Config, without a mesh
or field-coordinate substitution. For the next step take length=1. -/
theorem along_read [Fintype V] (P : MarkedPackets D G n S)
    (hN : start + length ≤ N) (x : TestSpace D) (U : Config G n) :
    (along A N period start length P).read x
        (regulatorRun A.family N period start) U =
      P.read x (regulatorRun A.family N period (start + length)) U := by
  change (retune P (actualRatio A N period start length)).read x
    (regulatorRun A.family N period start) U = _
  rw [retune_read, ratio_mul A N period start length hN]

/-- The actual original Paid receipt supplies the retuned packet with no
vacuum-ratio or coupling-ratio loss in its budget. -/
theorem along_paid (P : MarkedPackets D G n S)
    (hN : start + length ≤ N)
    {B : BudgetPoint} {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {width budget : ℝ} {coverOffset coverSlope : ℕ}
    (hP : P.Paid B address region w
      (regulatorRun A.family N period (start + length))
      width budget coverOffset coverSlope) :
    (along A N period start length P).Paid B address region w
      (regulatorRun A.family N period start) width budget coverOffset coverSlope := by
  apply retune_paid
  simpa only [ratio_mul A N period start length hN] using hP

end YM.Integration.ActualRunPacketRetuning
end
