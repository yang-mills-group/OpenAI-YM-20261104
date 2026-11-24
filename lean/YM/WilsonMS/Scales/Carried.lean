import YM.WilsonMS.Scales.ScaleMS
import YM.WilsonMS.Scales.ParityCoupling
/-!
# Finite continuum measurement grounds

At all horizons nested. Unique changes near the free comparison: because
both arrays solve *real* finite equations, not from a stripped
coefficientwise identity alone. Applies at the continuum end of eqX, on the
whole point and profile scope.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.GFlow
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries (coeff mk X C constantCoeff invOfUnit)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates FrameX Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d k n m j : ℕ} {S T : ChartK G d} {F H : Reports G d}
local notation "BΨ" => Ensure.deck G

abbrev Marked (P : ChartK G d) (F : Reports G d) :=
  ∀ n, FundsK (P n) F

lemma Marked.unique (h : Marked S F) (hp : Marked T H) (hv : Equad S T) : F = H := by
  funext n k
  ext1 p
  ext1 t
  rw [(h k n t).2 p, (hp k n t).2 p]
  apply Test.apply_eq
  intro x hx
  dsimp only
  rw [hv k hx]

/-- These are in common X normalization, ready for common coupling demand -/
def BasisTest (V : Store G) (P : ChartK G d) :=
  ∃ F : Reports G d,
    Marked P F ∧
      F 0 = reference G d ∧
        ∀ i, (V.measure d).D (F i) = if i = 0 then (V.measure d).D (reference G d) else 0
variable {R : Guard G d}
section unique
variable (V : Store G)

lemma BasisTest.unique (hx : Equad (Act S R) T) (ht : BasisTest V S) (h : BasisTest V T)
    (hp : CloseP R) : R = 1 := by
  obtain ⟨F, hF, hF', he⟩ := ht
  obtain ⟨G', hG, hG', hc⟩ := h
  obtain ⟨A, hA⟩ := hp.1.actions
  have hP : Marked (Act S R) (realm R F) := fun i => FrameConj.pivotFund (hF i) R
  have hK := Marked.unique hP hG hx
  have hU : (V.measure d).Solved A F := by
    rw [hA] at hK
    intro i
    rw [hK]
    exact hc i
  have hP : (V.measure d).Solved 0 F := fun i => by
    rw [deck0, Normalize.author]
    exact he i
  have hh : A 0 = 0 := by
    have hp := hp.2
    rw [hA, const_deck] at hp
    apply Subtype.ext
    ext1 p
    exact add_left_cancel (show p + _ = p + _ from (DFunLike.congr_fun hp p).trans (add_zero p).symm)
  have hi : Injective (slope (V.measure d) (A 0) (F 0)) := by
    rw [hh, hF']
    exact fun v p h => by rwa [regular _ (V.prepared d), regular _ (V.prepared d)] at h
  rw [hA, (V.measure d).shift_unique F _ _ hh hU hP hi, deck0]

lemma BasisTest.forcing {A : ChartK G d} {W : Guard G d} (hS : Equad (Act A R) S)
    (hT : Equad (Act A W) T) (ht : BasisTest V S) (h : BasisTest V T) (hp : CloseP R)
    (hv : CloseP W) : R = W := by
  let T' := vault R * W
  have he : Equad (Act S T') T := by
    obtain he := hS.symm.act T'
    rw [action_times, ← mul_assoc R (vault R) W, (antidote hp).1, one_mul] at he
    exact he.trans hT
  have hM : vault R * W = 1 := BasisTest.unique V he ht h (hp.invert.times hv)
  calc
    _ = R * (vault R * W) := by rw [hM, mul_one]
    _ = _ := by rw [← mul_assoc, (antidote hp).1, one_mul]

lemma BasisTest.styled (hx : BasisTest V S) {p : Cn} (ht : Aware p) : BasisTest V (Sub p S) := by
  obtain ⟨F, hF, he, hV⟩ := hx
  let P := substitute p F
  refine ⟨P, fun n => FundSwim (hF n) _, pay0 _ _ |>.trans he, ?_⟩
  let T := (V.measure d)
  intro i
  by_cases hp : i = 0
  · subst i
    rw [show P 0 = F 0 from pay0 p F]
    exact hV _
  unfold P
  rw [if_neg hp, rules, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hq : j = 0
  · subst j
    rw [cut, pow_zero, PowerSeries.coeff_one, if_neg hp, zero_smul, map_zero]
  rw [Clean.payment ht.clean j i,
    show ∀ (x : ℝ) (A : Prediction G d), (x : ℂ) • A = x • A from fun x A =>
      IsScalarTower.algebraMap_smul ℂ x A,
    map_smul, hV j, if_neg hq, smul_zero]
end unique
section thaw
variable {M : Booked (Ensure.deck G)} (F : MS_Data G M) (V : Store G) (r : ℝ) (d : ℕ)

def KnotMS :=
  deck (Lμ V F r d)

lemma KnotBase : Lμ V F r d 0 = 0 := by
  unfold Lμ
  rw [leads, free_match, pass_free]

lemma preparedK : (V.survey d).Executed (V.prepared d) (fun i => Continuum F r i d) :=
  baseGood _ _ (free_match ..)

lemma knot_base : CloseP (KnotMS F V r d) := by
  refine ⟨(preparedK F V r d).1, ?_⟩
  rw [KnotMS, const_deck, KnotBase, stand0]

lemma allocated : BasisTest V (Act (GMS F r d) (KnotMS F V r d)) := by
  refine ⟨thawed V F r d, fun n => FrameConj.Gates.theorem_F V r F d n, ?_, (preparedK F V r d).2.1⟩
  rw [thawed, Normalize.rest, PowerSeries.coeff_zero_eq_constantCoeff_apply, const_deck, KnotBase,
    stand0, free_match]
  rfl
end thaw
section modality
variable {M : Booked (Ensure.deck G)} {F : MS_Data G M} {V : Store G} (P : Rose.Pick V) {r : ℝ}
  {W : Initialize G}

def ΨScheme (P : Rose.Pick V) (F : MS_Data G M) (d : ℕ) : ChartK G d := fun _ x => softK P F 0 d x

abbrev ψW (P : Rose.Pick V) (F : MS_Data G M) :=
  Counter (χMS 0 P F)

lemma fitted (F : MS_Data G M) (d : ℕ) : Marked (ΨScheme P F d) (softX P F 0 d) := fun n =>
  SoftK_funds P F 0 n d
variable (hG : G.Simple) {X : Prescription (Ensure.deck G)} (hp : Installed W F X) (hh : Commuting X)
include hG hp hh

lemma awareχ (r : ℝ) : Aware (χMS r P F) :=
  ⟨built0 .., trueFirst r P W X F hG hp hh, cleanχ r P W X F hG hp hh⟩

lemma ψ_aware : Aware (ψW P F) :=
  (awareχ P hG hp hh 0).counter

lemma take_ψ (r : ℝ) (d : ℕ) :
    Equad (ΨScheme P F d) (GFlow.Sub (Counter (χMS r P F)) (Act (GMS F r d) (KnotMS F V r d))) := by
  intro n x hx
  funext i
  exact k_clock P W X F 0 hG hp hh r d x hx i

lemma ψCert (d : ℕ) : BasisTest V (ΨScheme P F d) :=
  BasisTest.styled _ (allocated F V 0 d) (ψ_aware P hG hp hh)

lemma watches : FrameConj.observed P ((ΨScheme P F 6) 3) = PowerSeries.X := by
  change FrameConj.observed P (Sub (ψW P F) (Act (GMS F 0 6) (KnotMS F V 0 6)) 3) = _
  obtain he :=
    ob_sub (P' := Act (GMS F 0 6) (KnotMS F V 0 6)) (X' := FrameConj.Gates.thawed V F 0 6) P (A :=
      ψW P F) (Ice.born _) (FrameConj.Gates.theorem_F V 0 F 6 3)
  apply he.trans
  exact
    counter_l (built0 P _)
      (show coeff 1 (χMS 0 P F) ≠ 0 from
        by
        rw [trueFirst 0 P W X F hG hp hh]
        norm_num)

abbrev transit (P : Rose.Pick V) (F : MS_Data G M) (t : ℝ) :=
  PowerSeries.subst (ψW P F) (χMS (-t) P F)

lemma flowAware (t : ℝ) : Aware (transit P F t) :=
  Aware.extend (awareχ P hG hp hh (-t)) (ψ_aware P hG hp hh)
end modality
end YM.WilsonMS.GFlow
