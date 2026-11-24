import YM.Integration.WilsonReceivedQUnitHistory
import YM.Integration.WilsonReceivedCompactPlacedStep

/-! A signed relative profile tests the compensated densities on the same actual earlier Wilson law.
The initial scalar, the dated scalar feeds and the remaining physical null densities keep their original weights. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQUnitLedger
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {m N per k:ℕ}
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j,Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
local notation "C₀" => R.family
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
variable {O:Type} [Fintype O]

theorem linear (b n:ℕ) (w:O → ℂ) (f:O → Config G (R.family.side (b+n) per) → ℂ)
    (integrals:∀o, Integrable (f o) (prior G _)) :
    flow (C₀) 0 N per b n (fun U=>∑o,w o*f o U)=fun U=>∑o,w o*flow (C₀) 0 N per b n (f o) U := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change flow (C₀) 0 N per b n (GermGraph.transition (C:=(C₀)) 0 N per (b+n) _) = _
    exact (congrArg (flow (C₀) 0 N per b n) (WilsonReceivedCompactPlacedStep.linear (N:=N) (i:=b+n) R w f integrals)).trans
      (ih _ (fun o=>WilsonOriginalNullCorridor.integrable (C₀) 0 N per (integrals o)))

variable [MeasurableSpace O] [MeasurableSingletonClass O] (test:Test 3) (χ:Points 3 → O) (measured:Measurable χ)
local notation "w" => WilsonSeparatedOriginalThermometerCells.weight test χ
local notation "mass" => (∫x:Points 3,‖test x‖)
variable (b n:ℕ) (ε:ℝ) (fees:Fares) (y:Site (R.family.side (b+n) per)) (v:O → Values (Config G (R.family.side (b+n) per)))
local notation "B₀" => max fees.regular fees.primary

def Integrated (h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (F₀) (R.family.side (b+n) per)) :Prop :=
  ∃ loans:∀o a,WilsonReceivedQUnitHistory.Returned (N:=N) R Ψ b n ε y (v o) fees (h o a),
    let z:=fun o a=>Classical.choose (loans o a)
    let a:=fun o p=>Classical.choose (Classical.choose_spec (loans o p))
    let first:=fun o=>if p:w o≠0 then ((projection (F₀) R.family.params (Ψ (b+n)).p.threshold y (h o p)) 0) else 0
    let emitted:=fun j o=>if p:w o≠0 then a o p j else 0
    let residual:=fun o U=>if p:w o≠0 then (z o p).density (WilsonReceivedQUnitHistory.address R (b+n) y b) (S₀) (Ψ b) U else 0
    (flow (C₀) 0 N per b n (fun U=>test.applyTo (fun x=>(v (χ x)).withdrawn U-((Ψ (b+n)).eval U:ℂ)*(v (χ x)).filed U)) =
      fun U=>(∑o,w o*residual o U)+(∑o,w o*(first o+∑j∈Finset.range n,emitted j o))*((Ψ b).eval U:ℂ)) ∧
    (∑o,‖w o‖*‖first o‖) ≤ mass*(2*|B₀|) ∧
    (∀j<n,(∑o,‖w o‖*‖emitted j o‖) ≤ mass*(ε*gain (C₀) (b+j) (b+n)*|B₀|))



include measured in
theorem fee (E:ℝ) (ep:0 ≤ E) (a:O → ℂ) (bound:∀o,‖a o‖ ≤ E) :
    (∑o,‖w o‖*‖a o‖) ≤ mass*E := by
  calc
    _ ≤ ∑o:O,‖w o‖*E := Finset.sum_le_sum (fun o _=>mul_le_mul_of_nonneg_left (bound o) (norm_nonneg _))
    _ = (∑o:O,‖w o‖)*E := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalThermometerCells.variation test χ measured) ep

include course measured in
theorem original (h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (F₀) (R.family.side (b+n) per))
    (floor:m ≤ b) (live:b+n ≤ N) (ep:0 ≤ ε)
    (spent:∀o a,Paid (N:=N) R (Ψ (b+n)) fees y (v o) (h o a))
    (split:∀o a,WilsonReceivedCompactQUnitSplit.Split R (Ψ (b+n)) y (h o a) (B₀))
    (gates:∀j<n,∀site,Filed (C₀) 0 N per (b+j) Ψ site ε) :
    Integrated (N:=N) R Ψ test χ b n ε fees y v h := by
  let loans o a:=WilsonReceivedQUnitHistory.original R π Γ Ψ course b n ε floor live fees y (v o) (h o a) (spent o a) (split o a) gates
  refine ⟨loans,?_⟩
  let z o a:=Classical.choose (loans o a)
  let feeds o a:=Classical.choose (Classical.choose_spec (loans o a))
  let first (o:O) := if p:w o≠0 then ((projection (F₀) R.family.params (Ψ (b+n)).p.threshold y (h o p)) 0) else 0
  let emitted (j:ℕ) (o:O) := if p:w o≠0 then feeds o p j else 0
  let residual (o:O) (U:Config G (R.family.side b per)):=if p:w o≠0 then (z o p).density (WilsonReceivedQUnitHistory.address R (b+n) y b) (S₀) (Ψ b) U else 0
  let inlet (o:O) (U:Config G (R.family.side (b+n) per)):=if w o≠0 then (v o).withdrawn U-((Ψ (b+n)).eval U:ℂ)*(v o).filed U else 0
  let issued o p:=Classical.choose_spec (Classical.choose_spec (loans o p))
  have law:=(course.1.walk (b+n) (by omega) live).truep.valid
  have safe (o:O):Integrable (inlet o) (prior G _) := by
    by_cases p:w o≠0
    · have eq:inlet o=(h o p).density y (S₀) (Ψ (b+n)):=by
        funext U
        simpa only [inlet,if_pos p] using ((spent o p).2.2.2.1 U).symm
      rw [eq]
      exact ((h o p).envelope (S₀) law (spent o p).2.1 (spent o p).1).integrableC _
    · simp only [inlet,if_neg p];simp
  have main:(fun U=>test.applyTo (fun x=>(v (χ x)).withdrawn U-((Ψ (b+n)).eval U:ℂ)*(v (χ x)).filed U))=fun U=>∑o,w o*inlet o U := by
    funext U
    refine (WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>(v o).withdrawn U-((Ψ (b+n)).eval U:ℂ)*(v o).filed U)).trans ?_
    apply Finset.sum_congr rfl
    intro o _
    by_cases p:w o≠0
    · simp only [inlet,if_pos p]
    · simp only [inlet,if_neg p,not_ne_iff.mp p,zero_mul]
  constructor
  · change flow (C₀) 0 N per b n _= fun U=>(∑o,w o*residual o U)+(∑o,w o*(first o+∑j∈Finset.range n,emitted j o))*((Ψ b).eval U:ℂ)
    rw [main,linear R b n w inlet safe]
    funext U
    rw [Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    by_cases p:w o≠0
    · have same:flow (C₀) 0 N per b n (inlet o) U=residual o U+(first o+∑j∈Finset.range n,emitted j o)*((Ψ b).eval U:ℂ) := by
        simpa only [inlet,if_pos p,residual,dif_pos p,first,emitted,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
          congrFun (issued o p).2.2.2.2.2 U
      rw [same,mul_add,mul_assoc]
    · simp only [not_ne_iff.mp p,zero_mul,zero_add]
  · constructor
    · apply fee test χ measured (2*|B₀|) (by positivity) first
      intro o
      by_cases p:w o≠0
      · simp only [first,dif_pos p]
        exact ((issued o p).2.2.2.1).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
      · simp only [first,dif_neg p,norm_zero];positivity
    · intro j hj
      have rate:0 ≤ ε*gain (C₀) (b+j) (b+n) := mul_nonneg ep (Real.exp_pos _).le
      apply fee test χ measured _ (mul_nonneg rate (abs_nonneg _)) (emitted j)
      intro o
      by_cases p:w o≠0
      · simpa only [emitted,dif_pos p] using ((issued o p).2.2.2.2.1 j hj).trans (mul_le_mul_of_nonneg_left (le_abs_self _) rate)
      · simp only [emitted,dif_neg p,norm_zero];exact mul_nonneg rate (abs_nonneg _)

end YM.Integration.WilsonReceivedCompactQUnitLedger
