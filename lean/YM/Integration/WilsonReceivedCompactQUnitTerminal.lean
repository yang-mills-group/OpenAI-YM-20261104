import YM.Integration.WilsonReceivedQUnitCompulsory

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQUnitTerminal
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {O:Type} [Fintype O]
variable {G:Gauge} (R:Run G) {N per m k:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin)
  (Ψ:∀i,RG.Rep G (R.family.side i per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
variable (test:Test 3) (χ:Points 3 → O) (b n:ℕ) (ε:ℝ) (fees:Fares)
  (y:Site (R.family.side (b+n) per)) (v:O → Values (Config G (R.family.side (b+n) per)))
local notation "w" => WilsonSeparatedOriginalThermometerCells.weight test χ
local notation "mass" => (∫x:Points 3,‖test x‖)
local notation "B₀" => max fees.regular fees.primary
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0


def Signed (h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (F₀) (R.family.side (b+n) per))
    (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h) :Prop :=
  let loans:=Classical.choose history
  let z:=fun o a=>Classical.choose (loans o a)
  let a:=fun o p=>Classical.choose (Classical.choose_spec (loans o p))
  let first:=fun o=>if p:w o≠0 then (projection (F₀) R.family.params (Ψ (b+n)).p.threshold y (h o p)) 0 else 0
  let emitted:=fun j o=>if p:w o≠0 then a o p j else 0
  let scalar:=∑o,w o*(first o+∑j∈Finset.range n,emitted j o)
  let hard:=fun o U=>if p:w o≠0 then WilsonMeasuredCoefficientTransport.account (z o p) (Ψ b) U else 0
  WilsonReceivedCompactQUnitReadout.Observed (N:=N) R Ψ test χ b n ε fees y v h history ∧
  Integrable (fun U=>∑o,w o*hard o U) (prior G _) ∧
  WilsonReceivedQUnitCompulsory.Heard (N:=N) R Ψ n
    (fun U=>test.applyTo (fun x=>(v (χ x)).withdrawn U-((Ψ (b+n)).eval U:ℂ)*(v (χ x)).filed U))
    (fun U=>∑o,w o*hard o U) scalar (mass*(2*gain R.family b (b+n)*|B₀|))

include course in
theorem original [MeasurableSpace O] [MeasurableSingletonClass O] (simple:G.Simple) (measured:Measurable χ)
    (h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (F₀) (R.family.side (b+n) per))
    (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h)
    (start:m ≤ b) (live:b+n ≤ N) (ep:0 ≤ ε) (cofinal:WilsonReceivedQUnitCompulsory.onset R simple ≤ b) :
    Signed (N:=N) R Ψ test χ b n ε fees y v h history := by
  let loans:=Classical.choose history
  let z:=fun o a=>Classical.choose (loans o a)
  let revenue:=2*gain R.family b (b+n)*|B₀|
  have gp:0 ≤ gain R.family b (b+n):=(Real.exp_pos _).le
  have rp:0 ≤ revenue:=mul_nonneg (mul_nonneg (by norm_num) gp) (abs_nonneg _)
  let d (o:O) (U:Config G (R.family.side b per)):=if p:w o≠0 then (z o p).density (WilsonReceivedQUnitHistory.address R (b+n) y b) (S₀) (Ψ b) U else 0
  let hard (o:O) (U:Config G (R.family.side b per)):=if p:w o≠0 then WilsonMeasuredCoefficientTransport.account (z o p) (Ψ b) U else 0
  let soft:=fun o U=>((Ψ b).eval U)⁻¹ • (d o U-hard o U)
  have stable (o:O) (p:w o≠0):=(Classical.choose_spec (Classical.choose_spec (loans o p)))
  have paid (o:O):Integrable (d o) (prior G _) ∧ Integrable (hard o) (prior G _) ∧ ∀U,‖soft o U‖ ≤ revenue := by
    by_cases p:w o≠0
    · have sale:=WilsonReceivedQUnitCompulsory.row R π Γ Ψ course simple cofinal start (by omega) _ (z o p)
        (stable o p).1 (stable o p).2.1 (stable o p).2.2.1
      simp only [d,hard,soft,dif_pos p]
      refine ⟨sale.1,sale.2.1,fun U=>(sale.2.2 U).trans ?_⟩
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (by norm_num) gp)
    · simpa only [d,hard,soft,dif_neg p,sub_self,smul_zero,norm_zero] using
        (show Integrable (fun _:Config G (R.family.side b per)=>(0:ℂ)) (prior G _) ∧
          Integrable (fun _:Config G (R.family.side b per)=>(0:ℂ)) (prior G _) ∧
          ∀_:Config G (R.family.side b per),0 ≤ revenue from ⟨by simp,by simp,fun _=>rp⟩)
  have intD:Integrable (fun U=>∑o,w o*d o U) (prior G _) := by
    apply integrable_finsetSum;intro o _;exact (paid o).1.const_mul _
  have intK:Integrable (fun U=>∑o,w o*hard o U) (prior G _) := by
    apply integrable_finsetSum;intro o _;exact (paid o).2.1.const_mul _
  have observed:=WilsonReceivedCompactQUnitReadout.original R π Γ Ψ course test χ b n ε fees y v h history start live ep
  refine ⟨observed,intK,WilsonReceivedQUnitCompulsory.terminal R π Γ Ψ course n start live _ _ _ _ observed.2.1 intD intK ?_⟩
  intro U
  have same:((Ψ b).eval U)⁻¹ • ((∑o,w o*d o U) - ∑o,w o*hard o U)=∑o,w o*soft o U := by
    simp only [soft,Complex.real_smul]
    rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun o _=>by ring)
  rw [same]
  apply (norm_sum_le _ _).trans
  simp_rw [norm_mul]
  exact WilsonReceivedCompactQUnitLedger.fee test χ measured revenue rp (fun o=>soft o U) (fun o=>(paid o).2.2 U)

end YM.Integration.WilsonReceivedCompactQUnitTerminal
