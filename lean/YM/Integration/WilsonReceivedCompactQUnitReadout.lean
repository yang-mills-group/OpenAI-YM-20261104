import YM.Integration.WilsonReceivedQUnitPosterior
import YM.Integration.WilsonReceivedCompactQUnitPrefix

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQUnitReadout
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {O:Type} [Fintype O]

theorem tariff (w first:O → ℂ) (emit:ℕ → O → ℂ) (n:ℕ) :
    ‖∑o,w o*(first o+∑j∈Finset.range n,emit j o)‖ ≤
        (∑o,‖w o‖*‖first o‖)+(∑j∈Finset.range n,∑o,‖w o‖*‖emit j o‖) := by
  have expanded:(∑o,w o*(first o+∑j∈Finset.range n,emit j o))=
      (∑o,w o*first o)+(∑j∈Finset.range n,∑o,w o*emit j o) := by
    simp_rw [mul_add,Finset.mul_sum]
    rw [Finset.sum_add_distrib,Finset.sum_comm]
  rw [expanded]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simpa only [norm_mul] using norm_sum_le Finset.univ (fun o=>w o*first o)
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun o=>w o*emit j o)

variable {G:Gauge} (R:Run G) {N per m k:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin)
  (Ψ:∀i,RG.Rep G (R.family.side i per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
variable (test:Test 3) (χ:Points 3 → O) (b n:ℕ) (ε:ℝ) (fees:Fares)
  (y:Site (R.family.side (b+n) per)) (v:O → Values (Config G (R.family.side (b+n) per)))
local notation "w" => WilsonSeparatedOriginalThermometerCells.weight test χ
local notation "mass" => (∫x:Points 3,‖test x‖)
local notation "B₀" => max fees.regular fees.primary
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0

def Observed (h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (F₀) (R.family.side (b+n) per))
    (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h) :Prop :=
  let loans:=Classical.choose history
  let z:=fun o a=>Classical.choose (loans o a)
  let a:=fun o p=>Classical.choose (Classical.choose_spec (loans o p))
  let first:=fun o=>if p:w o≠0 then (projection (F₀) R.family.params (Ψ (b+n)).p.threshold y (h o p)) 0 else 0
  let emitted:=fun j o=>if p:w o≠0 then a o p j else 0
  let residual:=fun o U=>if p:w o≠0 then (z o p).density (WilsonReceivedQUnitHistory.address R (b+n) y b) (S₀) (Ψ b) U else 0
  let scalar:=∑o,w o*(first o+∑j∈Finset.range n,emitted j o)
  WilsonReceivedCompactQUnitPrefix.Priced history ∧
  WilsonReceivedQUnitPosterior.Viewed (N:=N) R Ψ b n
    (fun U=>test.applyTo (fun x=>(v (χ x)).withdrawn U-((Ψ (b+n)).eval U:ℂ)*(v (χ x)).filed U))
    (fun V=>∑o,w o*residual o V) scalar ∧
  ‖scalar‖ ≤ mass*(2+ε*WilsonOriginalNullUnitSum.allowance)*|B₀|

include course in
theorem original (h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (F₀) (R.family.side (b+n) per))
    (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h)
    (start:m ≤ b) (live:b+n ≤ N) (ep:0 ≤ ε) :
    Observed (N:=N) R Ψ test χ b n ε fees y v h history := by
  let loans:=Classical.choose history
  let z:=fun o a=>Classical.choose (loans o a)
  let a:=fun o p=>Classical.choose (Classical.choose_spec (loans o p))
  let first (o:O):=if p:w o≠0 then (projection (F₀) R.family.params (Ψ (b+n)).p.threshold y (h o p)) 0 else 0
  let emitted (j:ℕ) (o:O):=if p:w o≠0 then a o p j else 0
  let residual (o:O) (U:Config G (R.family.side b per)):=if p:w o≠0 then (z o p).density (WilsonReceivedQUnitHistory.address R (b+n) y b) (S₀) (Ψ b) U else 0
  have stable (o:O) (p:w o≠0):=(Classical.choose_spec (Classical.choose_spec (loans o p)))
  have earned (o:O):Integrable (residual o) (prior G _) := by
    by_cases p:w o≠0
    · simp only [residual,dif_pos p]
      exact ((z o p).envelope (S₀) (course.1.walk b start (by omega)).truep.valid (stable o p).2.1 (stable o p).1).integrableC _
    · simp only [residual,dif_neg p];simp
  have paid:Integrable (fun U=>∑o,w o*residual o U) (prior G _) := by
    apply integrable_finsetSum
    intro o _
    exact (earned o).const_mul (w o)
  have pref:=WilsonReceivedCompactQUnitPrefix.original history ep
  refine ⟨pref,WilsonReceivedQUnitPosterior.original R π Γ Ψ course b n start live _ _ _ (Classical.choose_spec history).1 paid,?_⟩
  have entry:= (Classical.choose_spec history).2.1
  have tail:=pref n (le_refl n)
  rw [gain_self,mul_one] at tail
  exact (tariff w first emitted n).trans ((add_le_add entry tail).trans_eq (by ring))

end YM.Integration.WilsonReceivedCompactQUnitReadout
