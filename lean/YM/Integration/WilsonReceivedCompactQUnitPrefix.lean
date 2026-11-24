import YM.Integration.WilsonReceivedCompactQUnitLedger
import YM.Integration.WilsonOriginalNullUnitSum

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQUnitPrefix
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {R:Run G} {N per b n:ℕ} {Ψ:∀i,RG.Rep G (R.family.side i per)}
  {O:Type} [Fintype O] {test:Test 3} {χ:Points 3 → O} {ε:ℝ} {fees:Fares}
  {y:Site (R.family.side (b+n) per)} {v:O → Values (Config G (R.family.side (b+n) per))}
local notation "w" => WilsonSeparatedOriginalThermometerCells.weight test χ
local notation "mass" => (∫x:Points 3,‖test x‖)
local notation "B₀" => max fees.regular fees.primary
variable {h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (R.family.labels.level 0) (R.family.side (b+n) per)}

def Priced (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h) :Prop :=
  let loans:=Classical.choose history
  let a:=fun o p=>Classical.choose (Classical.choose_spec (loans o p))
  let emitted:=fun j o=>if p:w o≠0 then a o p j else 0
  ∀ k ≤ n, (∑j∈Finset.range k,∑o,‖w o‖*‖emitted j o‖) ≤
    mass*ε*|B₀| *gain R.family (b+k) (b+n)*WilsonOriginalNullUnitSum.allowance

theorem original (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h)
    (ep:0 ≤ ε) :Priced history := by
  let loans:=Classical.choose history
  let a:=fun o p=>Classical.choose (Classical.choose_spec (loans o p))
  let emitted:=fun j o=>if p:w o≠0 then a o p j else 0
  let bill:=fun j=>∑o,‖w o‖*‖emitted j o‖
  have bill0 j:0 ≤ bill j:=Finset.sum_nonneg (fun o _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have normed j:‖(bill j:ℂ)‖=bill j:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (bill0 j)]
  have paid j (hj:j<n):bill j ≤ mass*(ε*gain R.family (b+j) (b+n)*|B₀|) :=
    (Classical.choose_spec history).2.2 j hj
  have funded j (hj:j<n):‖(bill j:ℂ)‖ ≤ ε*gain R.family (b+j) (b+n)*(mass*|B₀|) := by
    rw [normed]
    exact (paid j hj).trans_eq (by ring)
  intro k earlier
  calc
    (∑j∈Finset.range k,bill j) = ∑j∈Finset.range k,‖(bill j:ℂ)‖ := Finset.sum_congr rfl (fun j _=>(normed j).symm)
    _ ≤ ε*(mass*|B₀|)*gain R.family (b+k) (b+n)*WilsonOriginalNullUnitSum.allowance :=
      WilsonOriginalNullUnitSum.first_dates R.family earlier ep
        (mul_nonneg (integral_nonneg (fun _=>norm_nonneg _)) (abs_nonneg _)) (fun j=>(bill j:ℂ)) funded
    _ = _ := by ring

end YM.Integration.WilsonReceivedCompactQUnitPrefix
