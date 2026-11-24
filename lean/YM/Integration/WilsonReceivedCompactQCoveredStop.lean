import YM.Integration.WilsonReceivedQCoveredPosterior
import YM.Integration.WilsonReceivedQUpperSoft
import YM.Integration.WilsonReceivedCompactCoveredCells

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQCoveredStop
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


open Filter MergeProof.Accent RG3.Law OPE.Therm Extra.Trajectories Extra.Histories Trace.Physical.GermGraph
open WilsonReceivedQUpperSoft
def Earlier (h:∀o:O,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → Coefficient (F₀) (R.family.side (b+n) per))
    (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h) :Prop :=
  let loans:=Classical.choose history
  let z:=fun o a=>Classical.choose (loans o a)
  let a:=fun o p=>Classical.choose (Classical.choose_spec (loans o p))
  let first:=fun o=>if p:w o≠0 then (projection (F₀) R.family.params (Ψ (b+n)).p.threshold y (h o p)) 0 else 0
  let emitted:=fun j o=>if p:w o≠0 then a o p j else 0
  let scalar:=∑o,w o*(first o+∑j∈Finset.range n,emitted j o)
  let hard:=fun o U=>if p:w o≠0 then WilsonMeasuredCoefficientTransport.account (z o p) (Ψ b) U else 0
  ∀u (ub:u ≤ b),(∫V,‖actualTransport R.family (N:=N) (named R Ψ test χ (b+n) v) (ub.trans (Nat.le_add_right b n)) V-
    actualTransport R.family (N:=N) (fun U=>((Ψ b).eval U)⁻¹ • (∑o,w o*hard o U)) ub V-scalar‖ ∂scene R.family.path N per u) ≤
      mass*(|fees.earlier|+2*gain R.family b (b+n)*|B₀|+|fees.primary|+|fees.regular|)

include course in
theorem original [MeasurableSpace O] [MeasurableSingletonClass O] (simple:G.Simple) (measured:Measurable χ)
    (h:∀o:O,w o≠0 → Coefficient (F₀) (R.family.side (b+n) per))
    (bought:∀o p,Paid (N:=N) R (Ψ (b+n)) fees y (v o) (h o p))
    (history:WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y v h)
    (paid:WilsonReceivedCompactQUnitTerminal.Signed (N:=N) R Ψ test χ b n ε fees y v h history)
    (start:m ≤ b) (live:b+n ≤ N) : Earlier (N:=N) R Ψ test χ b n ε fees y v h history := by
  let t:=b+n
  let W:=Ψ t
  let realW:=R.family.path.rep N per t
  let raw:=row R Ψ test χ t v
  let K:=forced R Ψ test χ t h
  let advertised:=named R Ψ test χ t v
  let f:=fun U=>(W.eval U)⁻¹ • raw U
  let soft:=fun U=>(W.eval U)⁻¹ • (raw U-K U)
  let seam:=fun U=>advertised U-K U/(W.eval U:ℂ)
  have top:=WilsonReceivedQUpperSoft.original R π Γ Ψ course test χ t fees y v simple measured h bought (by omega) live
  have originalSeam:=WilsonReceivedCompactCoveredCells.original R live test χ measured W v fees (fun _=>y) h bought
  have env:RG.Envelope seam:=originalSeam.2.1
  have payout:W.eval=realW.eval:=(course.1.walk t (by omega) live).view
  have cancel (a:Config G (R.family.side t per) → ℂ):(fun U=>realW.eval U • ((W.eval U)⁻¹ • a U))=a := by
    funext U
    have nv:realW.eval U≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
    rw [payout,smul_smul,mul_inv_cancel₀ nv,one_smul]
  have wf:Integrable (fun U=>realW.eval U • f U) (prior G _):=(cancel raw).symm ▸ top.1
  have ws:Integrable (fun U=>realW.eval U • soft U) (prior G _):=(cancel (raw-K)).symm ▸ top.1.sub top.2.1
  obtain ⟨cap,bound⟩:=env.cost
  have wz:Integrable (fun U=>realW.eval U • seam U) (prior G _) := by
    simpa only [Complex.real_smul,liftVac] using
      (vac_integrable R.family.path N per t R.makes.wilson live).mul_bdd env.meas.aestronglyMeasurable (ae_of_all _ bound)
  have identifies:f+seam-soft=advertised:=by
    funext U
    change (W.eval U)⁻¹ • raw U+(advertised U-K U/(W.eval U:ℂ))-(W.eval U)⁻¹ • (raw U-K U)=advertised U
    rw [Complex.real_smul,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv]
    ring
  intro u ub
  have result:=WilsonReceivedQCoveredPosterior.original R live (Nat.le_add_right b n) ub f seam soft _ _
    (mass*|fees.earlier|) (mass*(2*gain R.family b t*|B₀|)) (mass*(|fees.primary|+|fees.regular|))
    wf wz ws top.2.2 (paid.2.2 u ub) (originalSeam.2.2 u (ub.trans (Nat.le_add_right b n)))
  rw [identifies] at result
  exact result.trans_eq (by ring)

end YM.Integration.WilsonReceivedCompactQCoveredStop
