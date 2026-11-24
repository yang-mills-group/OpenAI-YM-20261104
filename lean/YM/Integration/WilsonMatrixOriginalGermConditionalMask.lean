import YM.Integration.WilsonMatrixOriginalGermMaskPanel
import YM.Integration.WilsonOriginalWardResponse

/-! At the date of the actual spring, the joint test is its original
conditional expectation. Its energy is taken after the whole signed
centered mesh has arrived from the UV cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermConditionalMask
open MeasureTheory Filter Lattice Wilson RG OPE.Therm PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.GridApprox FVA2
open WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermPanelRMS OriginalMarkedRunAction
open Comparison.RG02 IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Ticket WilsonLimitConstruction Pert.Asymptotics
open scoped BigOperators Classical
open private carried from YM.Integration.WilsonMatrixOriginalGermGram
open private tested from YM.Integration.WilsonMatrixOriginalGermMaskPanel
open private energy from YM.Integration.WilsonMatrixOriginalGermPanelRMS
variable {G:Gauge} (R:Run G) {m k N p:ℕ}

def response (lower:m≤k) (upper:k≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):Config G (R.family.side k p)→ℂ:=
  actualTransport R.family (N:=N) (panel R (lower.trans upper) v φ) upper

def cost (lower:m≤k) (upper:k≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):ℝ:=
  Real.sqrt (∫U,‖response R (p:=p) lower upper v φ U‖^2 ∂scene R.family.path N p k)

theorem entered (lower:m≤k) (upper:k≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):
    Envelope (response R (p:=p) lower upper v φ) ∧ ∀U:Config G (R.family.side k p),
      ((R.family.path.rep N p k).eval U:ℂ)*response R lower upper v φ U=raw R upper (panel R (lower.trans upper) v φ) U:=
  ⟨carried R (le_refl N) (tested R (lower.trans upper) v φ) upper,denominator R upper _⟩

theorem measured (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W) {δ:ℝ}
    (pos:0≤δ) (income:(∫V,‖W V‖^2 ∂scene R.family.path N p k)≤δ^2) (v:Fin 2→R.family.label 4) (φ:Test 2):
    bill R lower upper W v φ=(∫V,response R lower upper v φ V*W V ∂scene R.family.path N p k) ∧
      ‖bill R lower upper W v φ‖≤cost R (p:=p) lower upper v φ*δ:=by
  let μ:=scene R.family.path N p k
  let H:=panel R (p:=p) (lower.trans upper) v φ
  let T:=response R (p:=p) lower upper v φ
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson upper
  have t:Envelope T:=(entered R lower upper v φ).1
  have h:bill R lower upper W v φ=∫V,T V*W V ∂μ:=by
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun U=>mul_comm _ _)) ?_
    exact (WilsonExteriorWardEquations.adjoint R.family p R.makes hW upper (le_refl N) H (tested R _ v φ)).symm
  refine ⟨h,?_⟩
  rw [h]
  exact (norm_integral_le_integral_norm _).trans
    (spring_mask_spectator W T hW.meas.aestronglyMeasurable t.meas.aestronglyMeasurable (energy μ hW)
      (energy μ t) pos income).2

def Sale (j N:ℕ) (upper:j≤N) (Z:SeriesA G) (σ C:ℝ) (r q:ℕ) (ε:ℝ):Prop:=
  WilsonMatrixOriginalGermMaskPanel.Returned R j N upper Z σ C r q ε ∧
    ∀p (x:Site (R.family.side j p)) m (lower:m≤j) (v:Fin 2→R.family.label 4) (φ:Test 2),
      let g:=regulatorRun R.family N p j
      let W:=fun U=>((maskedSpringAt R N p j r Z σ C g x U-springAt R N p j r Z g x U:ℝ):ℂ)
      let paid:=bill R lower upper W v φ
      paid=(∫U,response R lower upper v φ U*W U ∂scene R.family.path N p j) ∧
        ‖paid‖≤cost R (p:=p) lower upper v φ*(ε*g^q)

theorem purchased (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit) (heat:Poetry R.family.path.levels)
    (v:ℕ→Gear G→ℝ) (rows:FundedMarkedCoverRows.prices v R.kit) (credit:Credit) (d M r q:ℕ) {ε:ℝ} (ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ i:ℕ in atTop,let j:=i+1
      let C:=credit.buy (zz V j)+zz V j*V.clock.loopCap j
      ∀N,∀upper:j<N,∀σ,0<σ→σ⁻¹≤zz V j→∀Z:SeriesA G,Draw Z σ C→Z.length≤M→
        (∀a∈Z,0<a.grade)→(∀a∈Z,a.grade≤d)→Sale R j N upper.le Z σ C r q ε:=by
  intro V
  filter_upwards [WilsonMatrixOriginalGermMaskPanel.purchased R simple slow heat v rows credit d M r q ep,
    cofinal_spring_mask_budget R simple slow heat v rows credit d M r,
    cofinal_spring_mask_return R simple slow heat v rows credit d M r q ep] with i old bounded earned
  intro j C N upper σ sp wide Z draw len lo hi
  refine ⟨old N upper σ sp wide Z draw len lo hi,?_⟩
  intro p x m lower marks φ g W paid
  obtain ⟨meas,cap,-⟩:=bounded N upper σ sp wide Z draw len lo hi p x
  have eW:Envelope W:=(show Envelope (fun U=>maskedSpringAt R N p j r Z σ C g x U-springAt R N p j r Z g x U)
    from ⟨meas,_,cap⟩).ofReal_env
  have inc:=(earned N upper σ sp wide Z draw len lo hi p x j (le_refl j)).2.2.2.1
  rw [actualTransport_base R.family R.makes upper.le] at inc
  exact measured R lower upper.le W eW (mul_nonneg ep.le (pow_nonneg
    (IterationFour.Currency.g_pos R.makes N p j upper.le).le _)) inc marks φ

end YM.Integration.WilsonMatrixOriginalGermConditionalMask
