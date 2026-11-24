import YM.Integration.WilsonMatrixOriginalGermPanelRMS

/-! The original masked and unmasked spring hearings on the full submitted
two-mark mesh differ by an all-orders factor times one true centered UV
second moment. The order and tolerance are fixed before the cutoff, period,
site, masked series and both observed labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermMaskPanel
open MeasureTheory Filter Lattice Wilson RG OPE.Therm PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.GridApprox FVA2
open WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermSpringHearing WilsonMatrixOriginalGermSpringPanel
open WilsonMatrixOriginalGermPanelRMS OriginalMarkedRunAction
open Comparison.RG02 IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Ticket WilsonLimitConstruction Pert.Asymptotics
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {m k N p:ℕ}

private theorem tested (l:m≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):Envelope (panel R (p:=p) l v φ):=by
  let X:=fun (x:Fin 2→Site (R.family.side N p)) (i:Fin 2)=>source R l (v i) x i
  have ex (x i):Envelope (X x i):=Envelope.compactC (R.family.continuousO ..)
  have per (x):Envelope (centered R (X x 0) (X x 1)):=
    (((ex x 0).subC (Envelope.constC _)).mulC ((ex x 1).subC (Envelope.constC _))).subC (Envelope.constC _)
  exact Envelope.sumC Finset.univ _ (fun x _=>(Envelope.constC (WilsonExternalMeshMass.charge R.family φ x)).mulC (per x))

private theorem derivative (lower:m≤k) (upper:k≤N) {W:Config G (R.family.side k p)→ℂ} (hW:Envelope W)
    (v:Fin 2→R.family.label 4) (φ:Test 2):HasDerivAt (hearing R lower upper W v φ) (bill R lower upper W v φ) 0:=
  (WilsonMatrixOriginalGermSpringPanel.measured R lower upper W hW.cost.choose hW.meas hW.cost.choose_spec
    (fun x:Fin 2→Site (R.family.side N p)=>WilsonExternalMeshMass.charge R.family φ x)
    (fun x=>source R (lower.trans upper) (v 0) x 0) (fun x=>source R (lower.trans upper) (v 1) x 1)
    (fun _=>Envelope.compactC (R.family.continuousO ..)) (fun _=>Envelope.compactC (R.family.continuousO ..))).1

theorem change (lower:m≤k) (upper:k≤N) (A B W:Config G (R.family.side k p)→ℂ) (eA:Envelope A) (eB:Envelope B)
    (eW:Envelope W) (eq:B=A+W) {δ:ℝ} (pos:0≤δ) (income:(∫U,‖W U‖^2 ∂scene R.family.path N p k)≤δ^2)
    (v:Fin 2→R.family.label 4) (φ:Test 2):
    HasDerivAt (fun t=>hearing R lower upper B v φ t-hearing R lower upper A v φ t) (bill R lower upper W v φ) 0 ∧
      ‖bill R lower upper W v φ‖≤rms R (p:=p) (lower.trans upper) v φ*δ:=by
  have Y:=tested R (p:=p) (lower.trans upper) v φ
  letI:IsProbabilityMeasure (scene R.family.path N p N):=probability R.makes.wilson (le_refl N)
  have sum:bill R lower upper B v φ=bill R lower upper A v φ+bill R lower upper W v φ:=by
    unfold bill
    rw [eq,backTo_add R.family.path N p upper eA eW]
    simp only [Pi.add_apply,add_mul]
    exact integral_add (((backTo_env R.family.path N p upper eA).mulC Y).integrableC _)
      (((backTo_env R.family.path N p upper eW).mulC Y).integrableC _)
  have effect:=(derivative R lower upper eB v φ).sub (derivative R lower upper eA v φ)
  rw [sum,add_sub_cancel_left] at effect
  exact ⟨effect,(WilsonMatrixOriginalGermPanelRMS.measured R lower upper W eW pos income v φ).2⟩

def Returned (j N:ℕ) (upper:j≤N) (Z:SeriesA G) (σ C:ℝ) (r q:ℕ) (ε:ℝ):Prop:=
  ∀p (x:Site (R.family.side j p)) m (lower:m≤j) (v:Fin 2→R.family.label 4) (φ:Test 2),
    let g:=regulatorRun R.family N p j
    let S:=fun U=>springAt R N p j r Z g x U
    let M:=fun U=>maskedSpringAt R N p j r Z σ C g x U
    let W:=fun U=>((M U-S U:ℝ):ℂ)
    let paid:=bill R lower upper W v φ
    HasDerivAt (fun t=>hearing R lower upper (fun U=>((-S U:ℝ):ℂ)) v φ t-
      hearing R lower upper (fun U=>((-M U:ℝ):ℂ)) v φ t) paid 0 ∧
      ‖paid‖≤rms R (p:=p) (lower.trans upper) v φ * (ε*g^q)

theorem purchased (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit) (heat:Poetry R.family.path.levels)
    (v:ℕ→Gear G→ℝ) (rows:FundedMarkedCoverRows.prices v R.kit) (credit:Credit) (d M r q:ℕ) {ε:ℝ} (ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ i:ℕ in atTop,let j:=i+1
      let C:=credit.buy (zz V j)+zz V j*V.clock.loopCap j
      ∀N,∀upper:j<N,∀σ,0<σ→σ⁻¹≤zz V j→∀Z:SeriesA G,Draw Z σ C→Z.length≤M→
        (∀a∈Z,0<a.grade)→(∀a∈Z,a.grade≤d)→Returned R j N upper.le Z σ C r q ε:=by
  intro V
  filter_upwards [cofinal_spring_mask_budget R simple slow heat v rows credit d M r,
    cofinal_spring_mask_return R simple slow heat v rows credit d M r q ep] with i bounded earned
  intro j C N upper σ sp wide Z draw len lo hi p x m lower marks φ g S M W paid
  obtain ⟨meas,cap,-⟩:=bounded N upper σ sp wide Z draw len lo hi p x
  have eW:Envelope W:=(show Envelope (fun U=>M U-S U) from ⟨meas,_,cap⟩).ofReal_env
  obtain ⟨sm,sc⟩:=filed_site_price R N p j r upper.le Z sp draw g x
  have eS:Envelope (fun U=>(S U:ℂ)):=(show Envelope S from ⟨sm,_,sc⟩).ofReal_env
  have eB:Envelope (fun U=>((-S U:ℝ):ℂ)):=by simpa only [Complex.ofReal_neg] using eS.negC
  have eA:Envelope (fun U=>((-M U:ℝ):ℂ)):=by
    convert! eB.subC eW using 1
    funext U
    simp only [W,Complex.ofReal_neg,Complex.ofReal_sub]
    ring
  have eq:(fun U=>((-S U:ℝ):ℂ))=(fun U=>((-M U:ℝ):ℂ))+W:=by
    funext U
    simp only [Pi.add_apply,W,Complex.ofReal_neg,Complex.ofReal_sub]
    ring
  have inc:=(earned N upper σ sp wide Z draw len lo hi p x j (le_refl j)).2.2.2.1
  rw [actualTransport_base R.family R.makes upper.le] at inc
  exact change R lower upper.le _ _ W eA eB eW eq (mul_nonneg ep.le (pow_nonneg
    (IterationFour.Currency.g_pos R.makes N p j upper.le).le _)) inc marks φ

end YM.Integration.WilsonMatrixOriginalGermMaskPanel
