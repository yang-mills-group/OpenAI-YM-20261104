import YM.Integration.WilsonMatrixOriginalGermSpringPanel
import YM.Integration.WilsonMacroscopicRichCaptureVariance
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskEarned

/-! The complete UV test stays joined in its own second moment. A real
second-moment invoice for one older signed source pays its response at
every upper cutoff by the original backward Wilson contraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermPanelRMS
open MeasureTheory Filter Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox FVA2
open WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermFourRawMarks
open WilsonMatrixOriginalGermSpringHearing WilsonMatrixOriginalGermSpringPanel OriginalMarkedRunAction
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {m k N p:ℕ}

def source (live:m≤N) (w:R.family.label 4) (x:Fin 2→Site (R.family.side N p)) (i:Fin 2):
    Config G (R.family.side N p)→ℂ:=asset R live w ((R.family.S.toDepth live p).parent (x i))

def panel (live:m≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):Config G (R.family.side N p)→ℂ:=
  plot R (fun x:Fin 2→Site (R.family.side N p)=>WilsonExternalMeshMass.charge R.family φ x)
    (fun x=>source R live (v 0) x 0) (fun x=>source R live (v 1) x 1)

def hearing (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (v:Fin 2→R.family.label 4)
    (φ:Test 2) (t:ℂ):ℂ:=
  ∑x:Fin 2→Site (R.family.side N p),WilsonExternalMeshMass.charge R.family φ x*
    invoice R lower upper W (source R (lower.trans upper) (v 0) x 0) (source R (lower.trans upper) (v 1) x 1) t

def bill (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (v:Fin 2→R.family.label 4)
    (φ:Test 2):ℂ:=
  ∫U,backTo R.family.path N p upper W U*panel R (lower.trans upper) v φ U ∂scene R.family.path N p N

def rms (live:m≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):ℝ:=
  Real.sqrt (∫U,‖panel R (p:=p) live v φ U‖^2 ∂scene R.family.path N p N)

private theorem energy {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsFiniteMeasure μ]
    {f:Ω→ℂ} (h:Envelope f):Integrable (fun U=>‖f U‖^2) μ:=by
  obtain ⟨b,hb⟩:=h.cost
  have bounded:∀U,‖‖f U‖‖≤b:=fun U=>(Real.norm_of_nonneg (norm_nonneg _)).le.trans (hb U)
  simpa only [sq] using (h.integrableC μ).norm.bdd_mul h.meas.norm.aestronglyMeasurable (Eventually.of_forall bounded)

theorem measured (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (hW:Envelope W) {δ:ℝ}
    (pos:0≤δ) (income:(∫V,‖W V‖^2 ∂scene R.family.path N p k)≤δ^2) (v:Fin 2→R.family.label 4) (φ:Test 2):
    HasDerivAt (hearing R lower upper W v φ) (bill R lower upper W v φ) 0 ∧
      ‖bill R lower upper W v φ‖≤rms R (p:=p) (lower.trans upper) v φ * δ:=by
  let μ:=scene R.family.path N p N
  let l:=lower.trans upper
  let a:=fun x:Fin 2→Site (R.family.side N p)=>WilsonExternalMeshMass.charge R.family φ x
  let X:=fun (x:Fin 2→Site (R.family.side N p)) (i:Fin 2)=>source R l (v i) x i
  let Y:=panel R (p:=p) l v φ
  let B:=backTo R.family.path N p upper W
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson (le_refl N)
  have ex (x i):Envelope (X x i):=Envelope.compactC (R.family.continuousO ..)
  have per (x):Envelope (centered R (X x 0) (X x 1)):=
    (((ex x 0).subC (Envelope.constC _)).mulC ((ex x 1).subC (Envelope.constC _))).subC (Envelope.constC _)
  have ey:Envelope Y:=Envelope.sumC Finset.univ _ (fun x _=>(Envelope.constC (a x)).mulC (per x))
  have eb:Envelope B:=backTo_env R.family.path N p upper hW
  constructor
  · exact (WilsonMatrixOriginalGermSpringPanel.measured R lower upper W hW.cost.choose hW.meas hW.cost.choose_spec a
      (fun x=>X x 0) (fun x=>X x 1) (fun x=>ex x 0) (fun x=>ex x 1)).1
  · have paid: (∫U,‖B U‖^2 ∂μ)≤δ^2:=(WilsonMacroscopicRichCaptureVariance.measured R upper (le_refl N) hW).trans income
    have bound:=(spring_mask_spectator B Y eb.meas.aestronglyMeasurable ey.meas.aestronglyMeasurable (energy μ eb)
      (energy μ ey) pos paid).2
    calc
      _≤∫U,‖B U*Y U‖ ∂μ:=norm_integral_le_integral_norm _
      _=∫U,‖Y U*B U‖ ∂μ:=integral_congr_ae (Eventually.of_forall fun U=>congrArg norm (mul_comm _ _))
      _≤_:=bound

end YM.Integration.WilsonMatrixOriginalGermPanelRMS
