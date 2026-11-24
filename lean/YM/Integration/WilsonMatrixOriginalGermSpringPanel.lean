import YM.Integration.WilsonMatrixOriginalGermSpringHearing

/-! The signed physical mesh is kept inside the final complete centered
moment when the original spring is booked before the two raw addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSpringPanel
open MeasureTheory Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox
open WilsonMatrixOriginalGermGram WilsonMatrixOriginalGermTwoMarkJoint WilsonMatrixOriginalGermFourRawMarks
open WilsonMatrixOriginalGermSpringHearing
open Laurent Bloch Precision Exterior Tree PowerSeries Marker IterationFour IterationFour.Vacuum FVA2
open Comparison.RG02 Comparison.RG02.Assembly WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank Stationary
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric OriginalMarkedRunAction
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {m k N p:ℕ} {I:Type*} [Fintype I]

def plot (a:I→ℂ) (X Y:I → Config G (R.family.side N p)→ℂ) (U:Config G (R.family.side N p)):ℂ:=
  ∑i,a i*centered R (X i) (Y i) U

theorem measured (lower:m≤k) (upper:k≤N) (W:Config G (R.family.side k p)→ℂ) (B:ℝ)
    (cw:Measurable W) (bound:∀U,‖W U‖≤B) (a:I→ℂ) (X Y:I → Config G (R.family.side N p)→ℂ)
    (hx:∀i,Envelope (X i)) (hy:∀i,Envelope (Y i)):
    let μ:=scene R.family.path N p N
    let paid:=∫U,backTo R.family.path N p upper W U*plot R a X Y U ∂μ
    HasDerivAt (fun t=>∑i,a i*invoice R lower upper W (X i) (Y i) t) paid 0 ∧
        ‖paid‖≤B*∫U,‖plot R a X Y U‖ ∂μ:=by
  intro μ paid
  let T:=backTo R.family.path N p upper W
  have hW:Envelope W:=⟨cw,B,bound⟩
  have hT:Envelope T:=backTo_env R.family.path N p upper hW
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson (le_refl N)
  have env (i:I):Envelope (centered R (X i) (Y i)):=
    (((hx i).subC (Envelope.constC _)).mulC ((hy i).subC (Envelope.constC _))).subC (Envelope.constC _)
  have total:Envelope (plot R a X Y):=
    Envelope.sumC Finset.univ _ (fun i _=>(Envelope.constC (a i)).mulC (env i))
  have same:(∑i,a i*debit R upper W (X i) (Y i))=paid:=by
    calc
      _=∑i,∫U,a i*(T U*centered R (X i) (Y i) U) ∂μ:=
        Finset.sum_congr rfl (fun i _=>(integral_const_mul _ _).symm)
      _=∫U,∑i,a i*(T U*centered R (X i) (Y i) U) ∂μ:=
        (integral_finsetSum _ (fun i _=>((hT.mulC (env i)).integrableC μ).const_mul (a i))).symm
      _=_:=by
        apply integral_congr_ae (Filter.Eventually.of_forall fun U=>?_)
        change _=T U*∑i,a i*centered R (X i) (Y i) U
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _=>mul_left_comm _ _ _)
  constructor
  · rw [←same]
    apply HasDerivAt.fun_sum
    intro i _
    exact (WilsonMatrixOriginalGermSpringHearing.measured R lower upper W hW B bound (X i) (Y i) (hx i) (hy i)).1.const_mul (a i)
  · have price:=backTo_bound R.family.path N p upper cw B bound
    calc
      _≤∫U,B*‖plot R a X Y U‖ ∂μ:=by
        apply norm_integral_le_of_norm_le ((total.integrableC μ).norm.const_mul B)
        exact Filter.Eventually.of_forall fun U=>(norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (price U) (norm_nonneg _))
      _=_:=integral_const_mul _ _

theorem original (lower:m≤k) (upper:k≤N) (r:ℕ) (Z:SeriesA G) {σ b:ℝ} (hs:0<σ) (draw:Draw Z σ b)
    (g:ℝ) (root:Site (R.family.side k p)) (v:Fin 2→R.family.label 4) (φ:Test 2):
    let l:=lower.trans upper
    let W:=fun U=>((-springAt R N p k r Z g root U:ℝ):ℂ)
    let a:=fun x:Fin 2→Site (R.family.side N p)=>WilsonExternalMeshMass.charge R.family φ x
    let X:=fun (x:Fin 2→Site (R.family.side N p)) (i:Fin 2)=>asset R l (v i) ((R.family.S.toDepth l p).parent (x i))
    let F:=plot R a (fun x=>X x 0) (fun x=>X x 1)
    let μ:=scene R.family.path N p N
    let paid:=∫U,backTo R.family.path N p upper W U*F U ∂μ
    HasDerivAt (fun t=>∑x,a x*invoice R lower upper W (X x 0) (X x 1) t) paid 0 ∧
      ‖paid‖ ≤ springSiteBill R N k r Z g b * ∫U,‖F U‖ ∂μ:=by
  intro l W a X F μ paid
  obtain ⟨hm,hb⟩:=filed_site_price R N p k r upper Z hs draw g root
  apply measured R lower upper W _ (Complex.continuous_ofReal.measurable.comp hm.neg) _ a
    (fun x=>X x 0) (fun x=>X x 1) (fun _=>Envelope.compactC (R.family.continuousO ..))
    (fun _=>Envelope.compactC (R.family.continuousO ..))
  intro U
  change ‖((-springAt R N p k r Z g root U:ℝ):ℂ)‖ ≤ _
  rw [Complex.norm_real,norm_neg]
  exact hb U

end YM.Integration.WilsonMatrixOriginalGermSpringPanel
