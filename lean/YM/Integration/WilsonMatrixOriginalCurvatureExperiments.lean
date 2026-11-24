import YM.Integration.WilsonMatrixOriginalCurvatureField
import YM.Integration.WilsonReportingPrescribedOldWardTree

/-! An original nonbare Wilson experiment with the complete finite deposited curvature coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalCurvatureExperiments
open MeasureTheory Lattice Wilson RG Precision Source Labels Maxwell StressFlux MS.Local.Physical MS.Menus
open FVA2 FVA2.Register Finset PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalIndependentFields WilsonMatrixOriginalCurvatureStock WilsonMatrixOriginalCurvatureField
open WilsonReportingPrescribedOldWardWallet WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldWardPanel WilsonReportingPrescribedOldWardTree
open private translate symmetry from YM.Integration.WilsonReportingPrescribedOldWardTree
open private continuous_operand from YM.Integration.WilsonReportingPrescribedOldWardPanel
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (B:Deck G) (N p:ℕ)
local notation "Ω" => Config G (R.family.side N p)
local notation "site" => Site (R.family.side N p)

def sample (a:Glyph B 4→ℂ) (o:site) (U:Ω):ℂ:=∑i,a i*R.family.O N p (source R B N p i) o U

private theorem diff {I:Type*} [Fintype I] (a b c:I→ℂ):
    (∑i,a i*(b i-c i))=(∑i,a i*b i)-∑i,a i*c i:=by simp_rw [mul_sub];rw [sum_sub_distrib]

theorem weighted (simple:G.Simple) (age:R.family.ref 4≤N) (a:Glyph B 4→ℂ) (o:site) (U T:Ω):
    sample R B N p a o U-sample R B N p a o T=normalization R N*
      (stencil R (stock B a) _ o U-stencil R (stock B a) _ o T):=by
  let f:=fun i:Glyph B 4=>a i*(R.family.O N p (source R B N p i) o U-R.family.O N p (source R B N p i) o T)
  let g:=fun (j:B.BIndex (4:ℤ) 2) (C:Ω)=>(((ActualOriginalDictionary.dictionary R B).cylinder 4 2 j).O _ o C:ℂ)
  have low(i:Glyph B 4)(hi:i.size<4):f i=0:=by
    obtain ⟨c,h⟩:=WilsonMatrixOriginalIndependentUnit.constant B R simple i hi
    simp [f,h N p age o]
  have top(j:B.BIndex (4:ℤ) 2):f (curvature B j)=normalization R N*(a (curvature B j)*(g j U-g j T)):=by
    obtain ⟨c,h⟩:=measured R B simple j
    unfold f g
    rw [h N p age o U,h N p age o T]
    ring
  calc
    _=∑i,f i:=(diff _ _ _).symm
    _=∑j:B.BIndex (4:ℤ) 2,f (curvature B j):=WilsonMatrixOriginalCurvatureStock.sum B simple f low
    _=normalization R N*∑j,a (curvature B j)*(g j U-g j T):=by rw [mul_sum];exact sum_congr rfl fun j _=>top j
    _=_:=congrArg (normalization R N*·) (diff _ _ _)

variable (Q:MS.Land.Prescription B)

/-- Actual cutoff labels, including each shifted atRef. The price is computed from its complete
original terminal coordinates, independently of the gauge configuration used in either reading. -/
theorem observed (simple:G.Simple) (age:R.family.ref 4≤N) (v:R.family.label 4) (clock:ℝ) (o:site) (U T:Ω):
    let z:=stock B (amounts R B N p v)
    R.family.O N p v o U-R.family.O N p v o T=normalization R N*
      (operand R Q z clock 0 _ o U-operand R Q z clock 0 _ o T):=by
  intro z
  have eq(C:Ω):R.family.O N p v o C=sample R B N p (amounts R B N p v) o C:=physical R B N p simple v o C
  exact (congrArg₂ (·-·) (eq U) (eq T)).trans ((weighted R B N p simple age _ o U T).trans
    (congrArg (normalization R N*·) (WilsonReportingPrescribedOldWardTree.centered R Q simple z clock _ o U T).symm))

def scale (N:ℕ):ℝ:=(R.family.S.a N^4)⁻¹*(R.family.path.levels.clock.threshold N)⁻¹^2

private theorem norm_real:normalization R N=(scale R N:ℂ):=by
  simp only [WilsonMatrixOriginalCurvatureField.normalization,scale,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow]

private theorem phase {X:Type*} (a b:X→ℂ) (t:ℝ) (χ:ℂ→L[ℝ]ℝ) (e:X)
    (h:∀v,a v-a e=(t:ℂ)*(b v-b e)):
    (fun v=>χ (a v))=fun v=>t*χ (b v)+(χ (a e)-t*χ (b e)):=by
  funext v
  have w:=congrArg χ (h v)
  rw [map_sub,←Complex.real_smul,χ.map_smul,map_sub,smul_eq_mul] at w
  linarith

private theorem scaled_moment (ν:Measure Ω) (a b:Ω→ℝ) (t:ℝ):
    WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>t*a U) (fun U=>t*b U)=t^2*WilsonReportingPrescribedOldWardTree.moment R ν a b:=by
  have same:(fun U=>t*a U*(t*b U))=fun U=>t^2*(a U*b U):=by funext U;ring
  unfold WilsonReportingPrescribedOldWardTree.moment
  rw [same,integral_const_mul,integral_const_mul,integral_const_mul]
  ring

private theorem pair (ν:Measure Ω) [IsProbabilityMeasure ν] (a b:Ω→ℝ)
    (ha:Continuous a) (hb:Continuous b) (t c d:ℝ):
    WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>t*a U+c) (fun U=>t*b U+d)=t^2*WilsonReportingPrescribedOldWardTree.moment R ν a b:=by
  have la:=continuous_const.mul ha (f:=fun _=>t)
  have lb:=continuous_const.mul hb (f:=fun _=>t)
  calc
    _=WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>t*a U) (fun U=>t*b U+d):=translate R ν _ _ la (lb.add continuous_const) c
    _=WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>t*b U+d) (fun U=>t*a U):=symmetry R ν ..
    _=WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>t*b U) (fun U=>t*a U):=translate R ν _ _ lb la d
    _=WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>t*a U) (fun U=>t*b U):=symmetry R ν ..
    _=_:=scaled_moment R N p ν a b t

/-- Both actual singleton means and the pair are sampled from the identical physical law. -/
theorem connected (ν:Measure Ω) [IsProbabilityMeasure ν] (simple:G.Simple) (age:R.family.ref 4≤N)
    (v w:R.family.label 4) (clock:ℝ) (o x:site) (χ:ℂ→L[ℝ]ℝ):
    let zv:=stock B (amounts R B N p v)
    let zw:=stock B (amounts R B N p w)
    WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>(R.family.O N p v o U).re) (fun U=>χ (R.family.O N p w x U))=
      scale R N^2*WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>(operand R Q zv clock 0 _ o U).re)
        (fun U=>χ (operand R Q zw clock 0 _ x U)):=by
  intro zv zw
  have a(v:R.family.label 4)(o:site)(f:ℂ→L[ℝ]ℝ):
      let z:=stock B (amounts R B N p v)
      (fun U=>f (R.family.O N p v o U))=fun U=>scale R N*f (operand R Q z clock 0 _ o U)+
        (f (R.family.O N p v o 1)-scale R N*f (operand R Q z clock 0 _ o 1)):=by
    intro z
    apply phase
    intro U
    rw [←norm_real R N]
    exact observed R B N p Q simple age v clock o U 1
  change WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>Complex.reCLM (R.family.O N p v o U)) _=_
  rw [a v o Complex.reCLM,a w x χ]
  exact pair R N p ν _ _ (Complex.continuous_re.comp (continuous_operand R Q zv clock 0 o))
    (χ.continuous.comp (continuous_operand R Q zw clock 0 x)) _ _ _

/-- Any interior observation year, arbitrary held exterior, actual original regulator and period. -/
theorem held (simple:G.Simple) (age:R.family.ref 4≤N) {j:ℕ} (jn:j+1≤N) (W:Config G (R.family.side j p))
    (v w:R.family.label 4) (clock:ℝ) (o x:site) (χ:ℂ→L[ℝ]ℝ):
    let ν:=WilsonMacroscopicRichFlatPosteriorLaw.law R N p jn W
    WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>(R.family.O N p v o U).re) (fun U=>χ (R.family.O N p w x U))=
      scale R N^2*WilsonReportingPrescribedOldWardTree.moment R ν
        (fun U=>(operand R Q (stock B (amounts R B N p v)) clock 0 _ o U).re)
        (fun U=>χ (operand R Q (stock B (amounts R B N p w)) clock 0 _ x U)):=by
  intro ν
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R jn (le_refl N) W
  exact connected R B N p Q ν simple age v w clock o x χ

end YM.Integration.WilsonMatrixOriginalCurvatureExperiments
