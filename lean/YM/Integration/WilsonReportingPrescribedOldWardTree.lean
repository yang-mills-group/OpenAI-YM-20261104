import YM.Integration.WilsonReportingPrescribedOldWardPanel

/-! The original quadratic Q columns differ by genuine constants at tree
order. They disappear under the same held Wilson law, before its final test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldWardTree
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Tree Precision Source Labels
open PhysicalNext.Repeat.Legato RGComparison.Core16 RG17 SectorNext.Vacuum Extraction Table Spec Climb
open MS MS.Local.Physical MS.Theater Maxwell Maxwell.Free StressFlux Trace.Pilot PhysMS
open Extraction.Order Next.UVStress OPE OPE.Therm FVA2 FVA2.Register
open WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldSignedPanel
open WilsonReportingPrescribedOldWardWallet WilsonReportingPrescribedOldWardPanel
open private continuous_operand from YM.Integration.WilsonReportingPrescribedOldWardPanel
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {B:Deck G} (Q:MS.Land.Prescription B) {N per:ℕ}
local notation "Ω" => Config G (R.family.side N per)
local notation "site" => Site (R.family.side N per)

def stencil (z:Stock B) (n:Side) (o:Site n) (U:Config G n) : ℂ :=
  ∑i,z.2 i*(((ActualOriginalDictionary.dictionary R B).cylinder 4 2 i).O n o U : ℂ)

theorem centered (simple:G.Simple) (z:Stock B) (clock:ℝ) (n:Side) (o:Site n) (U V:Config G n) :
    operand R Q z clock 0 n o U-operand R Q z clock 0 n o V=stencil R z n o U-stencil R z n o V := by
  unfold operand stencil
  rw [add_sub_add_left_eq_sub,←sum_sub_distrib,←sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_sub,←mul_sub]
  have h:=WilsonReportingPrescribedOldAction.measured R B Q i clock simple n o U V
  simp only [Complex.ofReal_sub] at h
  exact congrArg (fun t=>z.2 i*t) h

def moment (ν:Measure Ω) (a b:Ω→ℝ) : ℝ := (∫U,a U*b U ∂ν)-(∫U,a U ∂ν)*(∫U,b U ∂ν)

private theorem symmetry (ν:Measure Ω) (a b:Ω→ℝ) : moment R ν a b=moment R ν b a := by
  unfold moment
  rw [mul_comm (∫_,a _ ∂ν),show (fun U=>a U*b U)=(fun U=>b U*a U) from funext fun _=>mul_comm ..]

private theorem translate (ν:Measure Ω) [IsProbabilityMeasure ν] (a b:Ω→ℝ)
    (ha:Continuous a) (hb:Continuous b) (c:ℝ) : moment R ν (fun U=>a U+c) b=moment R ν a b := by
  have buy {x:Ω→ℝ} (h:Continuous x):Integrable x ν:=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold moment
  have expand : (fun U=>(a U+c)*b U)=(fun U=>a U*b U+c*b U) := funext fun _=>add_mul ..
  have plus : (∫U,a U*b U+c*b U ∂ν)=(∫U,a U*b U ∂ν)+(∫U,c*b U ∂ν) :=
    integral_add (buy (ha.mul hb)) (buy (continuous_const.mul hb))
  have marginal : (∫U,a U+c ∂ν)=(∫U,a U ∂ν)+∫_,c ∂ν := integral_add (buy ha) (integrable_const c)
  rw [expand,plus,marginal,integral_const_mul]
  simp
  ring

theorem connected (ν:Measure Ω) [IsProbabilityMeasure ν] (simple:G.Simple)
    (s t:Stock B) (clock:ℝ) (o x:site) (χ:ℂ→L[ℝ]ℝ) :
    moment R ν (fun U=>(operand R Q s clock 0 _ o U).re) (fun U=>χ (operand R Q t clock 0 _ x U))=
      moment R ν (fun U=>(stencil R s _ o U).re) (fun U=>χ (stencil R t _ x U)) := by
  let n:=R.family.side N per
  let c (a:Stock B) (u:site):=operand R Q a clock 0 n u 1-stencil R a n u 1
  have equal (a:Stock B) (u:site)(U:Ω) : operand R Q a clock 0 n u U=stencil R a n u U+c a u := by
    have h:=centered R Q simple a clock n u U 1
    dsimp only [c]
    linear_combination h
  have cont (a:Stock B) (u:site) : Continuous (stencil R a n u) := by
    have ident : stencil R a n u=fun U=>operand R Q a clock 0 n u U-c a u := by
      ext U
      rw [equal];simp
    rw [ident]
    exact (continuous_operand R Q a clock 0 u).sub continuous_const
  have left : (fun U=>(operand R Q s clock 0 n o U).re)=fun U=>(stencil R s n o U).re+(c s o).re := by
    funext U;rw [equal,Complex.add_re]
  have right : (fun U=>χ (operand R Q t clock 0 n x U))=fun U=>χ (stencil R t n x U)+χ (c t x) := by
    funext U;rw [equal,map_add]
  change moment R ν (fun U=>(operand R Q s clock 0 n o U).re) (fun U=>χ (operand R Q t clock 0 n x U))=_
  rw [left,right]
  let a:Ω→ℝ:=fun U=>(stencil R s n o U).re
  let b:Ω→ℝ:=fun U=>χ (stencil R t n x U)
  have ha:Continuous a:=Complex.continuous_re.comp (cont s o)
  have hb:Continuous b:=χ.continuous.comp (cont t x)
  change moment R ν (fun U=>a U+(c s o).re) (fun U=>b U+χ (c t x))=moment R ν a b
  calc
    _=moment R ν a (fun U=>b U+χ (c t x)):=translate R ν a _ ha (hb.add continuous_const) _
    _=moment R ν (fun U=>b U+χ (c t x)) a:=symmetry R ν ..
    _=moment R ν b a:=translate R ν b a hb ha _
    _=_:=symmetry R ν ..

theorem held (simple:G.Simple) {j:ℕ} (jn:j+1≤N) (W:Config G (R.family.side j per))
    (s t:Stock B) (clock:ℝ) (o x:site) (χ:ℂ→L[ℝ]ℝ) :
    let ν:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per jn W
    moment R ν (fun U=>(operand R Q s clock 0 _ o U).re) (fun U=>χ (operand R Q t clock 0 _ x U))=
      moment R ν (fun U=>(stencil R s _ o U).re) (fun U=>χ (stencil R t _ x U)) := by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R jn (le_refl N) W
  exact connected R Q _ simple s t clock o x χ

theorem original (simple:G.Simple) (s t:Stock B) (clock:ℝ) (χ:ℂ→L[ℝ]ℝ) (φ:Test 2) :
    separated R (N:=N) (per:=per) χ φ (operand R Q s clock 0 _) (operand R Q t clock 0 _)=
      separated R (N:=N) (per:=per) χ φ (stencil R s _) (stencil R t _) := by
  letI : IsProbabilityMeasure (scene R.family.path N per N) := probability R.makes.wilson le_rfl
  unfold WilsonReportingPrescribedOldSignedPanel.separated
  apply congrArg
  apply Finset.sum_congr rfl
  intro sites _
  exact congrArg (fun a=>(φ (cells R.family N per sites)).re*a)
    (connected R Q _ simple s t clock (sites 0) (sites 1) χ)

end YM.Integration.WilsonReportingPrescribedOldWardTree
