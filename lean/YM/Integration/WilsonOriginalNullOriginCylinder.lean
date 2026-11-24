import YM.Integration.WilsonOriginalNullPlacedFanField
import YM.Integration.WilsonMatrixOriginalGermPeriod
import YM.RG12.Canonical.Charts

/-! One centered finite-period inverse defines the original cylinder at
every translated site. The stored chart and the full measured origin germ
differ by the native wrapping bill uniformly in the upper cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullOriginCylinder
open Function Filter Lattice RG Wilson Source Labels RG12 Trace.Physical
open Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators
open private side_tendsto from YM.Integration.ActualOuterQuarterProfile
variable {G:Gauge} (C:Family G) (d m:ℕ)

abbrev stockMap (N p:ℕ) (b:C.label d):C.label d:=((C.factory d N p).entries m b).x

abbrev seam (p:ℕ):ℝ:=invoice (C:=C) d m p*stock C m

theorem reference (H:C.Makes) {N p:ℕ} (age:C.ref d ≤ m) (live:m ≤ N) (b:C.label d):
    charts C H d m (N,p) ((C.factory d N p).terminal b)=stockMap C d m N p b := by
  rw [charts,dif_pos ⟨age,live⟩]
  change ((C.factory d N p).entries m ((C.factory d N p).terminal.symm ((C.factory d N p).terminal b))).x=_
  rw [LinearEquiv.symm_apply_apply]

theorem pullback (H:C.Makes) {N p:ℕ} (age:C.ref d ≤ m) (live:m ≤ N) (b:C.label d):
    atK C H d m (N,p) (stockMap C d m N p b)=(C.factory d N p).terminal b := by
  rw [←reference C d m H age live]
  exact (charts C H d m (N,p)).symm_apply_apply _

theorem cylinder (H:C.Makes) {N p:ℕ} (age:C.ref d ≤ m) (live:m ≤ N) (b:C.label d) (o y:Site (C.side N p)):
    C.O N p (atK C H d m (N,p) (stockMap C d m N p b)) (o+y)=
      (initial (C.localSection d) C.path N p b o) ∘ Lattice.translate y := by
  rw [pullback C d m H age live]
  funext U
  rw [←C.translation o y]
  simp only [Function.comp_apply,Family.O,TransferData.cylinder,LinearEquiv.symm_apply_apply]

theorem measured (H:C.Makes) {N p:ℕ} (home:Opened C d m p) (live:m ≤ N) (b:C.label d):
    (C.labels.level d).coeffSize (fitting d N p m H home live b-stockMap C d m N p b) ≤ 
      seam C d m p*(C.labels.level d).coeffSize (stockMap C d m N p b) := by
  simpa only [fitting_apply,seam,stockMap,mul_assoc] using
    measured_diff (C:=C) d N p m H home.post live (entryOk d N p m H home.post live b)

theorem nonnegative (p:ℕ):0 ≤ seam C d m p:=by
  have positive:0<(Germ.germ_close (C.labels.level d) C.params).choose:=
    (Germ.germ_close (C.labels.level d) C.params).choose_spec.1
  have stock0:0 ≤ stock C m:=zero_le_one.trans (stage C m).columns_ge
  unfold seam invoice price cut Germ.wraps
  positivity

theorem correction (H:C.Makes) {N p:ℕ} (home:Opened C d m p) (live:m ≤ N) (e:C.label d):
    let b:=(fitting (C:=C) d N p m H home live).symm e
    let w:=stockMap C d m N p b
    (C.labels.level d).coeffSize (w-e) ≤ seam C d m p/(1-seam C d m p)*(C.labels.level d).coeffSize e := by
  intro b w
  let F:=C.labels.level d
  let h:=seam C d m p
  have pos:0 ≤ h:=nonnegative C d m p
  have small:h<1/4:=home.small
  have gone:F.coeffSize (e-w) ≤ h*F.coeffSize w:=by
    simpa only [b,LinearEquiv.apply_symm_apply] using measured C d m H home live b
  have swap:F.coeffSize (w-e)=F.coeffSize (e-w):=by
    unfold Frame.coeffSize
    apply Finset.sum_congr rfl
    intro j _
    exact norm_sub_rev _ _
  have error:F.coeffSize (w-e) ≤ h*F.coeffSize w:=swap.trans_le gone
  have triangle:F.coeffSize (e+(w-e)) ≤ F.coeffSize e + F.coeffSize (w-e):=by
    unfold Frame.coeffSize
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _=>norm_add_le _ _
  rw [_root_.add_sub_cancel] at triangle
  have den:0<1-h:=by linarith only [small]
  have radius:(1-h)*F.coeffSize w ≤ F.coeffSize e:=by linarith only [triangle,error]
  have rr:F.coeffSize w ≤ F.coeffSize e/(1-h):=(le_div_iff₀ den).mpr (by linarith only [radius])
  calc
    F.coeffSize (w-e) ≤  h*F.coeffSize w:=error
    _  ≤  h*(F.coeffSize e/(1-h)):=mul_le_mul_of_nonneg_left rr pos
    _ = h/(1-h)*F.coeffSize e:=by ring

theorem period : Tendsto (seam C d m) atTop (𝓝 0):=by
  let B:=plank C m
  have side:=side_tendsto C.S m
  have den:0<10*(4*(B.B:ℝ)+2):=by positivity
  have length:=(side.const_mul_atTop B.exponent_pos).atTop_div_const den
  have back:=tendsto_neg_atTop_atBot.comp length
  have down:=Filter.tendsto_atBot_add_const_left atTop (2*B.supportExponent) back
  have cost:=((Real.tendsto_exp_atBot.comp down).const_mul (price (C:=C) d)).mul_const (stock C m)
  change Tendsto (fun p => seam C d m p) atTop (𝓝 0)
  simpa [seam,invoice,cut,Germ.wraps,B,sub_eq_add_neg,Function.comp_def] using cost

theorem opened (age:C.ref d ≤ m):∀ᶠ p:ℕ in atTop,Opened C d m p:=by
  filter_upwards [(period C d m).eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with p small
  exact ⟨age,small⟩

theorem exact_label (H:C.Makes) {N p:ℕ} (home:Opened C d m p) (live:m ≤ N)
    (v:C.label d) (o y:Site (C.side N p)):
    let b:=(C.factory d N p).terminal.symm v
    let e:=fitting (C:=C) d N p m H home live b
    C.O N p (atK C H d m (N,p) (stockMap C d m N p ((fitting (C:=C) d N p m H home live).symm e))) (o+y)=
      (C.O N p v o) ∘ Lattice.translate y := by
  intro b e
  rw [show (fitting (C:=C) d N p m H home live).symm e=b from LinearEquiv.symm_apply_apply _ _,
    pullback C d m H home.post live,show (C.factory d N p).terminal b=v from LinearEquiv.apply_symm_apply _ _]
  funext U
  exact (C.translation o y v U).symm

end YM.Integration.WilsonOriginalNullOriginCylinder
