import YM.SchemeRG11.Hot.Salt

/-! Represent exponential and space derivatives. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.SchemeRG11.Hot
open Function Set MeasureTheory Metric Filter
open scoped Topology ContDiff Classical
variable {I X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
open Tint

section
variable [Fintype I]
def tongs (φ : I→X→ℝ) (P : Tint I X) (t : ℝ) (r : I→ℝ) (e : ℂ) (x : X) :=
  (t:ℂ)^(e-2)*Complex.ofReal (Real.exp (-∑ i:I,r i * φ i x))* read e r x P

lemma twist {φ : I→X→ℝ} (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (P : Tint I X) (t : ℝ) (r : I→ℝ) (e : ℂ) :
    ContDiff ℝ ∞ (tongs φ P t r e) := by
  unfold tongs
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (g:=Complex.ofRealCLM) (ContDiff.exp (ContDiff.neg (ContDiff.sum (fun i _=> contDiff_const.mul (hφ i))))))).mul (P.position ..)
lemma tunnel (φ : I→X→ℝ) (P : Tint I X) {t : ℝ} (h : 0<t) (r : I→ℝ) (x : X) :
    Differentiable ℂ (fun e=>tongs φ P t r e x) := by
  intro e; exact (((differentiableAt_id.sub_const (2:ℂ)).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr h.ne'))).mul_const _ |>.mul (P.dim r x e))

lemma tackle {Y : Type} [TopologicalSpace Y] {φ : I→X→ℝ} (hφ : ∀ i, Continuous (φ i)) (P : Tint I X)
    {t : Y→ℝ} {r : Y→I→ℝ} {e : Y→ℂ} {x : Y→X} {y} (ht : ContinuousAt t y) (hr : ContinuousAt r y) (he : ContinuousAt e y) (hx : ContinuousAt x y) (h : t y≠0) :
    ContinuousAt (fun y=> tongs φ P (t y) (r y) (e y) (x y)) y := by
  have hp : ContinuousAt (fun y=> (t y:ℂ)^(e y-2)) y := (Complex.continuousAt_ofReal_cpow (t y) (e y-2) (Or.inr h)).comp (f:=fun y=>(t y,e y-2)) (ht.prodMk (he.sub_const 2))
  refine (hp.mul (Complex.continuous_ofReal.continuousAt.comp ?_)).mul (P.team.continuousAt.comp (he.prodMk (hr.prodMk hx)))
  let L (v : (I→ℝ) × X) := Real.exp (-∑ i,v.1 i*φ i v.2)
  have he : Continuous L := Real.continuous_exp.comp (Continuous.neg (continuous_finsetSum _ fun i _=> ((continuous_apply i).comp continuous_fst).mul ((hφ i).comp continuous_snd)))
  exact he.continuousAt.comp (hr.prodMk hx)


omit [Fintype I] in
private lemma coded {φ : I→X→ℝ} (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (s : Finset I) : ∃ P : Tint I X, ∀ e r x,
    read e r x P = Complex.ofReal (∑ i∈s,-(r i*φ i x)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨digit 0,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨P,h⟩:=ih
    refine ⟨add (mul (slot i) (smooth (fun x=> (↑(-φ i x):ℂ)) (Complex.ofRealCLM.contDiff.comp (hφ i).neg))) P,fun e r x=>?_⟩
    simp only [Tint.read,h,Finset.sum_insert hi]; push_cast; ring

lemma winds {φ : I→X→ℝ} (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (P : Tint I X) (v : X) : ∃ Q : Tint I X, ∀ t r e x,
    fderiv ℝ (tongs φ P t r e) x v = tongs φ Q t r e x := by
  obtain ⟨R,hR⟩ := coded hφ Finset.univ
  have he t r e x (P : Tint I X) : tongs φ P t r e x=(t:ℂ)^(e-2)*Complex.exp (read e r x R)*read e r x P := by simp [tongs,hR,Complex.ofReal_exp]
  refine ⟨add (mul (dance v R) P) (dance v P),fun t r e x=>?_⟩
  rw [show tongs φ P t r e=(fun x=> (t:ℂ)^(e-2)*Complex.exp (read e r x R))*(fun x=> read e r x P) from funext fun x=> he t r e x P]
  let f := fun x=> read e r x R
  have hd:= (R.position e r).differentiable (by simp) x
  have hC:= hd.hasFDerivAt.cexp
  rw [he,fderiv_mul (hC.differentiableAt.const_mul _) ((P.position e r).differentiable (by simp) x), fderiv_const_mul hC.differentiableAt, hC.fderiv]
  simp only [Tint.read,dance_reads,add_apply,smul_apply,smul_eq_mul]; ring

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
/-- Apply derivative words. -/
def series (f : X→W) : (l : List X) → X→W
| [] => f
| v::l => fun x=> fderiv ℝ (series f l) x v
lemma recast {φ : I→X→ℝ} (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (P : Tint I X) (l : List X) : ∃ Q : Tint I X,
    ∀ t r e, series (tongs φ P t r e) l = tongs φ Q t r e := by
  induction l with
  | nil => exact ⟨P,fun _ _ _=>rfl⟩
  | cons v l ih =>
    obtain ⟨Q,h⟩:=ih; obtain ⟨R,k⟩:=winds hφ Q v
    exact ⟨R,fun t r e=> funext fun x=> by rw [series,h]; exact k _ _ _ _⟩
end
lemma swath (P : Tint Unit X) {φ : Unit→X→ℝ} (hd : ∀ i, ContDiff ℝ ∞ (φ i)) : ∃ Q : Tint Unit X, ∀ t : ℝ, 0<t → ∀ e x,
    HasDerivAt (fun t : ℝ=>tongs φ P t (fun _=>t⁻¹) e x) (tongs φ Q t (fun _=>t⁻¹) e x) t := by
  let A : Tint Unit X:=slot ()
  let U : Tint Unit X:= smooth (fun x=> (φ () x:ℂ)) (Complex.ofRealCLM.contDiff.comp (hd ()))
  let T : Tint Unit X:= number (fun z=> z-2) (differentiable_id.sub_const 2)
  refine ⟨add (mul (add (mul T A) (mul (mul U A) A)) P) (slant P), fun t ht e x=>?_⟩
  have hp : HasDerivAt (fun t : ℝ=>(t:ℂ)^(e-2)) ((e-2)*(t:ℂ)^((e-2)-1)) t := by
    by_cases h:e-2=0
    · simp only [h,Complex.cpow_zero,zero_mul]; exact hasDerivAt_const ..
    exact hasDerivAt_ofReal_cpow_const ht.ne' h
  have hz:=((((hasDerivAt_inv ht.ne').mul_const (φ () x)).neg).exp).ofReal_comp
  unfold tongs
  simp only [Fintype.sum_unique]
  convert! ((hp.mul hz).mul (P.slants e x ht)) using 1
  simp only [Tint.read,A,U,T,Pi.neg_apply,Pi.mul_apply,show (default:Unit)=() from rfl]
  rw [Complex.cpow_sub (e-2) 1 (Complex.ofReal_ne_zero.mpr ht.ne'),Complex.cpow_one]; push_cast; ring

end YM.SchemeRG11.Hot
