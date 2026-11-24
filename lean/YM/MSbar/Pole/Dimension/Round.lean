import YM.MSbar.Pole.Dimension.Range

/-! Pad by an even plane without any linear independence assumption on external data. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical BigOperators
variable {H : ℝ× ℂ → ℂ}

def Globular (H : ℝ × ℂ → ℂ) := ∀ (t s : ℝ) (x y : ℂ), t^2+‖x‖^2=s^2+‖y‖^2 → H (t,x)=H (s,y)
def Radius (t:ℝ)(x:ℂ) := Real.sqrt (t^2+‖x‖^2)
lemma Radius_nonneg (t:ℝ)(x:ℂ): 0≤ Radius t x:= Real.sqrt_nonneg _
lemma Radius_sq (t:ℝ)(x:ℂ): Radius t x^2=t^2+‖x‖^2:=Real.sq_sqrt (by positivity)
lemma Globular.radius (h:Globular H) (t:ℝ)(x:ℂ): H (t,x)=H (Radius t x,0):=h _ _ _ _ (by rw [Radius_sq]; simp)
lemma Globular.even (h:Globular H) : EvenOn univ H := fun x _ t=>h _ _ _ _ (by simp)

def fullPlane (H : ℝ× ℂ→ℂ) := Packet (univ ×ˢ univ) ((1:Price ℂ).back Prod.snd) (Moment (ticket (@id ℂ))) H
variable (p : fullPlane H) (h : Globular H)
include p h
private lemma meridian (t:ℝ)(x:ℂ) (ht:t≠0) : higher H (t,x)=higher H (Radius t x,0) := by
  let Y(s:ℝ):=Radius s x; let r:= Y t; have hr : 0<r := by unfold r Y Radius; positivity
  have hr' : t^2+‖x‖^2 ≠ 0 := by positivity
  have he : HasDerivAt Y (t/r) t := by
    apply ((((hasDerivAt_id' t).pow 2).add_const (‖x‖^2)).sqrt hr').congr_deriv; dsimp [r,Y,Radius]; norm_num; ring
  have hl := (letter_read p r (mem_univ (0:ℂ))).scomp t he
  have hy : letter H (t,x)= (t/r) • letter H (r,0) :=
    (letter_read p t (mem_univ x)).unique (hl.congr_of_eventuallyEq (Eventually.of_forall fun y=>h.radius y x))
  rw [alt_of_ne p h.even ht (mem_univ x),alt_of_ne p h.even hr.ne' (mem_univ _),hy]
  change t⁻¹ • (-(2:ℝ)⁻¹ • ((t/r) • _))=r⁻¹ • _
  rw [smul_comm (-(2:ℝ)⁻¹),smul_smul,inv_mul_eq_iff_eq_mul₀ ht |>.mpr (show t/r=t*r⁻¹ by ring)]

lemma meridian_all (t:ℝ)(x:ℂ) : higher H (t,x)=higher H (Radius t x,0) := by
  have hp := smooth isOpen_univ (show ContinuousOn (1:Price ℂ).val _ from continuousOn_const) p h.even
  let g (t:ℝ) := higher H (Radius t x,0)
  have hr : ContinuousAt g t := (hp.smooth _ (mem_prod.mpr ⟨mem_univ _,mem_univ _⟩)).continuousAt.comp (x:=t) (f:=fun t:ℝ=>(Radius t x,(0:ℂ)))
    (by unfold Radius; fun_prop)
  have hq := (letter_read hp t (mem_univ x)).continuousAt
  by_cases ht:t=0
  · subst t; apply tendsto_nhds_unique_of_eventuallyEq (hq.continuousWithinAt (s:={ (0:ℝ) }ᶜ) ) (hr.continuousWithinAt)
    filter_upwards [self_mem_nhdsWithin] with i hi; exact meridian p h i x hi
  exact meridian p h t x ht
lemma round_higher : Globular (higher H) := fun t s x y hh=> by rw [meridian_all p h, meridian_all p h s,show Radius t x=Radius s y from congr_arg Real.sqrt hh]
lemma nose (t:ℝ)(r:ℝ)(hr:0<r) :
    HasDerivAt (fun s:ℝ=> H (t,s)) (-(2:ℂ)*r*higher H (t,r)) r := by
  let Y(s:ℝ):=Radius t (s:ℂ); have hY(s) : Y s = Real.sqrt (t^2+s^2):= by dsimp [Y,Radius]; simp
  have ha: Y=fun s=>Real.sqrt (t^2+s^2):=funext hY; let b:=Y r; have hb: 0<b:= by dsimp [b]; rw [hY]; positivity
  have he: HasDerivAt Y (r/b) r:= by
    rw [ha]; have hy: t^2+r^2≠0:=by positivity
    refine ((((hasDerivAt_id' r).pow 2).const_add (t^2)).sqrt hy).congr_deriv ?_; dsimp [b]; rw [hY]; simp; ring
  have hh : HasDerivAt (fun s:ℝ=> H (t,(s:ℂ))) ((r/b) • letter H (b,0)) r :=
    ((letter_read p b (mem_univ (0:ℂ))).scomp r he).congr_of_eventuallyEq (Eventually.of_forall fun v=> h.radius _ _)
  apply hh.congr_deriv
  rw [meridian_all p h,alt_of_ne p h.even hb.ne' (mem_univ _)]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv,Complex.ofReal_neg, Complex.ofReal_ofNat]; change _*_= -(2:ℂ)*r*((b:ℂ)⁻¹*(-(2:ℂ)⁻¹*_))
  ring
end YM.MSbar.Pole.Radial
