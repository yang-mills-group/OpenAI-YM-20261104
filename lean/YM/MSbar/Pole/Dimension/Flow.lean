import YM.MSbar.Pole.Dimension.Measures
import YM.MSbar.Pole.Dimension.Coherent

/-! # Scale change on IR-cut dimensional amplitudes -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Ambient
open Set Function Filter MeasureTheory place Radial
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
variable {I : Type} [Fintype I] {n : ℕ} {F G H : Screened I}

variable (hF : Breezes F) (tF : Texture F) (hG : Breezes G) (tG : Texture G)
include hF tF
private lemma coast (n:ℕ) :
    let V: Set (place n × External I n):=Domain n univ
    let p:= (ticket (@id (External I n))).back (@Prod.snd (place n) (External I n)); let q:=screen n (1:Price (External I n))
    IsOpen V ∧ ContinuousOn p.val V ∧ Packet (univ ×ˢ V) (p.back Prod.snd) (Moment q) (lifting n F) ∧ EvenOn V (lifting n F):=
    ⟨isOpen_univ.prod isOpen_univ,continuousOn_const.add (continuousOn_snd.norm),aboveAxis hF,fun x _=> symmetric tF n x (mem_univ _)⟩

lemma financed (x : External I n) (D : ℂ) : Integrable (fun y:place n => dimensional (lifting n F) (y,x) (D-2*n)) := by
  have hs : EvenOn (Domain n univ) (lifting n F) := fun x _ => symmetric tF n x (mem_univ _)
  have hx := (internal (L:=0) (b:=D) (p:=ticket (@id (External I n))) isOpen_univ
    (show ContinuousOn (fun z:External I n=>1+‖z‖) univ from (continuous_const.add continuous_norm).continuousOn)
    (aboveAxis hF) hs ‖D‖ (by simp)).1 x (mem_univ _); simp only [zero_apply,add_zero] at hx; exact hx

include hG tG
lemma aligned (hH : Breezes H) (tH : Texture H) (u v:ℂ) (x:External I n)
    (hh : ∀ y r,lifting n H (r,y,x)=u*lifting n F (r,y,x)+v*lifting n G (r,y,x)) (D : ℂ) : omega n H x D= u * omega n F x D + v * omega n G x D := by
  obtain ⟨hi,hj,hf,ht⟩:=coast hF tF n; obtain ⟨-,hl,hg,hk⟩:= coast hG tG n; obtain ⟨-,hr,hQ,hM⟩:=coast hH tH n
  have he y := Radial.linear hi hj hf ht hl hg hk (mem_prod.mpr ⟨mem_univ y,mem_univ x⟩) u v hQ hM hr (hh y) (D-2*n)
  unfold omega inside; simp_rw [he]
  rw [integral_add ((financed hF tF x D).const_mul _) ((financed hG tG x D).const_mul _), integral_const_mul,integral_const_mul]; ring

lemma scaled (x z : External I n) {t:ℝ} (ht:0<t) (K D : ℂ)
    (hh : ∀ y r,lifting n F (r,y,x)=K*lifting n G (t*r,t • y,z)) :
    omega n F x D = (t:ℂ)^(-D) * K * omega n G z D := by
  obtain ⟨hi,hj,hf,hu⟩:=coast hF tF n; obtain ⟨-,hl,hg,hk⟩:= coast hG tG n
  have he y := Radial.relative hi hj hf hu hl hg hk
    (mem_prod.mpr ⟨mem_univ y,mem_univ x⟩) (mem_prod.mpr ⟨mem_univ (t • y),mem_univ z⟩) ht K (hh y) (D-2*n)
  let g y:= dimensional (lifting n G) (y,z) (D-2*n)
  unfold omega inside; simp_rw [he]; rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg _ g _ (hR:=ht.le)]
  rw [Complex.real_smul, show Module.finrank ℝ (place n)=2*n from finrank_euclideanSpace_fin, Complex.ofReal_inv,Complex.ofReal_pow]
  have ht' : (t:ℂ)≠0:= Complex.ofReal_ne_zero.mpr ht.ne'
  rw [show -(D-2*n)= -D+((↑(2*n:ℕ)):ℂ) by push_cast; ring,Complex.cpow_add _ _ ht',Complex.cpow_natCast]
  unfold g; field_simp

lemma nat_scale (x:External I n) (K D : ℂ) (hh : ∀ y r,lifting n F (r,y,x)=K*lifting n G (r,y,x)) :
    omega n F x D=K*omega n G x D:=by simpa using (scaled hF tF hG tG x x zero_lt_one K D (by simpa using hh))
end YM.MSbar.Pole.Ambient
