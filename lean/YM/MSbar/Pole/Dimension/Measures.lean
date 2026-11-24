import YM.MSbar.Pole.Dimension.Advance
import YM.MSbar.Pole.Dimension.Range
import Mathlib.Analysis.MellinTransform

/-! # Scale dependence of a dimensional subintegral. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "T" => Ioi (0:ℝ)
local notation "ω" => volume.restrict T
variable {U : Set E} {p q p' q' p'' q'' : Price E} {f g H: ℝ×E→ℂ}
variable (o : IsOpen U) (c : ContinuousOn p.val U)
  (hf : Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) f) (ef : EvenOn U f)
  (d : ContinuousOn p'.val U)
  (hg : Packet (univ ×ˢ U) (p'.back Prod.snd) (Moment q') g) (eg : EvenOn U g)
  {x y : E} (hx : x∈U) (hy : y∈U)
include o c hf ef hx d hg eg hy
lemma relative {t:ℝ} (ht : 0 < t) (K : ℂ) (hm : ∀ r : ℝ,f (r,x)= K * g (t*r,y))
    (w : ℂ) : dimensional f x w=(t:ℂ)^(-w)*K*dimensional g y w:= by
  let k:=shed w; let W(n:ℕ):= w+2*n
  let F (n:ℕ)(r:ℝ):= (higher^[n]) f (r,x); let G (n:ℕ)(r:ℝ):= (higher^[n]) g (r,y)
  let b(n:ℕ):= ((t:ℂ)^2)^n*K
  have ha (n:ℕ) : ∀ r:ℝ, F n r=b n*G n (t*r):= by
    induction n with
    | zero => intro r; simpa [F,G,b] using hm r
    | succ n ih =>
      obtain ⟨hk,h₁⟩:= all_higher o c hf ef n; obtain ⟨hl,h₂⟩:= all_higher o d hg eg n
      have Hv (r : ℝ) (hr : r ≠ 0) : F (n+1) r= b (n+1)*G (n+1) (t*r) := by
        have hu := formula h₁ hk r hx; have hv := formula h₂ hl (t*r) hy
        have hh := (letter_read h₂ (t*r) hy).scomp r (show HasDerivAt (fun z:ℝ => t*z) t r by simpa using (hasDerivAt_id' r).const_mul t)
        have he := (letter_read h₁ r hx).unique ((hh.const_mul (b n)).congr_of_eventuallyEq (Eventually.of_forall fun r'=> ih r'))
        rw [show b (n+1)= (t:ℂ)^2*b n by unfold b; rw [pow_succ]; ring]
        unfold F G; rw [iterate_succ_apply',iterate_succ_apply', alt_of_ne h₁ hk hr hx,alt_of_ne h₂ hl (mul_ne_zero ht.ne' hr) hy,he]
        simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_ofNat,Complex.ofReal_mul]; field_simp
      have H₁ : Continuous (F (n+1)) := continuous_iff_continuousAt.mpr fun r=> (letter_read (all_higher o c hf ef (n+1)).2 r hx).continuousAt
      have H₂ : Continuous (G (n+1)) := continuous_iff_continuousAt.mpr fun r=> (letter_read (all_higher o d hg eg (n+1)).2 r hy).continuousAt
      intro r; by_cases hr : r=0
      · subst r
        apply tendsto_nhds_unique_of_eventuallyEq (H₁.continuousAt (x:=0)|>.continuousWithinAt (s:={(0:ℝ)}ᶜ)) ((show Continuous (fun r=> b (n+1)*G (n+1) (t*r)) from by fun_prop).continuousAt (x:=0)|>.continuousWithinAt)
        exact mem_of_superset self_mem_nhdsWithin Hv
      exact Hv r hr
  have hb (A : ℝ→ℂ) : j A (W k)=Half (W k)*mellin A (W k) := by unfold j Half mellin; rw [div_eq_mul_inv]; simp_rw [smul_eq_mul,mul_comm (A _)]
  change j (F k) (W k)=(t:ℂ)^_ * K * j (G k) _
  rw [hb,hb,show F k=fun r=>b k* G k (t*r) from funext (ha k)]
  have h₃ : mellin (fun r : ℝ=>b k* G k (t*r)) (W k)= b k*mellin (fun r:ℝ=> G k (t*r)) (W k):=by unfold mellin; simp_rw [smul_eq_mul, mul_left_comm _ (b k),integral_const_mul]
  have ht' : (t:ℂ)≠0:= by exact_mod_cast ht.ne'
  rw [h₃,mellin_comp_mul_left _ _ ht]
  have hW : (t:ℂ)^(-(W k))=(t:ℂ)^(-w)* ( ( (t:ℂ)^2)^k)⁻¹ := by
    unfold W; rw [neg_add',sub_eq_add_neg,Complex.cpow_add _ _ ht']; congr 1
    rw [Complex.cpow_neg,Complex.cpow_mul_nat]; simp
  rw [smul_eq_mul,hW]; unfold b; field_simp

omit hy in
lemma linear (u v : ℂ) (hp : Packet (univ ×ˢ U) (p''.back Prod.snd) (Moment q'') H) (ep : EvenOn U H)
    (hb : ContinuousOn p''.val U) (hh : ∀ t:ℝ,H (t,x)=u*f (t,x)+v*g (t,x)) (w : ℂ) :
    dimensional H x w = u*dimensional f x w+v*dimensional g x w:=by
  have ht (k : ℕ): ∀ t:ℝ,higher^[k] H (t,x)=u*higher^[k] f (t,x)+v*higher^[k] g (t,x) := by
    induction k with
    | zero => exact hh
    | succ k ih =>
      have h₁ := (all_higher o c hf ef k).2; have h₂ := (all_higher o d hg eg k).2; have h₃:=(all_higher o hb hp ep k).2
      have ha (r : ℝ) (hr:r≠0) : higher^[k+1] H (r,x)=u*higher^[k+1] f (r,x)+v*higher^[k+1] g (r,x):=by
        have he := (((letter_read h₁ r hx).const_mul u).add ((letter_read h₂ r hx).const_mul v))
        have ht := (letter_read h₃ r hx).unique (he.congr_of_eventuallyEq (Eventually.of_forall ih))
        simp_rw [iterate_succ_apply',alt_of_ne h₃ (all_higher o hb hp ep k).1 hr hx,alt_of_ne h₁ (all_higher o c hf ef k).1 hr hx,alt_of_ne h₂ (all_higher o d hg eg k).1 hr hx,ht]
        simp only [Complex.real_smul]; ring
      intro r; by_cases hr : r=0
      · subst r; refine tendsto_nhds_unique_of_eventuallyEq ((letter_read (all_higher o hb hp ep (k+1)).2 0 hx).continuousAt.continuousWithinAt (s:={(0:ℝ)}ᶜ))
          ((((letter_read (all_higher o c hf ef (k+1)).2 0 hx).const_mul u).add ((letter_read (all_higher o d hg eg (k+1)).2 0 hx).const_mul v)).continuousAt.continuousWithinAt) (mem_of_superset self_mem_nhdsWithin ha)
      exact ha r hr
  obtain ⟨k,hk⟩ : ∃ k:ℕ, 2 ≤ (w+2*k).re := by obtain ⟨k,hk⟩:= exists_nat_gt (2-w.re); refine ⟨k,?_⟩; simp; linarith
  rw [reached o hb hp ep hx w k hk,reached o c hf ef hx w k hk,reached o d hg eg hx w k hk]; unfold Jstep j
  have hF := before o c (all_higher o c hf ef k).2 hx hk; have hG:=before o d (all_higher o d hg eg k).2 hx hk
  simp_rw [ht,add_mul,mul_assoc]
  rw [integral_add (hF.const_mul _) (hG.const_mul _),integral_const_mul,integral_const_mul]; ring
end YM.MSbar.Pole.Radial
