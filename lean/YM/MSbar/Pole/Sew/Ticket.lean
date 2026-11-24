import YM.MSbar.Pole.Sew.Amount
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
lemma docks {z:E} (hz:z∈U) (u v : ℂ) (hp : Packet (univ ×ˢ U) (p''.back Prod.snd) (Moment q'') H) (ep : EvenOn U H)
    (hb : ContinuousOn p''.val U) (hh : ∀ t:ℝ,H (t,x)=u*f (t,y)+v*g (t,z)) (w : ℂ) :
    dimensional H x w = u*dimensional f y w+v*dimensional g z w:=by
  have ht (k : ℕ): ∀ t:ℝ,higher^[k] H (t,x)=u*higher^[k] f (t,y)+v*higher^[k] g (t,z) := by
    induction k with
    | zero => exact hh
    | succ k ih =>
      have h₁ := (all_higher o c hf ef k).2; have h₂ := (all_higher o d hg eg k).2; have h₃:=(all_higher o hb hp ep k).2
      have ha (r : ℝ) (hr:r≠0) : higher^[k+1] H (r,x)=u*higher^[k+1] f (r,y)+v*higher^[k+1] g (r,z):=by
        have he := (((letter_read h₁ r hy).const_mul u).add ((letter_read h₂ r hz).const_mul v))
        have ht := (letter_read h₃ r hx).unique (he.congr_of_eventuallyEq (Eventually.of_forall ih))
        simp_rw [iterate_succ_apply',alt_of_ne h₃ (all_higher o hb hp ep k).1 hr hx,alt_of_ne h₁ (all_higher o c hf ef k).1 hr hy,alt_of_ne h₂ (all_higher o d hg eg k).1 hr hz,ht]
        simp only [Complex.real_smul]; ring
      intro r; by_cases hr : r=0
      · subst r; refine tendsto_nhds_unique_of_eventuallyEq ((letter_read (all_higher o hb hp ep (k+1)).2 0 hx).continuousAt.continuousWithinAt (s:={(0:ℝ)}ᶜ))
          ((((letter_read (all_higher o c hf ef (k+1)).2 0 hy).const_mul u).add ((letter_read (all_higher o d hg eg (k+1)).2 0 hz).const_mul v)).continuousAt.continuousWithinAt) (mem_of_superset self_mem_nhdsWithin ha)
      exact ha r hr
  obtain ⟨k,hk⟩ : ∃ k:ℕ, 2 ≤ (w+2*k).re := by obtain ⟨k,hk⟩:= exists_nat_gt (2-w.re); refine ⟨k,?_⟩; simp; linarith
  rw [reached o hb hp ep hx w k hk,reached o c hf ef hy w k hk,reached o d hg eg hz w k hk]; unfold Jstep j
  have hF := before o c (all_higher o c hf ef k).2 hy hk; have hG:=before o d (all_higher o d hg eg k).2 hz hk
  simp_rw [ht,add_mul,mul_assoc]
  rw [integral_add (hF.const_mul _) (hG.const_mul _),integral_const_mul,integral_const_mul]; ring
end YM.MSbar.Pole.Radial

namespace YM.MSbar.Pole
open Set Function Filter MeasureTheory Ambient Momentum Age Mellin place Symbol Radial
open scoped Topology ContDiff BigOperators Classical Real
variable {I : Type} [Fintype I]

/-- Screened value respects external slots as scalar function at fixed free momentum. -/
structure Signature (X V:Finset I) (F : Screened I) : Prop where
  listens n p (x y : External I n) : (∀ i∈X,x i=y i) → F n (p,x)=F n (p,y)
  tone i : i∈V → ∀ n p (x:External I n), Along fun v=> F n (p,update x i v)
namespace Sew
open Tip Thread
variable (T : Thread I) {F : Cloud I} {H : Screened I}
lemma lineage (p : Texture H) (h : Breezes H) {n:ℕ} (D : ℂ) (x y z: External I n) (u v:ℂ)
    (hh : ∀ q t, lifting n H (t,q,x)= u*lifting n H (t,q,y)+v* lifting n H (t,q,z)): omega n H x D=u*omega n H y D+v*omega n H z D:=by
  let q:Price (place n × External I n):= (ticket (@id (External I n))).back (@Prod.snd _ _)
  let V:= Domain n (univ:Set (External I n)); let K:=lifting n H; let w:=D-2*n
  have ho : IsOpen V:=isOpen_univ.prod isOpen_univ; have hp:= aboveAxis (n:=n) h; have hv : EvenOn V K := fun x _=> symmetric p _ _ (mem_univ _)
  have hq : ContinuousOn q.val V:=continuousOn_const.add continuousOn_snd.norm
  have he (i:place n): dimensional K (i,x) w=u*dimensional K (i,y) w+v*dimensional K (i,z) w:= docks ho hq hp hv hq hp hv (mem_prod.mpr ⟨mem_univ i,mem_univ x⟩) (mem_prod.mpr ⟨mem_univ i,mem_univ y⟩) (mem_prod.mpr ⟨mem_univ i,mem_univ z⟩) u v hp hv hq (hh i) w
  unfold omega inside; change ((π:ℂ)^n)⁻¹*(∫ i, dimensional K (i,x) w)=_
  simp_rw [he]
  have hh : Integrable (fun i:place n=> dimensional K (i,y) w) := financed h p y D
  have hm : Integrable (fun i:place n=> dimensional K (i,z) w) := financed h p z D
  rw [integral_add (hh.const_mul _) (hm.const_mul _),integral_const_mul,integral_const_mul]; unfold K w; ring
lemma loved (p : Texture H) (h : Breezes H) {X V:Finset I} (hg : Signature X V H) (D : ℂ) : Shape X V (fun n x=> omega n H x D) := by
  constructor
  · intro n x y hx
    simpa only [one_mul,zero_mul,add_zero] using (lineage p h D x y y 1 0 (fun i t=>by simp only [one_mul,zero_mul,add_zero]; exact hg.listens (n+1) _ _ _ (fun j hj=>congr_arg (pad n) (hx j hj))))
  intro i hi n x
  have ht (w : place n) : pad n ∘ update x i w = update (pad n∘x) i (pad n w):= by funext l; by_cases h:l=i; subst l; simp; simp [h]
  constructor
  · intro a b; simpa only [one_mul] using (lineage p h D (update x i (a+b)) (update x i a) (update x i b) 1 1 (fun y t=> by
       change H (n+1) (_,pad n ∘ update _ i _) = 1* H _ (_,pad n ∘ update _ i _) + 1 * H _ (_,pad n∘update _ i _); rw [one_mul,one_mul,ht,ht,ht,map_add]; exact (hg.tone i hi ..).add _ _))
  intro r a; simpa only [Complex.real_smul,zero_mul,add_zero] using! (lineage p h D (update x i (r • a)) (update x i a) x (r:ℂ) 0 (fun y t=>by
    rw [zero_mul,add_zero,← Complex.real_smul]; unfold lifting; rw [ht,ht,map_smul]; exact (hg.tone i hi ..).smul _ _))
end Sew
end YM.MSbar.Pole
