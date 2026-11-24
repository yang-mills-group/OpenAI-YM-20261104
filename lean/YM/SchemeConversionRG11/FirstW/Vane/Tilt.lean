import YM.SchemeConversionRG11.FirstW.Vane.Tower
/-! Local θ-gradient cancellation (CT uses Signed equivariant cutoff on vertices, ticket-multisets). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {G : Gauge} {X : Type*} [AddCommGroup X] [One X] {n : Side}
-- polar version of the Ward identity, retaining all positions of C. normalization −1/16 tower, plus 2 from advection
lemma podium (u v z : G.Color) : inner ℝ v (G.ad u z) + inner ℝ z (G.ad u v) = 0 := by
  rw [← real_inner_comm z (G.ad u v)] -- signature reversed!
  rw [G.ad_skew]; ring
lemma spire_grad (x : Four X) (i j : Step) (e : Four X→G.Color) (A : Wind G X) :
  spire G x (icon i j) A (momentE e)= G.ad (e x) (rail x (icon i j) A)-rail x (icon i j) (shiftT e A) := by
  rw [spire,LinearMap.smul_apply,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.add_apply,LinearMap.flip_apply]
  have h:= turn_inter e x (icon i j) A; rw [icon_stop,map_add,LinearMap.add_apply, ← two_smul ℝ (G.ad (e x) (rail x (icon i j) A))] at h -- syntax
  rw [eq_sub_of_add_eq h, smul_sub,smul_smul, smul_smul]; norm_num
lemma tower_shift (e : Four X→G.Color) (A B : Wind G X) (x) (i j : Step) :
   tower G x (icon i j) A B (momentE e) = (1/48)*(inner ℝ (rail x (icon i j) A) (rail x (icon i j) (shiftT e B))+inner ℝ (rail x (icon i j) B) (rail x (icon i j) (shiftT e A))) := by
   rw [tower_eq, reads_mom, icon_stop,sub_self,inner_zero_left,add_zero, spire_comm x _ _ A,spire_grad,spire_grad,inner_sub_right,inner_sub_right]
   linarith only [podium (e x) (rail x (icon i j) A) (rail x (icon i j) B)]
lemma patch_back (w : Walk) (x : Four X) (i j : Axis) : stop x (patch w i j)=x := by rw [patch, stop_append,stop_append,square_stop,reverse_stop]
lemma bare_turn (j : ℕ) (x : Four X) (e : Four X → G.Color) (hx:e x=0) (A : Wind G X) :
    rush G x j (momentE e) A +rush G x j A (momentE e) + (2:ℝ) • Bare.wideCore G j x (shiftT e A) = 0 := by
  funext i a p
  have H s : swerve x (patch (Bare.walk p s) i a) (momentE e) A +swerve x (patch (Bare.walk p s) i a) A (momentE e) + (2:ℝ) • Bare.wideCurl (shiftT e A) (x+∑ i∈s, step (p i)) i a=0 := by
    rw [add_comm (swerve x (patch (Bare.walk p s) i a) (momentE e) A)]; have h:= turn_inter e x (patch (Bare.walk p s) i a) A; simp only [patch_back,hx, add_zero,map_zero,LinearMap.zero_apply, patched,Bare.displaced] at h; exact h
  simp only [Pi.add_apply,Pi.smul_apply,rush,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.smul_apply,Bare.wideCore_apply, ← smul_add]
  let f :=(↑j.factorial:ℝ)⁻¹
  rw [smul_comm (2:ℝ) f, ←smul_add]; change f • _=0
  rw [Finset.smul_sum, ←Finset.sum_add_distrib,←Finset.sum_add_distrib, Finset.sum_eq_zero]; exact smul_zero _
  intro w _; rw [smul_comm (2:ℝ) (Bare.sign w), ←smul_add,←smul_add,H,smul_zero]
lemma turn_cost (e : Four X → G.Color) (s : Signed) (A : Wind G X) : Bare.wideLink G s (shiftT e A)= shiftT (e ∘ s.act) (Bare.wideLink G s A) := by
  funext l; rcases l with ⟨b,i⟩
  let d:= (posDir i).rotate s; let m : Edge (Four X) := (b,i)
  have hB (B : Wind G X) : Bare.wideLink G s B (b,i)= boardAt (s.act b) d B := by rw [Bare.wideLink_apply]; rfl
  have hv : s.act (b+ (step i : Four X)) = s.act b + d.vec := by simp only [s.act_add,d,Step.vec_rotate,Step.vec_pos]
  rw [hB]; apply (smul_right_injective (R:=ℝ) _ (two_ne_zero)) -- name/sign
  dsimp only; rw [leg_shiftT]; unfold shiftT; simp only [LinearMap.pi_apply,LinearMap.comp_apply,comp_apply,hv,LinearMap.smul_apply,LinearMap.proj_apply,hB,smul_smul]; norm_num
set_option maxHeartbeats 400000 in
lemma wide_turn (A : Wind G X) (e : Four X → G.Color) (x) (j) (he : e x=0) : sheer G j x A (momentE e)+sheer G j x (momentE e) A = (-2:ℝ) • (Bare.wideLinear G j 1 x (shiftT e A)) := by
  simp only [sheer_eq,Bare.wideLinear,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,one_zpow,one_smul,←smul_add]
  rw [smul_comm (-2:ℝ),Finset.smul_sum,←Finset.sum_add_distrib]; apply congrArg _; refine Finset.sum_congr rfl (fun s _=>?_); simp only [tilted, ←map_add,←map_smul,turn_cost]
  let u:=affine s⁻¹ 0 x
  have hu := bare_turn j u (e ∘ s.act) (by simp [he,u,affine]) (Bare.wideLink G s A)
  unfold u at hu; rw [add_comm (rush G _ j (Bare.wideLink G s A) (momentE (e ∘ s.act))), eq_neg_of_add_eq_zero_left hu]; simp only [map_smul,map_neg,neg_smul]
lemma contact_shear (A : Wind G X) (e : Four X→ G.Color) (x) (k : Labels.Key G) (he:e x=0) :
  2* echoAt x k A (momentE e) = - native k x (shiftT e A) := by
  have h:= wide_turn A e x k.fst he
  simp only [echoAt,LinearMap.compr₂_apply,glint_once,h,map_smul,native,tape,LinearMap.comp_apply,smul_eq_mul]; ring
end YM.RG11.FirstW
