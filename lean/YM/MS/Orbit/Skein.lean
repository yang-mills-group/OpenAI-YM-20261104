import YM.MS.Orbit.Wheel
/-!
# Wick on finite mode set.Mask.E
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Filter Function Finset Metric MeasureTheory Koszul Plane Heat
open scoped Topology ContDiff
variable {A:Type}{p:Sector A}
namespace Cog
abbrev Grain (A:Type):= A → A →ℂ
variable {S:Cog p}{K L:Grain A}{F H:Raw A ℂ}
abbrev Sym (p:Sector A)(K:Grain A): Prop:= ∀ x y, K x y=cross (p x) (p y)* K y x
abbrev Clear (p:Sector A)(K:Grain A): Prop:=∀ x y,K x y≠0→p x=p y
abbrev phase (S:Cog p)(K:Grain A): Prop:= ∀ x y,K (S.mode x) ( S.mode y )=K x y*( S.spin x * S.spin y )
def axis (S:Cog p): A≃A:= S.perm.toPerm S.mode -- check
-- transforms
abbrev imageW (S:Cog p)(K:Grain A): Grain A:= fun x y=> K x (S.mode y)*S.spin (S.mode y)
lemma image_u (h:S.phase K) (x y:A): imageW S K x y= K (S.mode x) y*S.spin (S.mode x):= by
   unfold imageW; obtain hp:= h x (S.mode y); rw [show S.mode (S.mode y)=y from S.perm y] at hp; rw [hp]; nth_rw 1 [← mul_one (K x (S.mode y)* S.spin (S.mode y))]; rw [← S.holo x]; ring
lemma sym_i (h:S.phase K)(he:Sym p K): Sym p (imageW S K) := fun x y=> by rw [image_u h]; unfold imageW; rw [ he (S.mode x), S.vivid,mul_assoc ]
lemma phase_i (hp:S.phase K): S.phase (imageW S K):= by intro x y; rw [ image_u hp ]; unfold imageW; rw [ show S.mode (S.mode x)=x from S.perm x ]; linear_combination (norm:=ring) -(K x (S.mode y)*S.spin x ) * S.holo y
lemma clear_i (hp:Clear p K): Clear p ( imageW S K ):= fun i j h=> ( hp i (S.mode j) (left_ne_zero_of_mul (b:=S.spin (S.mode j)) h) )|>.trans ( S.vivid j ) -- left_ne
abbrev Cascade (S:Cog p)(K:Grain A):= K+imageW S K
abbrev CCarry (S:Cog p)(K:Grain A): Prop:= ∀ x y,K x (S.mode y)= K x y*S.spin y
abbrev RCarry (S:Cog p)(K:Grain A): Prop:= ∀ x y,K (S.mode x) y=K x y*S.spin x
lemma Cc (S:Cog p)(K:Grain A): S.CCarry (Cascade S K):= by intro i j; unfold Cascade imageW; simp only [Pi.add_apply, show S.mode (S.mode j)=j from S.perm j]; linear_combination (norm:=ring_nf) -( K i (S.mode j) ) * S.holo j
lemma Rc ( hp:S.phase K ): S.RCarry (Cascade S K):= by intro x y; unfold Cascade; simp_rw [Pi.add_apply,image_u hp,show S.mode (S.mode x)=x from S.perm x]; linear_combination (norm:=ring_nf) -(K (S.mode x) y)* S.holo x
lemma symC (h:S.phase K)(hp:Sym p K): Sym p (Cascade S K) := fun x y=> by simp only [Cascade,Pi.add_apply]; rw [sym_i h hp x y, hp x y,mul_add]
lemma clearC (hp:Clear p K): Clear p (Cascade S K):= fun x y h=> Classical.byContradiction fun he=> h (by unfold Cascade; simp only [Pi.add_apply]; rw [ show K x y=0 from Classical.byContradiction fun v=> he ( hp x y v ), show S.imageW K x y=0 from Classical.byContradiction fun v=> he ( clear_i hp x y v ), zero_add ] )
-- Wick matrices
variable [Fintype A]
abbrev frame (K:Grain A): Op A ℂ := ∑ i:A,∑ j:A,K i j • diffPair i j
def conn (p:Sector A)(K:Grain A): Raw A ℂ→Raw A ℂ→Raw A ℂ:= link ( frame K ) false p
local notation "Cr"=> conn p
lemma frame_add (K H:Grain A) : frame (K+H)=frame K+frame H := by simp only [frame,Pi.add_apply, add_smul,Finset.sum_add_distrib]
abbrev imageV (S:Cog p)(b:Bool)(K:Grain A):= if b then S.Cascade K else K
lemma fr_stretch {k:A→ℂ} (h:∀ x,k (S.mode x)=k x*S.spin x) (u:Raw A ℂ): (∑ i:A,k i • blend S ((2:ℂ)⁻¹) ((2:ℂ)⁻¹) i u)=∑ i:A,k i • D i u := by
   have he : ∑ i:A,k i • S.spin i • D (S.mode i) u =∑ i:A,k i • D i u := by simp_rw [ ← mul_smul, ← h ]; exact Equiv.sum_comp S.axis (fun j=> k j • D j u)
   simp_rw [ blend_at,mul_smul, smul_add,smul_comm (k _) ((2:ℂ)⁻¹), Finset.sum_add_distrib, ← Finset.smul_sum,he,← add_smul ]; norm_num
lemma fr_read2 (hc:S.CCarry K)(i:A)(u:Raw A ℂ) : ∑ j:A,K i j • D j (S.look u) = S.look (∑ j:A, K i j • D j u):= by simp_rw [ wheel_rule, ← map_smul S.look, ← map_sum S.look, fr_stretch (hc i) u ]
lemma direct_read (hx: S.CCarry K)(he:S.RCarry K)(F:Raw A ℂ): frame K (S.look F)=S.look (frame K F):= by
   conv_lhs=> simp only [frame,LinearMap.sum_apply, LinearMap.smul_apply, diffPair_apply]
   simp_rw [show ∀ i:A,D i (S.look F) = _ from (fun i=>wheel_rule S ((2:ℂ)⁻¹) _ i), fr_read2 hx, ← map_sum]; -- unfolds self twice? watch
   apply congr_arg; unfold frame; simp only [ LinearMap.sum_apply, LinearMap.smul_apply, diffPair_apply ]; rw [ Finset.sum_comm ]; -- arrange both by j.Conv
   conv_rhs=> rw [Finset.sum_comm]
   simp_rw [← map_smul (D _), ← map_sum (D _)]; apply Finset.sum_congr rfl; intro i _; -- maybe D_x inward
   exact congr_arg (D i) (fr_stretch (k:=fun j=>K j i) (fun x=>he x i) F)
lemma direct_link (hx:S.CCarry K)(he:S.RCarry K): Cr K (S.look F) (S.look H)= S.look ( Cr K F H ):= by unfold conn link; simp only [sign_id,map_sub]; rw [ ← rotate_p,direct_read hx he,direct_read hx he,direct_read hx he, ← rotate_p, ← rotate_p ]
lemma phase_mirror (h:S.phase K)(F:Raw A ℂ): frame K (S.mirror F)=S.mirror (frame K F):= by
   unfold frame; conv_lhs=> simp only [LinearMap.sum_apply,LinearMap.smul_apply,diffPair_apply]
   simp_rw [reflect S, map_smul (D _), reflect S]; -- inside D nested simp? simp_rw initial reflect tries twice if both rewrite possible
   have hx (x y:A): K x y • S.spin x • (S.spin y • S.mirror ( D (S.mode y) ( D (S.mode x) F )))=S.mirror ( K (S.mode x) (S.mode y) • (diffPair (S.mode x) (S.mode y) F) ):= by rw [h,diffPair_apply,map_smul,mul_smul,mul_smul]
   simp_rw [ hx, ← map_sum, LinearMap.sum_apply,LinearMap.smul_apply ]; apply congr_arg; simp_rw [ show ∀ x:A, (∑ i:A,K x (S.mode i) • diffPair x (S.mode i) F) =∑ i:A,K x i • diffPair x i F from fun x=>Equiv.sum_comp S.axis (fun j=> K x j • diffPair x j F) ]; exact Equiv.sum_comp S.axis (fun x=>∑ i:A,K x i • diffPair x i F)
lemma phase_link (h:S.phase K) : Cr K (S.mirror F) (S.mirror H)= S.mirror (Cr K F H):= by unfold conn link; simp only [sign_id,map_sub]; rw [ ← rotate_p,phase_mirror h,phase_mirror h,phase_mirror h, ← rotate_p, ← rotate_p ]
end Cog
end YM.MS.Orbit
