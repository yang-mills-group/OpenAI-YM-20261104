import YM.FVA2.MixedTune
import YM.MS.City.Moves
import YM.MS.Tone.Egal
import YM.MS.Image.Atlas
/-!
# Remaining freedom to choose top frame equivariantly

Below only needs unmarked covariances on `net=0`; needs marked covariances
without that condition. Real compact group is unchanged on each family.
-/
set_option autoImplicit false
set_option maxHeartbeats 830000
noncomputable section
namespace YM.MS.SpinCode
open Function Filter Set Finset Plane Koszul Flux MeasureTheory City High
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect
open Complex (I)
open Book Convolve Program Native.Wilsonian Native.Paint
open Native.Orient
open scoped Topology ContDiff Pointwise
variable {G:Gauge} (s:Signed) {i j:Axis} {b:Bool}{F M H: Landau.Detect.Law G}{l:List (Lane4 G)}

def backlit (s:Signed) : Law G →ₗ[ℂ] Law G:= (Arts.flagS (m:=0) (Outlook.hand s) G).beam
lemma awarded (l:List (Lane4 G))(f: Law G): backlit s f l= SideS s l * f (l.map (permute s)):=Outlook.hand_index ..
lemma pinΓ (x:Dot G Lattice.Cover): backlit s (run (pose s x))=run x:= by funext i; rw [awarded, by_shift, ← mul_assoc, (show SideS s i*(i.map (negateField s)).prod=1 from twice_S s i),one_mul]
structure Carries (K: Flux (BH G) QP ℂ): Prop where
  turns x (i j:BH G): K (passN s i) (passN s j) (s.act x)= tick s i*tick s j*K i j x

lemma K_cpu (G:Gauge) (t:ℝ): Carries s (Cpu G t):= ⟨fun x=> turn_p s x t⟩
lemma K_zone (G:Gauge): Carries s (Kzone G):= by
   refine ⟨ fun x i j=>?_⟩; rw [zeroX, zeroX i j];
   rcases i with ⟨⟨_|a,_|_⟩,p⟩ <;> rcases j with ⟨⟨_|b,_|_⟩,q⟩ <;> simp [tick,negateField,Kzone,Landau.choir,laplace,passN,delta]
   all_goals by_cases h:a=b <;> simp [h,cross_cross]
-- arbitrary right atmosphere; any kernel. directly attaches costs
private lemma at_tree (l r:List (Lane4 G)){K : Flux (BH G) QP ℂ}(he: Carries s K)(h:SignedScope true F) :
 attaches parity K F (backlit s H) l r = SideS s l*SideS s r* attaches parity K F H (l.map (permute s)) (r.map (permute s)):= by
   let N : BH G≃BH G := passN s; let x := -net l
   have hv{a:BH G} : Course true ((a,x)::l):= fun ht=> by simp [x]
   have hn {a:BH G}: F ( (N a,s.act x) :: l.map (permute s))= tick s a * SideS s l * F ((a,x)::l):= by unfold N; rw [← passenger ]; exact oppositeS s h hv
   unfold attaches; dsimp only; rw [repose,← Signed.act_neg, ← Signed.act_neg]; nth_rw 2 [← Equiv.sum_comp N]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; nth_rw 2 [ ← Equiv.sum_comp N ]; rw [Finset.mul_sum];
   have Hk (a:BH G) : parity (N a)=parity a:= back_p s (a,(0:QP))
   have hR : degree (field parity) (l.map (permute s)) = degree (field parity) l := by clear hv hn x; induction l with| nil=>rfl| cons a l ih=> rw [List.map_cons,degree_cons,degree_cons,back_p,ih]
   apply Finset.sum_congr rfl; intro j _; rw [ he.turns ,he.turns,hn,hn,Hk,Hk,hR,awarded,awarded ]; simp only [SideS,List.map_cons,List.prod_cons,tick1,passenger,x,N]; ring_nf; simp only [pow_two,tick2,  show (l.map (negateField s)).prod * (l.map (negateField s)).prod=1 from twice_S s l ]; ring -- tidy
lemma shadow_tree {K:Flux (BH G) QP ℂ}(he: Carries s K)(h:SignedScope true F) : tree parity K F (backlit s H)=backlit s (tree parity K F H):= by
   ext w; rw [awarded,tree,tree,scat_move,show SideS s w * scatter _ w _= _ from (map_smul (allocate (field parity) w) (SideS s w) (fun (a b:List (Lane4 G))=> attaches parity K F H (a.map (permute s)) (b.map (permute s)))).symm ]; refine scatter_congr _ _ _ _ (fun a b hm=>?_); rw [at_tree s a b he h, show SideS s a * SideS s b=SideS s w from by simpa [SideS] using ((split_perm hm).map (negateField s)).prod_eq]; rfl

lemma mist_cc {K:Flux (BH G) QP ℂ}(he: Carries s K) (M: Law G) : backlit s (cycle K μzone M)=cycle K μzone (backlit s M):= by
   ext l; simp only [awarded,cycle]; rw [← (measureVeh s).integral_comp', ← integral_const_mul ]; refine integral_congr_ae (Eventually.of_forall (fun x=>?_)); dsimp only; rw [at_trc,at_trc,← Equiv.sum_comp (passN s), Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [← Equiv.sum_comp (passN s),Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [awarded,show seat s x=s.act x from rfl,he.turns x i j,show SideS s ((i,x)::(j,-x)::l)= tick s i * (tick s j*SideS s l) from rfl,List.map_cons,List.map_cons,passenger,passenger,Signed.act_neg]; ring

open Cylinder Lab
section native
local notation "W"=> Cover
variable {F: Dot G Lattice.Cover} {e:ℤ} {B: Local.Physical.Deck G}{n:ℕ}
lemma shaded (h : Tuned F e): Tuned (pose s F) e := by
    obtain h := h.self_cash ( c:=σ s ) (fun _=>by simp [σ]); -- replace
    exact ⟨ (ferry_tie (R:=ℂ) (p:=Native.Draft.DotFlip) (q:= Draft.DotFlip) (turn s) (fun i=> (pos_par s i).symm)).sym _ h.symm,h.ghost.ferry _ (fun i=> by rcases i with ⟨⟨⟨_|a,_|_⟩,t⟩,x⟩ <;> rfl) _, h.still.passes _ _ ⟩ -- map basis
private lemma paid_color (x:G.El) (F:Dot G W) : graffiti (σ s) (dye x F)=dye x (graffiti (σ s) F):= by
    apply Subtype.ext; funext i; induction i generalizing F with| nil=> simp [Cylinder.tagged, dye_rep]; | cons j i ih=>
       simp only [D_eval j _ , ← enterp]; obtain ⟨⟨a,k⟩,u⟩:=j; rw [tagged_s,solok,solok]; simp_rw [ map_sum,map_smul, tagged_s,map_smul,Finset.smul_sum, sum_stack,Finset.sum_apply,smul_stack,Pi.smul_apply, ih ]; refine Finset.sum_congr rfl fun i ih=>?_ ; exact smul_comm (σ s ((a,k),u)) (wc x k i) _
private def phaseLeft (p:Landau.Atom Axis × Cover): Landau.Atom Axis × Cover:= match p with
     | ((some i,k),x) => ((some (s.perm i),k),(purse s (x,i)).1)
     | ((none,k),x)=> ((none,k),s.act x)
lemma tinges (x:G.El)(F: Dot G Cover) : pose s (dye x F)= dye x (pose s F):= by
    unfold pose; rw [ LinearMap.comp_apply,LinearMap.comp_apply,paid_color ]; exact paint_pass (stripe G Cover) x (stripe G Cover) (turn s) (phaseLeft s) (fun x j=> by rcases x with ⟨⟨_|a,_|_⟩,r⟩ <;> rfl) _
lemma tinting (h:Colorless F) : Colorless (pose s F):= fun x=> by rw [← tinges,h x]
lemma ceiling (h:Limit F.val e) : Limit (pose s F).val e:= by
    show Limit ((Ferry _ (graffiti _ F)).val) e; apply Limit.shades; intro l he; rw [landc,Cylinder.rent,h l he,mul_zero]
end native
end YM.MS.SpinCode
