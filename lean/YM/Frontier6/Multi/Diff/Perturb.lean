import YM.Frontier6.Multi.Comparable.Outposts
import YM.Frontier6.Exact.CostStep

/-!
# Stencils and the costs of moving along deep meshes

First free calculus: perturbations charged at any strict power saving so
asymptotic lower bounds and the shared-value assertion persist. Use open as well
as closed interpolation stencils later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Finset Set MergeProof.Ribbons MergeProof.Acme Fareway
open scoped Topology BigOperators ContDiff Classical
variable {I J V X Y:Type}{G:Gauge}{C:Family G}{T : Fareway I}
variable {x y z v:I→ E4} {a b c:ℝ}
namespace Fareway
lemma Mint.sandwich {T:Fareway I}{f g h:I→ℝ}(hf:T.Mint f a)(hg:T.Mint g a) (hv:f≤ᶠ[T.via] h)(hp:h≤ᶠ[T.via]g): T.Mint h a:=by
    have he: ∀ᶠ i in T.via,0 < h i:= (hf.pos.and hv).mono fun i hi=> hi.1.trans_le hi.2
    refine ⟨he, tendsto_of_tendsto_of_tendsto_of_le_of_le' hf.pitch hg.pitch ?_ ?_⟩
    · filter_upwards [hv,hf.pos,T.ahead] with i hi hp h; exact div_le_div_of_nonneg_right (Real.log_le_log hp hi) h.le
    filter_upwards [hp,he,T.ahead] with i hi hp h; exact div_le_div_of_nonneg_right (Real.log_le_log hp hi) h.le
section
variable {X Y:Type*}[SeminormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ Y]
lemma Mint.with_change {f g:I→X}(hf:T.Mint (fun i=>‖f i‖) a)(hg:T.Costs g b) (he:b<a): T.Mint (fun i=>‖f i + g i‖) a:=by
   let V i:=‖f i‖/2; have hv:T.Mint V a:= (hf.div (T.minted_c 2 two_pos)).eq (sub_zero _); have hP:=hg.from_allowance hv he
   let W i:=‖f i‖+V i; refine Mint.sandwich hv (hf.common hv) ?_ ?_
   · filter_upwards [hP] with i hi; have he:= norm_sub_norm_le (f i) (-g i); rw [sub_neg_eq_add,norm_neg] at he; unfold V at *; linarith only [he,hi]
   filter_upwards [hP] with i hi; exact (norm_add_le ..).trans (add_le_add le_rfl hi)
lemma Costs.scalarR₀ {f:I→Y}{s:I→ℝ}(h:T.Costs f a)(hv:T.Costs s b):T.Costs (fun i=> s i • f i) (b+a):= hv.coordinated h _ <| Eventually.of_forall fun _=>(norm_smul ..).le
end
end Fareway
lemma ReachWide.mono (h:ReachWide T x y a)(he:a≤b): ReachWide T x y b:= fun c hc=>h c (he.trans_lt hc)
lemma ReachWide.flip (h:ReachWide T x y a):ReachWide T y x a:=fun _ hb=>(h _ hb).mono fun i hi=>(show _ ≤ ‖y i - x i‖ from hi.trans_eq (norm_sub_rev ..))
lemma reach_mint (h:T.Mint (fun i=>‖x i-y i‖) (-a)): ReachWide T x y a:= fun c hc=> ((T.minted (-c)).cheaper h (by linarith)).mono fun i hi=> hi.le
lemma Aspect.wide {x:I→ V→ E4}(h:Aspect T x): Wide T x 1:=fun _ _ hi=> reach_mint (h.2 hi)
lemma Wide.higher {x:I→ V→ E4}(h:Wide T x a)(ha:a≤b):Wide T x b:=fun _ _ hi=> (h hi).mono ha
lemma Wide.injective {x:I→V→E4}[Finite V](h:Wide T x a):∀ᶠ i in T.via,Injective (x i):=by
    filter_upwards [eventually_all.mpr (fun j:V=>eventually_all.mpr (fun k:V=>eventually_all.mpr fun ht:j≠k=> h ht (a+1) (lt_add_one _)))] with i hi j k ht
    by_contra he; have hh:= hi j k he; rw [ht,sub_self,norm_zero] at hh; linarith only [hh,Real.exp_pos (T.scale i * -(a+1))]
lemma ReachWide.motion (h:ReachWide T x y a)(hz:T.Costs z (-b))(he:b>a): ReachWide T (fun i=> z i+x i) y a:= by
   intro d hd; obtain ⟨c,hc,hc'⟩:= exists_between (lt_min he hd)
   let f (a:ℝ)(i:I) := Real.exp (T.scale i*(-a)); let g i:= f c i/2; have hm:T.Mint g (-c):= (T.minted (-c)|>.div (T.minted_c 2 two_pos)).eq (sub_zero _)
   filter_upwards [hz.from_allowance hm (neg_lt_neg (hc'.trans_le (min_le_left ..))), h c hc, (T.minted (-d)).cheaper hm (neg_lt_neg (hc'.trans_le (min_le_right ..)))] with i hi hp hu
   have hf:= norm_sub_norm_le (x i-y i) (z i+x i-y i); rw [show x i-y i-(z i+x i-y i)= -z i from (by abel), norm_neg] at hf
   unfold g f at *; linarith only [hi,hp,hu,hf]
lemma Aspect.peal {x y:I→V→ E4}(h:Aspect T x)(he:∀ v:V,T.Costs (fun i=>y i v-x i v) (-a))(ha:1<a):Aspect T y:=by
   constructor
   · intro v; exact (((he v).too (neg_le_neg ha.le)).add (h.1 v)).cf (Eventually.of_forall fun y=> by simp)
   intro i j hi; refine Mint.congr ((h.2 hi).with_change ((he i).sub (he j)) (neg_lt_neg ha)) ?_; filter_upwards with v; congr 1; abel
lemma Wide.concat {N: V→Type} {v:I→∀ i:V,N i→ E4}{u:I→ V→ E4} (he:∀ i,Aspect T (fun k=> v k i))(h:Wide T u a) (hb:a<1): Wide T (fun i (x:Σ j:V,N j) => v i x.1 x.2 + u i x.1) 1:=by
   rintro ⟨i,s⟩ ⟨j,t⟩ hv
   by_cases hi:i=j
   · subst j; simp only; intro c hc; simpa only [add_sub_add_right_eq_sub] using (he i|>.wide (show s≠t from fun h=> hv (congr_arg _ h)) c hc)
   exact (((((h hi).motion ((he i).1 s) hb).flip).motion ((he j).1 t) hb).flip).mono hb.le
lemma Aspect.cf {x y:I→V→ E4} (h:Aspect T x)(he:x=ᶠ[T.via]y): Aspect T y:= ⟨fun j=> (h.1 j).cf (he.mono (fun i hi=>congr_fun hi j)),fun j k hk=> (h.2 hk).congr (he.mono (fun i hi=> by dsimp only; rw [hi]))⟩
lemma Wide.cf {x y:I→V→ E4}(h:Wide T x a)(he:x=ᶠ[T.via]y): Wide T y a:= fun j k hk b hb=> ((h hk b hb).and he).mono (fun i hi=> by dsimp only; rw [←hi.2]; exact hi.1)
-- spherical neighborhoods for induction
variable (T)
def Neighbors (x y:I→ V→ E4)(a:ℝ):Prop:=∀ v,T.Costs (fun i=>y i v-x i v) (-a)
variable {u v w:I→ V→ E4} {T}
lemma Neighbors.rfl : Neighbors T u u a:= fun i=> Fareway.Costs.free.cf (Eventually.of_forall fun i=>by simp)
lemma Neighbors.trans (h:Neighbors T u v a)(he:Neighbors T v w a): Neighbors T u w a:= fun i=> ((h i).add (he i)).cf (Eventually.of_forall fun i=>by simp)
end YM.Frontier6.Road
