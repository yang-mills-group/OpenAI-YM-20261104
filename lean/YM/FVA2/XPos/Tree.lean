import YM.XSpace.Regulated
import YM.FVA2.Orbit.TreeChoice
/-!
# XSpace.Initialize's top Tree is permitted on the inversion orbit

Even side, reps might disagree by orientation. Strict algebraic criterion. No assumption on
chosen XSpace root & same `Root` of the *gauge parameters* (at the fixed site 0), i.e. subtract
the constant angle accordingly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.XPos
open Function Set Filter Finset MeasureTheory Lattice Wilson
open Orbit Orbit.Grove XSpace
open PertExtension PertExtension.Orb
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {R:XSpace.Period}(T:R.Tree)
local notation "V" => Rep G R.side
local notation "J" => OEdge R.side
local notation "U" => Edge (Site R.side)
local notation "C" => G.Color
local notation "A" => T.Field G
variable (R)
def enc : OEdge R.side ≃ R.Link where
   toFun i := R.rep i.val
   invFun i:= index i.val
   left_inv i := by
     apply Subtype.ext; change eR ((R.rep i.val).val) = _; rcases Classical.em (R.Chosen i.val) with hi|hi; rw [R.rep_chosen _ hi, i.property]; rw [R.rep_other _ hi]; exact (eR_reflect i.val).trans i.property -- definitional reflect
   right_inv i := by
     change R.rep (eR i.val)=i; rcases eR_spec i.val with h|h; rw [h, R.rep_fixes]; rw [h]; exact (R.rep_reflect _).trans ( R.rep_fixes i )
variable {R}
-- predicate, both accessible via `num`
def Marked (i: OEdge R.side) := (enc R i)∈ T.edges
local notation "S" => Marked T
def num (P:R.Link→ Prop) : {x: OEdge R.side // P (enc R x)} ≃ {x:R.Link // P x}:= Equiv.subtypeEquiv (enc R) (fun _=> Iff.rfl)
abbrev Descend (T:R.Tree) := {i:OEdge R.side // Marked T i}
abbrev Beyond (T:R.Tree) := {i:OEdge R.side // ¬ Marked T i}
local notation "W" => Beyond T
local notation "N" => Descend T

def portal : Beyond T ≃ T.Free:= num (fun x=> x∉ T.edges)
def cap : Descend T ≃ (T.edges) := num (fun x=> x ∈ T.edges)
def flux (G:Gauge)(i: OEdge R.side) : G.Color≃ₗ[ℝ] G.Color:= if R.Chosen i.val then LinearEquiv.refl _ _ else LinearEquiv.neg _
lemma signs (x: R.Link→ G.Color) (i:J) : R.extend x i.val= flux G i (x (enc R i)):= by unfold XSpace.Period.extend flux; split <;> rfl

def screen (G: Gauge): T.Field G≃ₗ[ℝ] Complement G (Marked T) where
    __ := LinearMap.pi (fun i=> (flux G i.val) ∘ₗ LinearMap.proj (portal T i))
    invFun z i:= (flux G ((portal T).symm i).val).symm (z ((portal T).symm i))
    left_inv x:= by funext i; simp [LinearMap.pi_apply]
    right_inv x:= by funext i; simp [LinearMap.pi_apply]
lemma screen_keep (x:A)(i:W): (screen T G) x i= T.covering x i.val.val:= by
    change flux G i.val (x ( portal T i )) = R.extend _ _
    rw [signs]; exact congr_arg (flux G i.val) (T.prolong_free _ (portal T i)).symm
lemma lit_angle (x:A)(i:J): T.covering x i.val= (rise S (screen T G x)) i:= by
    by_cases hi: S i
    · have he:=congr_fun (rise_nil S (screen T G x)) ( ⟨ i,hi⟩ : Descend T ); change R.extend _ _ = _; rw [signs,show T.prolong x (enc R i)=0 from dif_pos hi,map_zero]; exact he.symm
    exact (screen_keep T x (⟨i,hi⟩:Beyond T)).symm.trans (congr_fun (rise_up S (screen T G x)) ( ⟨i,hi⟩:Beyond T )).symm
lemma screen_path (x:A): ignite (rise S (screen T G x)) = T.links x := by
    let Q:Pert.Orb.Potential G R.side:= ⟨T.covering x,fun p=> T.covering_reflect ..⟩; rw [← show touches G R.side Q= _ from funext (lit_angle T x), lit]; exact (funext (T.links_apply x)).symm -- orientation rw

-- Root incidence (unlike sign, need subtract root0)
def marker (v:Root G R.side) : R.Vertex→ G.Color:= Quotient.lift (fun i=> Orbit.atSite i v) (by intro a b (h:b=a ∨ b= -a); rcases h with h|h; rw [h]; rw [h,site_neg])
lemma mark_steps (v:Root G R.side)(i:J): let w:=i.val; Orbit.atSite w.1 v - Orbit.atSite (w.1+step w.2) v= flux G i ( marker v (R.src (enc R i)) - marker v (R.dst (enc R i)) ):= by
 let m:=marker (R:=R) v; change m (R.vertex _) - m (R.vertex _)= flux G i (m ( R.src ( R.rep i.val ))-m ( R.dst ( R.rep i.val )))
 unfold flux; by_cases h:R.Chosen i.val
 · rw [if_pos h,( R.rep_sites _ h ).1,(R.rep_sites _ h).2]; rfl
 rw [if_neg h,( R.rep_sites' _ h ).1,( R.rep_sites' _ h ).2]; exact (neg_sub ..).symm
local notation "F" => Root G R.side
private lemma ascent (z:R.Vertex)(h:z≠T.root): T.parent z ≠ z:= fun p=> by have hh:=T.closer _ h; rw [p] at hh; exact hh.false
private lemma bij_ι : Injective (take S ∘ₗ vertical (0: Rep G R.side)):= by
 apply LinearMap.ker_eq_bot.mp; apply bot_unique; intro z hz; change take S (vertical _ z)=0 at hz; rw [vertical_flat,map_neg,neg_eq_zero] at hz
 let m:= marker (R:=R) z; have hy (i: Descend T) : m (R.src ( (cap T i).val )) = m (R.dst ((cap T i).val)):= by
    apply sub_eq_zero.mp; apply (flux G i.val).injective; rw [map_zero]; exact (mark_steps (R:=R) z i.val).symm.trans (congr_fun hz i)
 have hk (n:ℕ) : ∀ x,T.rank x=n→ m x=m T.root:= by
   induction n using Nat.strong_induction_on with
   | h n ih => intro x hx; by_cases he:x=T.root; rw [he]; obtain hh:= ih _ (hx ▸ T.closer x he) _ rfl; rw [← hh]; let i:↥T.edges:=⟨ T.edge x he,( T.mem_edges .. ).2 ⟨x,he,rfl⟩⟩; specialize hy ((cap T).symm i); rw [Equiv.apply_symm_apply] at hy; change m (R.src (T.edge x he))= m (R.dst (T.edge x he)) at hy; rcases T.joins x he with ⟨a,b⟩|⟨a,b⟩; rw [a,b] at hy; exact hy; rw [a,b] at hy; exact hy.symm
 refine (Submodule.mem_bot _).mpr (funext fun i=>?_); change z i=0; rw [← Orbit.atSite_eq i z, show Orbit.atSite i.val z=m (R.vertex i.val) from rfl,hk _ _ rfl, ← hk _ (R.vertex 0) rfl]; exact Orbit.at_cent _

private def harvest (q: T.edges → G.Color)(x:R.Vertex): G.Color:= if h : x=T.root then 0 else
    let i:=T.edge x h
    (harvest q (T.parent x)) + if R.src i=x then q ⟨i,( T.mem_edges .. ).2 ⟨x,h,rfl⟩⟩ else -q ⟨i,( T.mem_edges .. ).2 ⟨x,h,rfl⟩⟩
termination_by T.rank x
-- on the true orbit-graph nodes, rank descent is strict
decreasing_by exact T.closer x h
private lemma harvest_edge (q:T.edges→C)(i:T.edges): harvest T q (R.src i.val)-harvest T q (R.dst i.val)= q i:= by
 obtain ⟨e,he⟩:=i; obtain ⟨x,h,rfl⟩:= (T.mem_edges _).1 he; dsimp only; let i:T.edges:=⟨T.edge x h,he⟩; rcases T.joins x h with ⟨a,b⟩|⟨a,b⟩
 · rw [a,b,harvest.eq_1,dif_neg h]; dsimp only; rw [if_pos a]; abel
 rw [a,b,harvest.eq_1 T q x,dif_neg h]; dsimp only; rw [if_neg (by rw [a]; exact ascent T x h)]; abel
private lemma bij_S : Surjective (fun z:Root G R.side=>fun i:Descend T=> let w:= i.val.val; Orbit.atSite w.1 z - Orbit.atSite (w.1+step w.2) z):= by
 intro y; let m (i:T.edges):= (flux G ((cap T).symm i).val).symm (y ((cap T).symm i)); let u:= harvest T m; let Z : Pert.Orb.Parameter G R.side := ⟨fun x=> u (R.vertex x) - u ( R.vertex 0 ),⟨fun x=> (congr_arg (fun x=> u x-u (R.vertex 0)) (R.vertex_neg x)),sub_self _⟩⟩
 let z:= (gaugeAngles G R.side).symm Z; have h (x:R.Vertex): marker z x=u x-u ( R.vertex 0 ):= by obtain ⟨x,rfl⟩:= R.vertex_surjective x; exact congr_fun (congr_arg Subtype.val ( (gaugeAngles G R.side).apply_symm_apply Z)) x
 refine ⟨ z,?_⟩; funext i; refine (mark_steps (R:=R) z i.val).trans ?_; rw [h,h, sub_sub_sub_cancel_right, show u (R.src (enc R i.val))-u (R.dst (enc R i.val)) = m (cap T i) from harvest_edge T m (cap T i) ]; unfold m; rw [Equiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
theorem valid : Permitted G S:= by
    refine (incidence S).mpr ⟨?_,bij_S T⟩; intro z w he; apply bij_ι T; rw [LinearMap.comp_apply,LinearMap.comp_apply, vertical_flat,vertical_flat,map_neg,map_neg]; exact congr_arg Neg.neg (show take S _=take S _ from he)
end YM.FVA2.XPos
