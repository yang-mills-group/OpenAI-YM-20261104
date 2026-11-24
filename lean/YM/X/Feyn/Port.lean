import YM.Pert.Lattice.Action
import YM.PertExtension.OrbLaurent
import YM.Pert.Fourier.Source
import YM.X.Gauss.Hook
/-!
# tree→Feynman port at fixed finite volume: representation maps.
Exact germ via same gauge `frame`. Definite quadratic calculation in next.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Feyn
open Function Filter Set Lattice Wilson
open PertExtension PertExtension.Chart PertExtension.Orb
open Pert.Orb (Potential positiveLinks takeLink)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (he:Even n.val)
abbrev Key (n:Side):= Edge (Site n)
local notation "O" => OEdge n
local notation "E" => Potential G n
local notation "A" => Dir G n
local notation "V" => Config G n

lemma reveal (v:E) : liftLinks (fun e:O=>positiveLinks v e.val)= positiveLinks v:= by
   funext e; unfold liftLinks; split
   next h=> change positiveLinks v (eR e)=_; rw [h]
   next h=> have hm:=v.property e; change (G.lieExp (v.val (eR e)))⁻¹= G.lieExp (v.val e); rw [(eR_spec e).resolve_left h]; change (G.lieExp (v.val (Pert.Orb.image e)))⁻¹= _; rw [hm, Work.F03.exp_neg_color,inv_inv]

def leaves (v:E)(a: Trees n) := positiveLinks v a.val.val
def flower (v:E)(a: Cotree n) := positiveLinks v a.val.val
def porter (v:E)(x:Site n):G.El:= frame (leaves v) x
def branch (v:E) := fresh (leaves v) (flower v)
lemma take_map (v:E): links (leaves v) (flower v)=positiveLinks v:= by
   rw [←reveal v]; unfold links; apply congr_arg liftLinks; funext i; unfold splitLink; split<;> rfl

section
include he
lemma worth (v:E): gauge (porter v) (positiveLinks v)=links 1 (branch v):= by
    conv_lhs=> rw [← take_map v] -- need goals
    exact alignment he ..
end

def fits : A→ₗ[ℝ] E:= variation.codRestrict (Pert.Orb.LinkP G n) (fun p=> fun i=>variation_invert he p i)
lemma fits_at (v:A): positiveLinks (fits he v)= representative v:= by
   have he' : (fun e:O=>positiveLinks (fits he v) e.val)=splitLink 1 (fun i:Cotree n=> G.lieExp (v i)):= by
      funext e; unfold splitLink; split
      next h=> change G.lieExp (variation v e.val)=1; rw [variation_branch v ⟨e,h⟩]; simp
      next h=> change G.lieExp (variation v e.val) = _; rw [variation_others v ⟨e,h⟩]
   exact (reveal _).symm.trans (congr_arg liftLinks he')
lemma leaf_nil (a:Trees n): leaves (0:E) a=1:= by simp [leaves]
lemma frame_flat (x:Site n):frame (fun _ : Trees n=> (1:G.El)) x=1:= by
   let a:=fun _ : Trees n=>(1:G.El); induction hz: depth x using Nat.strong_induction_on generalizing x with
   | _ k ih=> rw [frame]; split
              · rfl
              next he => have hv:= (down_spec he).trans_eq (depth_vertex x); dsimp only; rw [ih _ (hz ▸ hv) _ rfl]; unfold Step.read; simp only [liftLinks,splitLink]; split <;> split <;> split<;> simp
lemma porter_zero (x:Site n): porter (0:E) x=1:= by rw [porter,funext leaf_nil]; exact frame_flat _
lemma branch_zero (a:Cotree n): branch (0:E) a=1:= by unfold branch fresh; change porter (0:E) _ * flower 0 _ * (porter 0 _)⁻¹=_; rw [porter_zero,porter_zero];simp [flower]
lemma branch_inc (v:A): branch (fits he v)=fun i:Cotree n=> G.lieExp (v i) := by
   have ht : leaves (fits he v)=(fun _=>1) := funext (fun a=> by change G.lieExp (variation v a.val.val)=_; rw [variation_branch]; simp)
   unfold branch; funext i; rw [fresh,ht, frame_flat,frame_flat, inv_one,one_mul,mul_one]; change G.lieExp (variation v i.val.val)=_; rw [variation_others]

lemma unlocked (k: Key n)(v:E): liftLinks (splitLink (leaves v) (fun _=>1)) k= if Branch (index k) then positiveLinks v k else 1:= by
    by_cases h:Branch (index k)
    · conv_rhs=> rw [if_pos h,← take_map v]
      unfold links liftLinks splitLink; simp [h]
    unfold liftLinks splitLink; simp [h]

lemma leaf_smooth (a:Trees n): ContDiff ℝ ω fun x:E=> G.mat (leaves x a) := Pert.Orb.pos_mDiff _
lemma node_smooth (a:Site n): ContDiff ℝ ω fun x:E=> G.mat (porter x a) := by
   induction hz: depth a using Nat.strong_induction_on generalizing a with
   | _ k ih=> unfold porter; conv => rhs; intro p; rhs; rw [frame] -- loops
              split_ifs
              · exact contDiff_const
              rename_i e; let x:Site n:= vertex a; let d:=down x; have hh : depth (x+d.vec) < k:= hz ▸ (down_spec e).trans_eq (depth_vertex a)
              have hyp : ContDiff ℝ ω (fun p:E=> G.mat (d.read (liftLinks (splitLink (leaves p) (fun _=>1))) x)):=by
                 unfold Step.read; simp_rw [unlocked]; split_ifs
                 all_goals first | exact contDiff_const | exact Pert.Orb.pos_mDiff _ | simp only [G.mat_inv]; exact (starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.comp (Pert.Orb.pos_mDiff _)
              change ContDiff ℝ ω (fun p:E=> G.mat (porter p (x+d.vec) * (d.read _ x)⁻¹)); simp only [G.mat_mul,G.mat_inv]; apply ContDiff.mul (ih _ hh _ rfl); exact (starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.comp hyp
lemma branch_smooth (a:Cotree n): ContDiff ℝ ω fun x:E=> G.mat (branch x a):= by
   unfold branch fresh; simp_rw [G.mat_mul,G.mat_inv]; refine ContDiff.mul (ContDiff.mul ?_ ?_) ?_
   · exact node_smooth _
   · exact Pert.Orb.pos_mDiff _
   exact (starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.comp (node_smooth _)

end YM.PositionX.Feyn
