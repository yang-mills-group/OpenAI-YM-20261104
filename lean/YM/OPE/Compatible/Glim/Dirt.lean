import YM.OPE.Compatible.Glim.Noc
/-! # On orbit edges. payout. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer
variable {n:Side}(H:Even n.val)(T:Plot H)(p:T.Free)(b:Bool)
local notation "E!"=> Keys G T.Free
noncomputable abbrev offZ (H: Even n.val)(T:Plot H): Keys G T.Free→L[ℝ] Bid.Dir G n:= cloak H ∘L T.rollX.toContinuousLinearMap
abbrev whiz (e:edgeV n): Body 1 n:= driftB n e
local notation "𝔏" => offZ H T
abbrev Plate (k:Kv):edgeV n:= ferry k p.val.val
lemma plateHere : Plate H T p 0=p.val.val:= ferry_0 _
lemma hub_r (e: edgeV n)(x:E!): 𝔏 x (whiz e)=hover H (T.rollX x) e:=(cloak_at H _ _ _)
lemma suchE(x:E!)(e:edgeV n)(h:pathX H e=p.val) : 𝔏 x (whiz e)= if dir H e then -(x p) else x p:=by rw [hub_r,hover,h,show T.rollX x p.val=_ from T.kept 0 x p]
lemma elsewhere(x:E!)(a:G.Color)(e:edgeV n)(h:pathX H e≠ p.val): 𝔏 (lunge p b x a) (whiz e)=0:=by
     rw [hub_r]; let z:= lunge p b x a; have he:T.rollX z (pathX H e)=0:=by
          by_cases ht:T.Branch (pathX H e); exact T.keptZ 0 z (⟨_,ht⟩:T.Stable)
          let i:T.Free:=⟨_,ht⟩; have hh:i ≠ p:=fun hv=> h (congr_arg Subtype.val hv); rw [show T.rollX z (pathX H e)=z i from T.kept 0 z i]; simp [z,hh]
     unfold hover;rw [show T.rollX _ _=0 from he];simp
lemma abrupt (x:E!)(a:G.Color)(h:sword (!b) (- x p) a= -sword b (x p) a)(e:edgeV n)(i:Body 1 n)(h':pathX H e=p.val)(hx:i=whiz e):
     𝔏 (lunge p b x a) i=lunge i (b.xor (dir H e)) (𝔏 x) a i :=by subst i; rw [suchE H _ _ _ _ h']; unfold lunge; rw [suchE H _ _ _ _ h']; cases hg:dir H e<;>simp [h]
noncomputable abbrev planet (k:Kv)(x:E!) := lunge (whiz (Plate H T p k)) (b.xor (dir H (Plate H T p k))) (𝔏 x)
lemma dualX : ∀ᶠ x:E! in 𝓝 0,∀ a:G.Color, 𝔏 (lunge p b x a)=∑ k:Kv,planet H T p b k x a:=by
     filter_upwards [((continuous_apply p).tendsto (0:E!)).eventually (swordV b)] with x hx a; funext i; rw [Finset.sum_apply]; let v:= (driftB n).symm i; have he: i=whiz v:=((driftB n).apply_symm_apply i).symm; have ht(k:Kv)(hh:Plate H T p k≠ v): planet H T p b k x a i=0:=by
          have hp:i≠ whiz (Plate H T p k):= fun hv=>hh ((driftB n).injective (hv.symm.trans he)); unfold planet; simp [lunge,hp]
     by_cases h:pathX H v=p.val
     · let k:= (edgesK H).tick v; have hk:Plate H T p k=v:=by unfold Plate; rw [← h]; exact (resettle H _).symm
       rw [sum_eq_single k]; unfold planet; rw [hk]; nth_rw 1 [show whiz v=i from he.symm]
       · exact abrupt H T p b x a (hx a) v i h he
       · exact fun i _ hv=> ht i fun H'=>hv ((edgesK H).together (H'.trans hk.symm))
       simp
     rw [he, elsewhere H T p b x a _ h]; symm; apply sum_eq_zero; intro j _; rw [← he]; exact ht j (fun hh=> h ((show pathX H v=p.val from by rw [← hh,Plate,path_ferry,path_id])))
end YM.OPE.Variance
