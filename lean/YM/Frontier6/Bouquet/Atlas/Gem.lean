import YM.Frontier6.Bouquet.Audit.Contracts

/-!
# Remembrance of coordinate origins
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q : Ensemble} (i:P)(x:fiber P)
def rune (i:P): fiber P →L[ℝ] normal i.val:= floorOf _ _
lemma mass_missing : mass i.val.val x.val=0:= (fiber_iff _ _).mp x.property|>.2 i.val i.property
lemma centroid_empty : centroid i.val x.val=0:=by unfold centroid; rw [ContinuousLinearMap.smul_apply, mass_missing i x,smul_zero]
lemma begins (j:Slot)(h:j∈ i.val.val): house j x.val=house j (rune i x).val:=by
    let y:=rune i x; let z:= x.val-y.val; apply sub_eq_zero.mp; have hh:z∈(normal i.val)ᗮ:= on_drop; change house j x.val-house j y.val=0; rw [← map_sub, home_eq, ← pod_centroid hh j h, map_sub, centroid_empty];
    have hv:centroid i.val y.val=0:= by unfold centroid; rw [ContinuousLinearMap.smul_apply,(normal_iff _ _).mp y.property|>.2,smul_zero]
    rw [hv,sub_zero]
lemma pricesR {B:Audit.Aura P} {M:Pod→ℝ}(he:B.Cozy M)(f:Full (fiber P))(hf:Fair f B.foot B.center)(h:x∈ tsupport f): ‖rune i x‖≤ (i.val.card:ℝ)*M i.val:=by
   let y:= rune i x; have hh:= (normal_iff _ _).mp y.property; have he'(j:Slot)(hj:j∈i.val.val):‖y.val j‖≤ M i.val:=by
       change ‖house j y.val‖ ≤ _; rw [← begins i x j hj]; have ht:= he.prices i _ (hf x h i j hj); simpa only [actual,add_sub_cancel_right] using ht
   exact (entry_cardinal_est i.val.val y.val hh.1).trans ((Finset.sum_le_sum he').trans_eq (by simp [nsmul_eq_mul]))

-- unnormalized projected coordinates embedded by this balance.
lemma on_zero (j:P)(h:j≠i) : floorOf (normal i.val) (normal j.val)=0:=by ext1 x; exact on_blank (normal_orth (P.pairwise j.property i.property (fun H=> h (Subtype.ext H))) x.property)
lemma centerless_unchanged {j:P}(h:j≠i): rune j (centerless (home_sub i.property) x)=rune j x:=by
    change rune j (_ - _)=_; rw [map_sub]; change _- floorOf (normal j.val) (normal i.val) (ontoSpace (normal i.val) _)=_; rw [on_zero j i h.symm]; simp
lemma coordinate_unchanged {j:P}(h:j≠i)(b:Slot)(hb:b∈ j.val.val): house b (centerless (home_sub i.property) x).val= house b x.val :=by rw [begins,centerless_unchanged i x h,← begins]; all_goals assumption -- args
lemma average_within (Q:Set E4)(h:Convex ℝ Q)(z:E4)(he:∀ j∈i.val.val,house j x.val+z∈Q): z∈ Q:= by
    let k:=(i.val.card:ℝ); have hp:0< k:= by unfold k; exact_mod_cast i.val.card_pos
    let f(j):= house j x.val+z; have hx: (∑ j∈i.val.val,k⁻¹ • f j)=z:=by
        rw [← Finset.smul_sum]; unfold f; rw [Finset.sum_add_distrib, Finset.sum_const, show ∑ j∈i.val.val,house j x.val =0 from ((mass_eq i.val.val x.val).symm.trans (mass_missing i x)),← Nat.cast_smul_eq_nsmul ℝ]; rw [zero_add]; exact inv_smul_smul₀ hp.ne' z -- direction
    exact hx ▸ (h.sum_mem (t:=i.val.val) (w:=fun i=> k⁻¹) (fun j hj=> (inv_pos.mpr hp).le) (by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_inv_cancel₀ hp.ne') he) -- inspect
end YM.Frontier6.Bouquet
