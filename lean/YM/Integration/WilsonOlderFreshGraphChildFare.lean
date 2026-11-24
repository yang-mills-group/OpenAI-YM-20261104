import YM.Integration.WilsonOlderFreshGraphSchoolSite
import YM.FormalBulk08.Annex.Palm

/-! The exact child test dilation contracts the funded, compressed test film.
After summing the original finite preimages only the physical engineering
weight remains. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphChildFare
open Function Filter Finset Lattice FormalBulk08 Dawn Annex
open scoped Classical BigOperators Topology
variable {L:Side}{D:ℕ}

theorem compressed (odd:Odd L.val)(h:2 ≤ L.val)(x:Site L)(f:Studio D):
    ‖Annex.compress D (Dawn.throughW x D h f)‖ ≤ ‖Annex.compress D f‖:=by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro z
  rw [Annex.compel]
  change ‖(Dawn.tunnel x D h f).val k (Annex.embark z)‖ ≤ _
  rw [Dawn.tunnel_show,norm_mul,Real.norm_of_nonneg (pow_nonneg Dawn.scale_pos.le _)]
  have atChild:‖f.val k (Dawn.peninsula x h (Annex.embark z))‖ ≤ ‖Annex.compress D f‖:=by
    let v:Annex.Deck:=⟨_,Annex.peninsula_in L odd h x z⟩
    exact ((Annex.compress D f k).norm_coe_le_norm v).trans (norm_le_pi_norm _ k)
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ Dawn.scale_pos.le Dawn.scale_small)).trans atChild

theorem engineering (odd:Odd L.val)(h:2 ≤ L.val)(f:Studio D)(d:ℕ)(v:ℝ)(hv:0 ≤ v)
    (fare:Site L→ℝ)(paid:∀x,fare x ≤ v*(1+‖Annex.compress D (Dawn.throughW x D h f)‖)):
    ∑x:Site L,((L.val:ℝ)^d/(L.val:ℝ)^4)*fare x ≤ (L.val:ℝ)^d*v*(1+‖Annex.compress D f‖):=by
  let fee:ℝ:=v*(1+‖Annex.compress D f‖)
  have each (x:Site L):fare x ≤ fee:=(paid x).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right (compressed odd h x f) 1) hv)
  have pos:0 < (L.val:ℝ):=by exact_mod_cast L.pos
  calc
    _ ≤ ∑ _x:Site L,((L.val:ℝ)^d/(L.val:ℝ)^4)*fee:=by
      exact Finset.sum_le_sum fun x _=>mul_le_mul_of_nonneg_left (each x) (by positivity)
    _ = _:=by
      rw [Finset.sum_const,Finset.card_univ,Lattice.site_card,nsmul_eq_mul,Nat.cast_pow]
      dsimp [fee]
      field_simp
end YM.Integration.WilsonOlderFreshGraphChildFare
end
