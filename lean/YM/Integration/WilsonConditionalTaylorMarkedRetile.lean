import YM.Integration.WilsonConditionalTaylorRetile
import YM.FormalBulk08.Kemp.Crest

/-! The whole signed source keeps its own spatial root and positive strip
under the actual finite block decomposition, for varying incoming fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedRetile
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05 Bank Kemp Rift
open scoped Topology ENNReal BigOperators Classical
variable {I : Type} {n f : Side} (S : Ratio n f)

theorem amount {r : ℕ} {σ τ C : ℝ} {T : Tile (Tor f I) r} (x : Tor n (Tor S.count I))
    (h : τ ≤ S.count.val*σ) (he : 0 ≤ τ) (price : Knoxville (lake f _) σ ((splitCo S I).symm x) T C) :
    Knoxville (lake n _) τ x (jetty (splitCo S I).symm T) (Real.exp (8*τ)*C) :=by
  let a:= (splitCo S I).symm
  let inc : chain (Tor n (Tor S.count I)) r→chain (Tor f I) r:=fun v=>a ∘ v
  have embed : Function.Injective inc:=by
    intro v w hh;funext i;exact a.injective (congrFun hh i)
  have bill:=(ENNReal.tsum_comp_le_tsum_of_injective embed (penon (lake f _) (a x) σ T)).trans price.2
  refine ⟨mul_nonneg (Real.exp_pos _).le price.1,?_⟩
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine le_trans ?_ (mul_le_mul_right bill _)
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum;intro v
  have mask:=WilsonConditionalTaylorRetile.weight S (Fin.cons x v) h he
  rw [Fin.comp_cons] at mask
  exact (mul_le_mul_left mask _).trans_eq (mul_assoc ..)

theorem scaled {r : ℕ} (L : Side) {σ τ : ℝ} (h : τ ≤ L.val*σ) (hs : 0≤σ) (he : 0≤τ) (x : Biglot I)
    {A : Tile (Biglot I) r} {U : (n:Side)→Tile (Tor n I) r} (prior : Kalm σ x A U) :
    Kalm τ (scroll L I x) (jetty (scroll L I).symm A) (fun n=>jetty (splitCo (endo n L) I).symm (U (n*L))) :=by
  have lines:=(WilsonConditionalTaylorRetile.scaled L h he (prior.charges hs)).1
  obtain ⟨C,paid⟩:=prior.2
  refine ⟨lines,Real.exp (8*τ)*C,?_⟩
  filter_upwards [(WilsonConditionalTaylorRetile.sides L).eventually paid] with n fee
  have id:=scroll_pull x (endo n L)
  change drip n (scroll L I x)=(splitCo (endo n L) I) (drip (n*L) x) at id
  apply amount (endo n L) _ h he
  rw [id,Equiv.symm_apply_apply];exact fee

end YM.Integration.WilsonConditionalTaylorMarkedRetile
end

