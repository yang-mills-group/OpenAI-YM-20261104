import YM.OPE.Compatible.Lines.Compass
import YM.EveryPhase.Pages
/-!
# Common holomorphic one-coordinate amplification

From the EveryPhase extension facts on any Final. In particular analytic bounds here uniform when phase *and* spectators vary through heights of prescribed minimum, independently of other closeness costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Set Filter Analysis Table Lattice MeasureTheory Complex Boundary EveryPhase Spec OPE
open scoped Topology InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U:Final C F S}(L : Almanac U) {n:ℕ} {s :Times n}
def orb (i:Viewers U) : Waves S:= i.elim U.B.waves (fun j=> (L.contours j).waves)
lemma region_for (i:Viewers U):(orb L i).Region (spectator U i):=by cases i; exact U.realization.allWorld.heat; exact (L.cards _).fromPhase.heat
include L
private lemma both_power (v:Fin n→ S.Union):∃ m:ℕ,∃ C₀:ℝ, 0≤C₀∧∀ i,∀ (y:Heights n)(k:ℝ), k∈Ioc 0 1 → broad y k → ∀ x, ‖(orb L i).restricted v y x‖ ≤ C₀*k⁻¹^m:=by
   obtain ⟨m,M,hM,hm⟩:=EveryPhase.power L n v; refine ⟨m,M,hM,fun i y k hk hy x=>?_⟩
   cases i with
   | some i=> exact hm i y k hk hy x
   | none =>
       have h : y ∈ east n:=fun i j h=> sub_pos.mp (hk.1.trans_le (hy i j h))
       have ht:= strict_evaluation L x v h
       haveI:= U.phase.phase.decomposition.normalized
       change ‖U.B.waves.restricted _ _ _‖ ≤ _; rw [← ht.2]; apply le_trans (_root_.MeasureTheory.norm_integral_le_of_norm_le (g:=fun _=> M*k⁻¹^m) (integrable_const _) (ae_of_all _ (fun i=> hm i y k hk hy x))); simp
-- all at arbitrary complex coords
lemma ocean (v:Fin n→ S.Union) : ∃ m:ℕ,∃ C₀:ℝ, 0≤C₀ ∧ ∀ i,∀ (s : Times n)(k:ℝ), k∈Ioc 0 1 → broad (fun j=> (s j).im) k → ∀ x, ‖(orb L i).F _ s x v‖ ≤ C₀*k⁻¹^m:=by
    obtain ⟨m,M,h,he⟩:=both_power L v; refine ⟨m,M,h,fun i s k hk hK x=>?_⟩
    let z:= place x (fun j=> (s j).re); have hh : shift z (fun j=> (s j).im)= s:=by
       ext1 j; simp [shift,z,place]
    have ht: trace z=x:=by ext1 j; simp [trace,z,place]
    have he:= he i _ _ hk hK z; unfold Waves.restricted at he; rwa [hh,ht] at he
end YM.FrameRead
