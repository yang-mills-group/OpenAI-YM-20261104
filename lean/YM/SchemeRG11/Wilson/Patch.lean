import YM.SchemeRG11.Wilson.Port
import YM.Pert.Rig.Linked
/-! Discrete formal first-order Orb restriction. Point kernel equality in running top system
 from H.Field representatives requires more. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Acorn
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial Tree Catch Cellular Full Atoll Pile Align Tile
open MeasureTheory ProbabilityTheory
open scoped Classical ContDiff Topology
variable {G:Gauge} {I:Type}[Fintype I][DecidableEq I]
variable (s:Finset I)(p:I→ Pile.pLabel G) {T:Itinerary}
lemma centerline (he:∀ i,4∣(T.period i).val) : Interior T (fun i=> Full.center (T.period i)):=by
 refine ⟨1/4,by norm_num,Filter.Eventually.of_forall ?_⟩; intro i
 let n:=T.period i; let z:= Full.center n+Full.center n
 have hx:4*|(0:Cover) 0| < (n.val:ℤ):=by simp
 have hh := Align.dist_half (x:=z) (he i) (0:Cover) 0 hx (by simp [z]); have hv:4*|(lift z 0)| = ((4*(lift z 0).natAbs:ℕ):ℤ) :=by rw [Int.abs_eq_natAbs,Nat.cast_mul]; rfl
 rw [hv] at hh; have he : (n.val:ℤ)≤ ((4*pdist z:ℕ):ℤ) :=by apply le_trans hh; exact_mod_cast Nat.mul_le_mul_left 4 (component_le z 0)
 have hh : (n.val:ℝ) ≤4*pdist z:=by exact_mod_cast he
 linarith only [hh]
lemma stencil (hg:G.Simple)(t:I→ℕ→ Cover) (o:StepPath T)(w:I→ℕ)(hw:∀ i, IsWeightedHomogeneous generation (p i) (w i))(cap:ℕ)(hc:∀ i,Full.within (realCast (p i)) cap) (hi:Interior T o)(hx:∀ i,Medium T (t i)) (d:ℕ):
 let X(m:ℕ):=Full.amplitude (fun _:I=>cap) (T.gap m) s (poseN t m (o:=o)) (fun i=>realCast (p i))
 Tendsto (fun m=> Complex.ofReal ((T.gap m)⁻¹^d)*(PowerSeries.coeff 0 (X m)-coverGod s p (T.gap m) (fun i=>t i m))) atTop (𝓝 0) ∧
 Tendsto (fun m=> Complex.ofReal ((T.gap m)⁻¹^d)*(PowerSeries.coeff 1 (X m)-firstCovers s p (T.gap m) (fun i=>t i m))) atTop (𝓝 0):=by
 intro f; dsimp only [f]
 rw [PowerSeries.coeff_zero_eq_constantCoeff]; simp_rw [allowing _ _ _ p _ hc,charging _ _ _ p _ hc hg, ← Complex.ofReal_sub,← Complex.ofReal_mul, inv_pow]
 have hk (F:ℕ→ℝ)(hf:Tendsto F atTop (𝓝 0)): Tendsto (fun i=> Complex.ofReal (F i)) atTop (𝓝 0):=by simpa [comp_def] using (Complex.continuous_ofReal.continuousAt (x:=(0:ℝ))).tendsto.comp hf
 constructor
 · apply hk; simpa only [zpow_neg,zpow_natCast] using dashes s p t o w hw hi hx d
 apply hk; simpa only [zpow_neg,zpow_natCast] using enters s p t o w hw hi hx d
end YM.SchemeRG11.Acorn
