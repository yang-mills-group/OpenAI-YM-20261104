import YM.LocalLTE.FieldPT.Outlet
/-!
 Kinetic currency. ∆ transformed as `g^2*∆(s)`: cash at all s→ τ witness.
 Powers above n and discard leading poles forbidden for ratio. Error ∆ billed after multiplying s^2.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset MeasureTheory
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open YM.LocalLTE YM.LocalLTE.Weft FrameBox FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n L : Side} {j z k m:ℕ} {W κ K U C V t H u v ε: ℝ}
attribute [local instance] Gauge.frobInner
open Residual Geo Animals Quotes Extra.Iteration Averaging
-- s^2 pays.TH tolerance.WITHIN normalization at outgoing t^{-2} convention.
noncomputable def poloDelta (k r:ℕ)(f:ℝ→ℝ)(s:ℝ):ℝ:= ∑ j∈ (univ:Finset (J k)).filter (fun j=> k≤j.val+2∧j.val+2 ≤ k+r), Weft.mark k j s * Weft.pick k f j
def scaleFee (k:ℕ) := ∑ j:J k,∑ i:J k,|slate k i j| / (Weft.probe k i)^2
lemma carteF (k:ℕ): 0 ≤ Price.scaleFee k:= Finset.sum_nonneg (fun i _=>Finset.sum_nonneg fun j _=> by positivity)
lemma fundedQ (r:ℕ) {f:ℝ→ℝ} (hp:Hex k f)(hc:∀ s∈Weft.clip,|s^2*f s| ≤C) (s:ℝ)(hs:s∈Weft.clip): (∀ i:J k,i.val+2<k → Weft.pick k f i=0) ∧ |s^2*(f s-Price.poloDelta k r f s)| ≤ (scaleFee k*C)*s^(r+1):=by
    let t(i:J k):=Weft.mark k i s*pick k f i; let V(j:J k):= (∑ i:J k,|slate k i j|/(Weft.probe k i)^2); let A:= (univ:Finset (J k)); let S:=A.filter fun i=> k ≤ i.val+2∧i.val+2≤k+r
    have h i: 0≤ V i:=sum_nonneg (fun _ _=>by positivity)
    have hh(i:J k):‖pick k f i‖ ≤ V i*C := Weft.caisson i hc
    have hC:0≤ C:=(abs_nonneg _).trans (hc _ (probes k 0))
    have hv:= Weft.vanish hp hc
    refine ⟨hv,?_⟩; let α x:= s^2*t x; have he(Q): s^2 *(∑ i∈Q,t i)=∑ i∈Q,α i :=Finset.mul_sum Q (fun i=> t i) (s^2)
    have hz : |s^2*(f s - Price.poloDelta k r f s)|=|∑ i∈ A \ S, α i|:= by
       congr 1; rw [show f s=∑ i∈A,t i from hp.seen hs,show Price.poloDelta k r f s=∑ i∈S,t i from rfl, mul_sub,he,he,Finset.sum_sdiff_eq_sub (Finset.subset_univ _)] -- edit
    rw [hz]; have ht j (hj:j∈A \ S): |α j| ≤ s^(r+1)*(V j*C):=by
       have he:0<s:=hs.1; have hx:= Finset.mem_sdiff.mp hj|>.2; have hh0: 0≤ V j*C:= mul_nonneg (h _) hC
       by_cases ht: k≤j.val+2
       · have hw: k+r < j.val+2:= by_contra fun hb=> hx (Finset.mem_filter.mpr ⟨mem_univ j,ht,le_of_not_gt hb⟩); have hp:s^2 * Weft.mark k j s ≤ s^(r+1):= by
            unfold Weft.mark; rw [← mul_div_assoc,div_le_iff₀ (pow_pos he _),← pow_add,← pow_add]; exact pow_le_pow_of_le_one he.le hs.2 (by omega)
         unfold α t; rw [← mul_assoc,abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) (show 0 ≤ Weft.mark k j s from div_nonneg (pow_nonneg he.le _) (pow_nonneg he.le _)))]; exact mul_le_mul hp (hh _) (abs_nonneg _) (pow_nonneg he.le _)
       unfold α t; rw [hv _ (lt_of_not_ge ht),mul_zero,mul_zero,abs_zero]; positivity
    refine ((abs_sum_le_sum_abs ..).trans (sum_le_sum ht)).trans (?_); rw [← Finset.mul_sum, ← Finset.sum_mul, mul_comm _ (s^_)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=> h _)) hC) (pow_nonneg hs.1.le _)
end YM.AnalyticBridge.VerifiedReset.Collection.Price
