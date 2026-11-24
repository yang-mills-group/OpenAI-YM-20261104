import YM.GradedFar.Street
/-!
# The geometry needed on the (C5) grid

In combined `x,Ty` coordinates (Euclidean l₂). Give positivity of grid exponent; use
smaller clearance automatically at the spindle. No rounding a test to make it a product.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Crosser
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Metric
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n m:ℕ}
local instance {k:ℕ} : ContinuousSMul ℝ (Points k):= IsBoundedSMul.continuousSMul
def NExt (n m : ℕ) : Points (n+m)→L[ℝ] Points n:= LinearMap.toContinuousLinearMap {
    toFun v:= points (fun i=> v (Fin.castAdd m i))
    map_add' _ _:=rfl
    map_smul' _ _:=rfl }
def FExt (n m : ℕ) : Points (n+m)→L[ℝ] Points m := LinearMap.toContinuousLinearMap {
    toFun v:= points (fun i=> v (Fin.natAdd n i))
    map_add' _ _:=rfl
    map_smul' _ _:=rfl }
lemma extract_all (z:Points (n+m)){T:ℝ}(hT:1≤T) : z= forest (NExt n m z) (T • (T⁻¹ • FExt n m z)) :=by
 rw [smul_inv_smul₀ (zero_lt_one.trans_le hT).ne']; ext1 i; refine Fin.addCases (fun j=> by rw [forest_left]; rfl) (fun j=> by rw [forest_right]; rfl) i

variable {T:ℝ}{K K':Set (Points n)}{N N':Set (Points m)}(hK:IsCompact K)(hN:IsCompact N)
include hK hN
set_option maxHeartbeats 500000 in
lemma enlargement(hKK:K⊆interior K')(hNN:N ⊆ interior N'): ∃ ε:ℝ,0<ε ∧ ∀ T:ℝ,1≤T→∀ z, Fits K N T z →
    ∀ z', ‖z'-z‖<ε→ Fits K' N' T z':=by
 obtain ⟨δ,hδ,H⟩:= hK.exists_thickening_subset_open isOpen_interior hKK
 obtain ⟨η,hη,A⟩:= hN.exists_thickening_subset_open isOpen_interior hNN
 let Δ:=min δ η; let L:=1+‖NExt n m‖+‖FExt n m‖
 have hP:0<Δ:= lt_min hδ hη; have hc:0<L:=by dsimp only [L]; positivity
 have L₀ : ‖NExt n m‖ ≤ L:= by dsimp only [L]; linarith only [ContinuousLinearMap.opNorm_nonneg (FExt n m)]
 have L₁ : ‖FExt n m‖ ≤ L:= by dsimp only [L]; linarith only [ContinuousLinearMap.opNorm_nonneg (NExt n m)]
 refine ⟨Δ/L, div_pos hP hc,fun T hT z hz z' he=>?_⟩
 obtain ⟨x,hx,y,hy,D⟩:= hz; let x':=NExt n m z'; let y':=T⁻¹ • FExt n m z'
 have hn:NExt n m z=x:= by rw [D]; ext1 i; exact forest_left _
 have hf:FExt n m z=T • y:= by rw [D]; ext1 i; exact forest_right _
 have hh: L*‖z'-z‖ < Δ:= by rw [mul_comm]; exact (lt_div_iff₀ hc).mp he
 have hp:0<T:=zero_lt_one.trans_le hT; refine ⟨x',interior_subset (H ?_), y',interior_subset (A ?_), extract_all z' hT⟩
 · apply mem_thickening_iff.mpr; refine ⟨x,hx,?_⟩
   rw [dist_eq_norm,← hn]; unfold x'; rw [← map_sub]; exact lt_of_le_of_lt (((NExt n m).le_opNorm (z'-z)).trans
     (mul_le_mul_of_nonneg_right L₀ (norm_nonneg _))) (hh.trans_le (min_le_left ..))
 apply mem_thickening_iff.mpr; refine ⟨y,hy,?_⟩; rw [dist_eq_norm, show y=T⁻¹ • FExt n m z from by rw [hf,inv_smul_smul₀ hp.ne']]
 unfold y'; rw [← smul_sub, ← map_sub, norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ T⁻¹)]
 apply lt_of_le_of_lt ((mul_le_mul ((inv_le_one₀ hp).mpr hT) ((FExt n m).le_opNorm _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
 exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right L₁ (norm_nonneg _)) (hh.trans_le (min_le_right ..))

local notation "Pt"=>Points (n+m)
-- true-ball radius property. Earlier grid hypotheses can be supplied as Covers for their grid z
-- (v etc positions all r-units even for Far). Uniform on r,T-before rounding, no order-swaps.
def Coverage (G:Gauge)(U B:ℝ)(K:Set (Points n))(N:Set (Points m))(A:Calendar→Set (Points (n+m)))(p:ℕ): Prop:=
    ∃ c:ℝ,0<c ∧ ∀ᶠ i in moving G U B,∀ q,Fits K N i.2 q→∃ z∈A i, ‖z-q‖ ≤ c*strength G i.1^p
variable {U B:ℝ}{hG:G.Simple}
include hG
lemma Coverage.data {A:Calendar→Set (Points (n+m))}{p:ℕ}(hk:Coverage G U B K N A p)(hKK: K⊆interior K')(hNN:N⊆interior N')(hp:1≤p):
    ∃ c:ℝ,0<c ∧ ∀ᶠ i in moving G U B,∀ q,Fits K N i.2 q→∃ z∈A i,Fits K' N' i.2 z ∧ Crosser.segment K' N' i (q,z) ∧ ‖z-q‖ ≤ c*strength G i.1^p:=by
 obtain ⟨c,hc,A⟩:=hk -- shadow
 obtain ⟨ε,he,H⟩:=enlargement hK hN hKK hNN; have hf:Tendsto (fun i:ℝ=>c*strength G i^p) trail (𝓝 0):= by
   simpa [show p≠0 from by omega] using ((Coupling.conforms hG (strength_coupling hG)).pow p).const_mul c
 refine ⟨c,hc,?_⟩
 filter_upwards [A,poses (hf.eventually_lt_const he), ifWide] with i hw H' ht q hx; obtain ⟨z,hz,h⟩:=hw _ hx; obtain ha:=h.trans_lt H'
 refine ⟨z,hz,H _ ht.1 _ hx z ha,?_ ,h⟩; intro j hj; rw [uIcc_of_le zero_le_one] at hj
 apply H _ ht.1 _ hx; dsimp only [slopePath]; rw [add_sub_cancel_left, norm_smul,Real.norm_of_nonneg hj.1]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hj.2) ha
omit hG
lemma larger (hx:K⊆conf n)(hy:N ⊆ Outside m): ∃ K':Set (Points n), ∃ N': Set (Points m), IsCompact K' ∧ IsCompact N' ∧
    K ⊆ interior K' ∧ N ⊆ interior N' ∧ K'⊆conf n ∧ N'⊆Outside m:= by
 obtain ⟨U,hU,H,hu⟩:= exists_compact_between hK (conf_open n) hx
 have hh:IsOpen (Outside m):=(conf_open _).preimage (show Continuous (fun x:Points m=> outgoing x) from (continual (g:=id) (f:=fun (_:Points m)=>(0:Points 1)) continuous_const continuous_id))
 obtain ⟨B,hB,hb,h'⟩:=exists_compact_between hN hh hy
 exact ⟨U,B,hU,hB,H,hb,hu,h'⟩
end YM.Integration.GradedFar.Tariff.Crosser
