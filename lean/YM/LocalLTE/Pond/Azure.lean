import YM.LocalLTE.Pond.Signs
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
lemma ridge_same (i:Spikes n): (Price.ridge R p i).site=i.1.2:= rfl
lemma boostT (i:EKey n): (Price.tubeX R p X i).site=(incoming X R p i).site ∧ (incoming X R p i).support ⊆ (Price.tubeX R p X i).support:=by
    rcases i with i|i|⟨v,i⟩
    · exact ⟨rfl,Finset.Subset.refl _⟩
    · exact ⟨rfl,Finset.Subset.refl _⟩
    exact ⟨rfl,Finset.image_subset_image (Price.erect ..)⟩
-- paint height.C costs. High geometric increase.Share.
def tH (p:BudgetPoint) := Scarf.kiosk p.supportExponent 2
lemma ridge_w {k:ℝ}(hk:0≤k) (i:Spikes n): p.mass (Price.ridge R p i).support k ≤ tH p*p.mass (highEntry G R i).support k:=by
    by_cases hx:High.length R i.2 < p.B
    · change p.mass (i.1.spread (bloomH R p 0 i.2)) k ≤ _; rw [bloomH,if_pos hx,BudgetPoint.mass,Seat.visit_count]; refine le_trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ p.exponent_pos.le)) hk) (show tH p*k ≤_ from mul_le_mul_of_nonneg_left (p.loMass (highEntry G R i).support k hk) (Real.exp_nonneg _)); exact_mod_cast Scarf.standing _ p 2 (0:Site n) le_rfl
    · rw [show (Price.ridge R p i).support=(highEntry G R i).support from congr_arg (Seat.spread i.1) (if_neg hx)]; exact le_mul_of_one_le_left (mul_nonneg (Real.exp_nonneg _) hk) (Real.one_le_exp (mul_nonneg p.exponent_pos.le (Nat.cast_nonneg _)))
lemma heightL {f:Spikes n→ ℝ} (hp:∀ i,0 ≤ f i)(hf: anchored p (highEntry G R) f k) : anchored p (Price.ridge R p) f (tH p*k):=by
    have h':0≤tH p:= Real.exp_nonneg _
    intro x; refine budget_mono (budget_scale h' (hf x)) (fun i=>?_) (fun i=>?_)
    · split; next=>exact mul_nonneg (Real.exp_nonneg _) (hp _)
      exact le_rfl
    split
    next hx=> rw [if_pos (show (highEntry G R _).site=x from hx)]; exact ridge_w (hp _) _
    next hx=> rw [if_neg (show (highEntry G R _).site≠x from hx),mul_zero]
-- post regular budget with same reps.Contrast easily.AFF sanitized but not yet sewn.
variable {ι:Type}
def Stocked (p:BudgetPoint)(X:ι→ RegularAddress n)(g:ι→Pot G n)(k:ℝ):Prop:= ∃ w:ι→ℝ,(∀ i,p.Regular (X i|>.support) (g i)∧ p.supBounds (X i).site (X i).support (g i) (w i))∧anchored p X w k
variable (α Δ)
end YM.AnalyticBridge.VerifiedReset.Collection.Price
