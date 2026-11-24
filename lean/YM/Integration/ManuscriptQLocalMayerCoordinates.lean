import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Splay

/-! The actual no-hole marked molecule reads only the finite square
coordinates selected by the original sector geometry. The count uses the
true Wilson block fibers and the actual purchased molecule shape. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMayerCoordinates

open ConnectedActivityE6 ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider
open scoped BigOperators Classical

theorem cardinal {G : Gauge} {c f : Side} (S : StepData c f) (Z : Support c) (B : ℕ) :
    (podium S G Z B).card ≤ Z.card * tubularPrice G S.patch.L := by
  calc
    _ ≤ (univ.filter (fun e : Tubular f G=>along S e∈Z)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨_,h⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨mem_univ _,h (along S e) (by simp)⟩
    _ ≤ _ := Census.entering (G:=G) S Z

variable {G : Gauge} {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} (I : Finset (Bond f)) {η r q Y W A a β b p v d t γ C s C' μ : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {H : Cash W s μ L Q o C T R}

theorem charged (H : Cash W s μ L Q o C T R) (p : Molecule S) (B : ℕ) :
    ((podium S G (H.unionP p) B).card:ℝ) ≤
      H.shapeW p * (Animals.ballCost (radiusB s):ℝ) * (tubularPrice G S.patch.L:ℝ) := by
  have h : ((podium S G (H.unionP p) B).card:ℝ) ≤
      ((H.unionP p).card:ℝ)*(tubularPrice G S.patch.L:ℝ) := by
    exact_mod_cast cardinal S (H.unionP p) B
  exact h.trans (mul_le_mul_of_nonneg_right (ConnectedActivityE6.Blaze.Flux.spaces H p) (Nat.cast_nonneg _))

end YM.Integration.ManuscriptQLocalMayerCoordinates
