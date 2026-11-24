import YM.LocalTaylorR2.Kiln.Season
import YM.WilsonCoeffUV.Reclosure.Paths.RetainBase

/-! The two incoming ordered walks in the measured quadratic action, with
their Wilson weights, physical masks, held backgrounds, and length charges. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonHeldKineticSectorPurchase
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Kiln
open Axial Channel Canvas
open Itinerary Port WilsonCoeffUV.Bank.Mosaic Stationary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

theorem original {G : Gauge} {W : ℝ} (P : Teller G) (o : Target.Order G W)
    (Q : ConnectedActivityE6.Target G P) (L : Side) (patch : Patch) (hp : patch.Branches P.bind G)
    (v d : ℝ → ℝ) (hv : Rate G L (-(1/2)) v) (hd : Rate G L (-(1/2)) d)
    (pos : ∀ᶠ x in atTop, 0 ≤ v x) (p j : ℕ) (χ : Chi) {η : ℝ} (hη : 0 < η) :
    ∃ a b : ℝ → ℝ, Rate G L (-((p+4 : ℕ) : ℝ)/2) a ∧ Rate G L 0 b ∧
      ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f) (μ C : ℝ)
        (H : Cash W x μ L Q o C T R), S.patch = patch →
        (∀ i : Trans f, Sees H j (v x) (d x) χ
          (debt (primary G) (p+3) (tides R.path) R o.a R.beta i)
          (bill (a x) (b x) R.beta x (tides R.path) i) (seating Q.halo x S (tides R.path) i)) ∧
        Sales (radiusB x) Q.relative Q.ε (atomFoot S.ratio Q.halo (radiusB x) (tides R.path))
          (fun i => bill (a x) (b x) R.beta x (tides R.path) i * (betaF G x L ^ (1/2 : ℝ))^p)
          (atomCharge (tides R.path)) (betaF G x L ^ (-(1/2 : ℝ)+η)) := by
  obtain ⟨a,b,ha,hb,reads⟩ := portrait G P o L (primary G) patch hp v d hv hd pos 2 j (p+3) χ Q.halo
  have hQ : 0 ≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  have sums := shops G L Q.halo p 2 P.top.width Q.ε Q.relative Q.usable hQ Q.grants.2.1
    ha hb (Rate.const (gramCost G P.top.paths)) (1/2) 0 (-(1/2)+η) le_rfl (by norm_num) (by linarith)
  refine ⟨a,b,ha,hb,?_⟩
  filter_upwards [reads,sums] with x hrs hs
  intro c f S T R μ C H hpatch
  let I := H.laws.intake
  have hL := H.laws.data.funds.length_eq
  have hK := I.cap.paths
  have hβ := I.window.2
  rw [hL] at hK hβ
  refine ⟨fun i => hrs c f S T R Q μ C H hpatch R.beta (tides R.path) i (tones R.path _), ?_⟩
  have charge := hs c f S hL (tides R.path) (tides_pay hK) R.beta
    (by simpa only [abs_of_nonneg I.positive.le] using hβ)
  simpa only [Real.rpow_zero, one_mul] using charge

end YM.Integration.WilsonHeldKineticSectorPurchase
