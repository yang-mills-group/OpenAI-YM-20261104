import YM.Integration.PhysicalMSOPECandidate

/-! The final ordinary-OPE reduction in the original complete physical
frame.  The native OPE remainder already pays the whole inverse frame.
Consequently the displayed, finitely truncated formal comparison has the
requested coupling order exactly when its signed complete-product residual
has that order.  No estimate for that second residual is assumed here.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.MSOPEPhysicalTransfer
open Filter Set Spec OPE OPE.Orbits PhysMS Asymptotics
open Pert.Position RG11.Neighborhood
open EngineeringWeightedReadout PhysicalMSOPECandidate
open scoped Topology Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (H : Leading F J) (hF : Foundation F R)
    {n i D : ℕ} (U : Detector S D) (v : Fin n → E C.labels i)
    (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η)
    (g : ℝ → ℝ) (hg : Trace.Pilot.Coupling G g) (hG : G.Simple)

include H hF hM hη hg hG in
/-- Arbitrary approaching scales and separated configurations are allowed.
The formal block may depend on the configuration; the physical frame,
fields, detector and formal conversion remain the original ones.

This equivalence isolates the genuinely unpaid signed residual.  It does
not replace that estimate with scalar, unweighted or absolute-density
smallness. -/
theorem remainder_isLittleO_iff
    {A : Type*} {l : Filter A} (r : A → ℝ)
    (hr : Tendsto r l Trace.Pilot.trail) (x : A → Fin n → E4)
    (hx : ∀ᶠ a in l, WithinRoom (r a) M η (x a) 0)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : A → Blocks C.labels n i D) (N : ℕ) :
    (fun a => actualOutput F R J v (r a) (x a) -
      composedTruncation p Z (B a) v N (g (r a))) =o[l]
        (fun a => g (r a) ^ N) ↔
    (fun a => weightedMSResidual J U p Z (B a) v N (g (r a)) (r a) (x a)) =o[l]
      (fun a => g (r a) ^ N) := by
  have hO := detectorOPE_whole_readout_flat_along F R U J H hF v
    M η hM hη g hg hG r hr x hx N
  have hs :
      (fun a => actualOutput F R J v (r a) (x a) -
        composedTruncation p Z (B a) v N (g (r a))) =
      (fun a => weightedMSResidual J U p Z (B a) v N (g (r a)) (r a) (x a) -
        wholeReadout U J (r a) (detectorOPEError F R J v U (r a) (x a))) := by
    funext a
    exact exact_split F R J U p Z (B a) v N (g (r a)) (r a) (x a)
  rw [hs]
  constructor
  · intro h
    simpa only [Pi.add_apply, sub_add_cancel] using h.add hO
  · intro h
    exact h.sub hO

end YM.Integration.MSOPEPhysicalTransfer
