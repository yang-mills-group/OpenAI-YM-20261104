import YM.WiderProfiles.Basket
import YM.WiderProfiles.Reached
/-!
# Wider test profiles for the independent prescription

`wholeBook` chooses a Wilson prescription, MS data and a position
prescription once. Both `Main.Match` and the wider-profile estimates
hold for that choice. A comparison with measured physical correlation
functions requires a separate estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Structure1 XSpace.Cirrus Filter
open scoped Classical Topology

theorem wholeBook (G : Gauge) (h : G.Simple) :
    ∃ (N : WilsonPrescription G)
      (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)),
      N.run=Notch.stair ∧ Main.Match N h T S true ∧
      ∀ (d n k a : ℕ) (c D : ℝ) (hc : 0 < c), 1 ≤ D → ∀ p : Tags G d n,
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in Front, ∀ s : Sample n, grab s=m → ∀ hy : Admits a c D s,
        ‖Rose.measureₓ N.scheme N.criterion d s k p -
          Scale.Measure.start N.scheme N.criterion d n ⟨familiar s, hy.conf hc⟩ k p‖ ≤
          C * m.spacing^(mildG/2) := by
  obtain ⟨N,T,S,hN,H⟩ := Main.solution G h Notch.stair true
  exact ⟨N,T,S,hN,H,matched N h T S H⟩
end YM.FVA2.WiderProfiles
-- The corresponding wider-profile estimates are available for individual kernels and forests.

