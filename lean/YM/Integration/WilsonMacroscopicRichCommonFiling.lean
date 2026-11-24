import YM.Integration.WilsonMacroscopicRichCountertermAtCapture

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCommonFiling
open Function Filter Set MeasureTheory Lattice Wilson RG Source Marker Extra.Histories
open Extraction Next.Rank Push Push.GridApprox
open Extra.Histories.Relay MergeProof MergeProof.Accent Bid Cells Motion
open Extra.Trajectories Extra.Multi Overlay Exponential Edition
open Planned.GuardedAtom Push.Local MergeProof.Float
open Trace.Physical.GermGraph
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators ContDiff
set_option quotPrecheck false
open RG16.Literal
variable {G:Gauge} (C:Family G) (N p d b u:ℕ)
local notation "terminal" => (C.factory d N p).terminal
variable {ψ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}
    {D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
    {cost:ℕ → ℝ}
    (X : ∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) {g:ℕ→ℝ}
    (h:C.Makes) (hn:u ≤ b) (hN:b ≤ N)
    (hh: Club C.path C.params (C.localSection d) (ζ d) ψ u b N p cost D X g hN)
    (f:Cut C N p) (hf:Continuous f) (z:C.label d)
    (hR: (X b).density 0 (C.localSection d) (C.path.rep N p b) = credit C N p d f b hN +
       ((C.factory d N p).entries b (-(C.factory d N p).terminal.symm z)).density 0 (C.localSection d) (C.path.rep N p b))

include hh hf hR h
theorem readings {E:ℝ}
    (price:∀ i, u ≤ i → i ≤ b → g i + (C.labels.level d).coeffSize (X i).x ≤ E/gainChart C.path b i) :
    ∀ (i : ℕ), u ≤ i → ∀ (ib : i ≤ b) (door : Opened C d i p),
      mCost C d N p i (topReport C N p d h i door (ib.trans hN) f - (terminal).symm z) ≤
        E/gainChart C.path b i := by
  intro i ui ib door
  have club : Club C.path C.params (C.localSection d) (ζ d) ψ i b N p cost D X g hN := by
    refine ⟨fun j ij => hh.ticks j (ui.trans ij),fun j ij => hh.rates j (ui.trans ij),
      fun j ij => hh.votes j (ui.trans ij)⟩
  exact (align C N p d b i X h door ib hN club f hf z hR (price i ui ib)).2

end YM.Integration.WilsonMacroscopicRichCommonFiling
