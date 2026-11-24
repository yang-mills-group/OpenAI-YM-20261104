import YM.Integration.WilsonMacroscopicRichUnreplicatedFiling

/-! The single-source reporting reservation from a measured coefficient and its actual remainder. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCaptureFilingBudget
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open MergeProof MergeProof.Accent MergeProof.Float PhysicalNext.Repeat Lotus RG16.Literal
open Extra.Histories.Relay Trace.Physical.GermGraph Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} (C:Family G) (N k m p d:ℕ) (H:C.Makes)
variable {W:Worth} {u ψ φ δ:ℕ → ℝ} {r:ℕ → ℕ} {ζ:ℕ → ℕ → ℝ}
  {D:∀ N p i:ℕ,i<N → GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
local notation "T"=>C.path
local notation "R"=>C.path.rep N p
local notation "S!"=>C.localSection d
local notation "F"=>C.labels.level d
local notation "T!"=>C.factory d N p


def capital (C:Family G) (k:ℕ) (rem η:ℝ) : ℝ :=
  4*(1+(C.path.levels.params k).columns)*(2*rem+η)

theorem original (scrim:Scrim C W u ψ φ δ ζ r D)
    (f:Cut C N p) (hf:Continuous f) (Q:Coefficient F (C.side k p)) (rem η:ℝ) (ηpos:0 < η)
    (ht:C.ref d ≤ m)(mk:m ≤ k)(kN:k ≤ N)
    (formatted:Q.Format 0 C.params (R k))
    (forced:Q.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) rem)
    (amount:(F).coeffSize Q.x ≤ rem) (source:credit C N p d f k kN=Q.density 0 S! (R k)) :
    let E:=capital C k rem η
    ∃ z:C.label d, Next.UVStress.quota C d k N p z ≤ 2*E ∧
      ∀ (i:ℕ),m ≤ i → ∀ (ik:i ≤ k)(door:Opened C d i p),
        mCost C d N p i (topReport C N p d H i door (ik.trans kN) f-(T!).terminal.symm z)
          ≤ E/gainChart T k i := by
  dsimp only
  let E:=capital C k rem η
  let θ:=‖alto T m d‖*(E/gainChart T k m)
  let w:=ζ d m/(2*(1+θ))
  have abs0:0 ≤ (F).coeffSize Q.x:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have rem0:0 ≤ rem:=abs0.trans amount
  have cpos:0 < 2*rem+η:=by linarith
  have columns:1 ≤ (C.path.levels.params k).columns:=(C.path.levels.params k).columns_ge
  have Epos:0 < E:=by dsimp only [E,capital];exact mul_pos (by linarith) cpos
  have gain:0 < gainChart T k m := Real.exp_pos _
  have θ0:0 ≤ θ:=mul_nonneg (norm_nonneg _) (div_nonneg Epos.le gain.le)
  have ζ0:=scrim.grows d m ht
  have wp:0 < w:=div_pos ζ0 (by positivity)
  have reserved:w*‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2 := by
    calc
      _ = w*θ := mul_assoc ..
      _ ≤ w*(1+θ) := mul_le_mul_of_nonneg_left (by linarith) wp.le
      _ = _ := by dsimp only [w];field_simp [show 1+θ ≠ 0 by positivity]
  obtain ⟨z,quota,_,_,_,_,_,_,_,allDates⟩:=WilsonMacroscopicRichUnreplicatedFiling.original
    C N k m p d H scrim w wp f hf Q rem (2*rem+η) E ht mk kN formatted forced
    (by linarith) cpos (le_refl _) reserved source
  exact ⟨z,quota,allDates⟩

end YM.Integration.WilsonMacroscopicRichCaptureFilingBudget
