import YM.Integration.WilsonCapturedPrimaryPhysicalChamber

/-! The same original compact thermometer cell pays the reflection geometry
for every budget face after a single chosen microscopic translation. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryCenteredMeter
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Extraction
open Extra.Histories Motion PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open Next.Rank WilsonReflectedMicroscopicSites
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {N per:ℕ}
local notation "CF" => R.family
local notation "BB" i:max => ((CF).path.levels.budget i).B
local notation "copy" J:max p:max => Site ((CF).side J p)
local notation "centerOf" p:max J:max i:max => Mix.camp (CF) p J i

theorem charged (φ:Test 3) (r:ℝ) (z:Fin 3→Site ((CF).side N per)) :
    WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per)) z =
      WilsonCenteredCompactBooking.mass R φ r (N,per) z :=by
  exact integral_indicator (WilsonCenteredCompactBooking.measurable_cell R r (N,per) z)

theorem original (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (J v:ℕ) (wide:4<v) (φ:Test 3) :
    ∀ᶠ r:ℝ in 𝓝[>]0,
    let b:=WilsonCapturedPrimarySupportedHalo.date R r
    let k:=WilsonMeasuredWindow.stop (CF).path.levels simple v r
    J ≤ b ∧ b < k ∧ ∀N per (_live:k ≤ N) (z:Fin 3 → Site ((CF).side N per)),
    WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per)) z ≠ 0 →
    ∀i₀:Fin 3, let placedSites:=fun i=>z i-z i₀
    (∀t,8*‖(CF).S.place (placedSites t)‖ ≤ (CF).S.a J) ∧
    (∀u:copy J per,site R (J:=J) placedSites b (u,i₀)=(centerOf per J b) u) ∧
    (∀u:copy J per, ∀s:Finset (Fin 3), coverNumber (BB b)
      (insert ((centerOf per J b) u) (s.image fun t=>site R (J:=J) placedSites b (u,t))) ≤ 1) ∧
    (∀u:copy J per, ∀i j:Fin 3, coverNumber (BB b)
      ({site R (J:=J) placedSites b (u,i),site R placedSites b (u,j)}:Support _) ≤ 1) ∧
    (∀i, b ≤ i → i ≤ k → Cross (BB i) (site R (J:=J) placedSites i)) ∧
    Edition.Spaced (BB k) (site R (J:=J) placedSites k) ∧
    ∀a c:(copy J per)×Fin 3, a ≠ c →
      (BB k)^2 < separation (site R (J:=J) placedSites k a) (site R placedSites k c) :=by
  filter_upwards [WilsonCapturedPrimaryPhysicalArray.original R simple slow J v wide φ,
    WilsonCapturedPrimaryPhysicalChamber.original R J φ] with r geom nearOrigin
  dsimp only at geom nearOrigin ⊢
  refine ⟨geom.1,geom.2.1,?_⟩
  intro N per live z nonzero i₀
  rw [charged R φ r z] at nonzero
  have seats:=geom.2.2 N per live z nonzero (some i₀)
  exact ⟨nearOrigin N per (geom.2.1.le.trans live) z nonzero (some i₀),
    fun u=>seats.1 u i₀ rfl,seats.2⟩

end YM.Integration.WilsonCapturedPrimaryCenteredMeter
