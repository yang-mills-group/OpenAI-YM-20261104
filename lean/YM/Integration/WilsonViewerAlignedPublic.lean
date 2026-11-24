import YM.Integration.WilsonViewerGridMS

/-! One original positioned field portfolio and one independent, oriented
measurement. The inlet prices only true screened microscopic ordinary moments. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato Lattice
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonThermometerWeakMeasuredSeries WilsonPositionHomogeneousFrame
open WilsonViewerGridPins WilsonViewerReportingGrid WilsonViewerAlignedResidual
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {L:EveryPhase.Almanac F} {Y:(Bel R.family.book).Hierarchy}
    {arch:Trace.Terrace.Arch R.family} {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop} (run:Selected.{u} F L Q J Y arch ℓ simple cohort)

structure Report (F:Final R.family f S) (ℓ:Ultrafilter (ℕ×ℕ)) (H:ℕ) (g:ℝ→ℝ) where
  grid:Grid (ℓ:=ℓ) F H g
  rows:ℝ→Maps R.family S H
  paid:∀ᶠ r in trail,Lives grid r (rows r)

include run in
theorem Selected.report (H:ℕ) (g:ℝ→ℝ) (temp:Coupling G g) : Nonempty (Report F ℓ H g):=by
  obtain ⟨Γ⟩:=WilsonViewerReportingGrid.original F simple run.bliss g temp H
  obtain ⟨E,live⟩:=portfolio Γ
  exact ⟨⟨Γ,E,live⟩⟩

variable (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)} {branch:Bool} (ms:Main.Match Z simple M σ branch)
    (ν:ℝ) {n H:ℕ} {d:Caps n} (v:MaxwellSlots R.family d) (within:∀i,d i≤H)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z
local notation "c" => coefficient Z M ν H (commonCaps v within)

def PinBill (P:Report F ℓ H θ) (W:Finset E4) (p q:ℕ) : Prop :=
  ∀ K, IsCompact K → K⊆conf n → ∃ C,0≤C ∧ ∀ᶠr in trail,∀ o y,y∈K→
    Pin R.family.S W r (P.grid.date r) o y →
      ∃ᶠ k:ℕ in atTop, f.late fun N per=>‖atCut (R:=R) d (P.grid.date r) o
        (fun u i=>(P.rows r).field ⟨d i,Nat.lt_succ_of_le (within i)⟩ u (pub r (d i) (v i))) (N,per)-
        WilsonViewerGridMS.read Z M ms ν (commonCaps v within) q (θ r) y k‖≤C*(θ r)^p

include run in
theorem Selected.cutoff_nodes (P:Report F ℓ H θ) (W:Finset E4) (p q:ℕ)
    (signed:PinBill Z M ms ν v within P W p q) :
    Nodes R.family.S W P.grid.date (fun r=>measured F none (pub r) v r-approximate c q (θ r)) θ p:=by
  intro K compact clear
  obtain ⟨C,hC,priced⟩:=signed K compact clear
  refine ⟨C,hC,?_⟩
  filter_upwards [priced,P.paid,RG17.positiveLength] with r sale live rp o y hy pin
  exact WilsonViewerGridPins.compare P.grid rp live run.original (pub r) v within pin
    (WilsonViewerGridMS.read Z M ms ν (commonCaps v within) q (θ r) y)
    (WilsonViewerGridMS.point Z M ms ν (commonCaps v within) q (θ r) y (clear hy))
    _ (sale o y hy pin)

include run in
/-- Smooth, joint tests with their actual total variation. -/
theorem Selected.aligned_tests (P:Report F ℓ H θ) (W:Finset E4) (p q:ℕ) (temp:Coupling G θ)
    (signed:PinBill Z M ms ν v within P W p q) :
    WilsonThermometerWeakValueRecovery.Signed trail (conf n)
      (fun r=>measured F none (pub r) v r-approximate c q (θ r)) θ p 0:=
  run.grid_tests Z M ms ν v within P.grid W p q temp (run.cutoff_nodes Z M ms ν v within P W p q signed)

include run in
/-- Derivatives at every real separated configuration and in every physical viewer. -/
theorem Selected.aligned_positions (P:Report F ℓ H θ) (W:Finset E4) (j p q:ℕ)
    (retain:WilsonThermometerWeakSignedJets.high j p≤q) (temp:Coupling G θ)
    (signed:PinBill Z M ms ν v within P W (WilsonThermometerWeakSignedJets.high j p+1) q) :
    ∀ K, IsCompact K → K⊆conf n → ∀ ε:ℝ,0<ε → ∀ᶠr in trail,∀x∈K,∀viewer:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F viewer (pub r) v r) x-
        iteratedFDeriv ℝ j (approximate c p (θ r)) x‖≤ε*(θ r)^p:=
  run.grid_positions Z M ms ν v within P.grid W j p q retain temp
    (run.cutoff_nodes Z M ms ν v within P W _ q signed)

end YM.Integration.WilsonViewerElectedHierarchy
end
