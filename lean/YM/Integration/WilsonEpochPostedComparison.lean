import YM.Integration.WilsonEpochPhysicalFront
import YM.Integration.WilsonEpochSubmittedReports

/-! The separated finite MS bound for the closed, independently computed
physical UV graph on its own regulator. The one remaining entry is the
actual signed source discrepancy after the true field/coupling conversion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochPostedComparison
open Function Filter Set Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register MS MS.Land FormalBulk08.Flat
open WilsonEpochPhysicalFront WilsonEpochMeshTransport WilsonEpochPositionCoefficients
open WilsonEpochSubmittedReports
open scoped Topology Classical BigOperators

theorem measured {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
    (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (α : G.ColorIndex)
    {hG : G.Simple} (Z : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)
    (lo : ℕ → ℕ) (ν : ℝ) (n d k : ℕ) (p : Tags G d n) (K : Set (Points n))
    (hK : IsCompact K) (hs : K ⊆ conf n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c : ℕ in atTop, ∀ per ≥ entrance R lo c, ∀ D : ℕ,
      let m := mesh R c per
      ∀ f : Test n, tsupport f ⊆ K → ∀ b : ℝ, TestBudget.Bound f b →
      ‖publish ν S m (report m d (graph R L α Z.scheme c per D)) k n f p -
        Reg.CoverTest.Rates ν T d k n f p‖ ≤
        ‖publish ν S m (report m d (residual R Z.scheme m.p.side)) k n f p‖ +
          b*C*(R.family.S.a c)^MS.Tide.mildG := by
  obtain ⟨C,hC,good⟩ := (M.exactbreg ν n d k p K hK hs).2
  refine ⟨C,hC,?_⟩
  filter_upwards [invoice R lo good] with c hc per hp D m f hf b hb
  let f₀ := Reg.Pivot.posted ν Z.scheme S d m k n f p
  let g := publish ν S m (report m d (residual R Z.scheme m.p.side)) k n f p
  let f₁ := Reg.CoverTest.Rates ν T d k n f p
  have hnew : publish ν S m (report m d (graph R L α Z.scheme c per D)) k n f p = f₀ + g := by
    exact congrArg (fun r : Reports G d => r k n f p) (posted R L α Z.scheme S ν c per D d)
  rw [hnew]
  have hg : f₀ + g - f₁ = g + (f₀-f₁) := by abel
  change ‖f₀+g-f₁‖ ≤ ‖g‖ + _
  rw [hg]
  exact (norm_add_le _ _).trans (add_le_add_right (hc per hp f hf b hb) ‖g‖)

end YM.Integration.WilsonEpochPostedComparison
end
