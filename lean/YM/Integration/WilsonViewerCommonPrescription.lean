import YM.Integration.WilsonViewerElectedHierarchy

/-! The physical position thermometer is the one argument of both independent
polynomials. Fix the original extraction, the MS prescription and the external
roster before taking a joint separated correlation and OPE measurement. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonViewerElectedHierarchy
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score
open MS MS.Land MS.Fleet WilsonMSDictionaryVector WilsonPositionHomogeneousFrame
open WilsonPositionSeparatedProfileMatching
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin} {J : ℝ → PhysMS.tower S}
    {Y : (Bel R.family.book).Hierarchy} {A : Trace.Terrace.Arch R.family}
    {ℓ : Ultrafilter (ℕ × ℕ)} {cohort : Ultrafilter (ℕ × ℕ) → Prop} {simple : G.Simple}
    (run : Selected.{u} F L Q J Y A ℓ simple cohort) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "P" => homogeneous F J Z
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z

include run in
/-- Source hypotheses are one original unselected correlation and the signed
finite independent experiments at each radius. The output includes the
actual tested ordinary product evaluated on every fixed-clearance exterior. -/
theorem Selected.joined {σ : Prescription (Press.portDeck G)} {branch : Bool}
    (matchMS : Main.Match Z simple M σ branch) (ν : ℝ)
    {m : ℕ} (d₀ : ℕ) (φ : Test m) (v₀ : Fin m → Sec G d₀) (p₀ : ℕ)
    (g₀ : ℝ → ℝ) (running : Coupling G g₀)
    (clock : ∃ B : ℝ, 0 < B ∧ ∀ᶠ r in trail, g₀ r ≤ B * |θ r|)
    (correlation : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail,
      ‖observed Z F J none d₀ φ v₀ r - polynomial Z M ν d₀ φ v₀ p₀ (θ r)‖ ≤ ε * |θ r|^p₀)
    {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i)) (h q : ℕ)
    {K : Set (Points n)} (compact : IsCompact K) (separated : K ⊆ conf n)
    {E : Type} [Fintype E] {e : E → ℕ} (w : Labels S e) {δ η : ℝ}
    (distance : 0 < δ) (slack : 0 < η) (a : ℝ → Test n → ℝ)
    (detector : ∀ᶠ r in trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
      ∃ᶠ s : ℝ in atTop,
        ‖(P r h).symm (RG17.basket Q h (fun i => P r (d i) (v i)) r ψ) -
          experiment R.family d h Z M ν v ψ ((matchMS.separatedOPE ν).wilson.light h).choose q (θ r) s‖ ≤ a r ψ) :
    matchesThrough Z M F J ν d₀ φ v₀ p₀ ∧
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r in trail, ∀ ψ : Test n, tsupport ψ ⊆ K →
      ∀ y : E → E4, ClearOf 0 y δ → ∀ p : Viewers F,
      ‖RG17.query F (fun i => P r (d i) (v i)) y w p r ψ -
        upon (spectator F p) h 0 y w (P r h (prediction R.family d h Z M ν v ψ q (θ r)))‖ ≤
        r^((h:ℝ)+1-η) * (∫ x : Points n, ‖ψ x‖) + D * a r ψ := by
  refine ⟨run.correlations Z M ν d₀ φ v₀ p₀ g₀ running clock correlation, ?_⟩
  obtain ⟨D,Dn,publicCoefficient⟩ :=
    run.coefficients Z M matchMS ν d v h q θ w distance K a detector
  have grade := WilsonViewerOriginalProducts.charges F Q J Z simple run.leading run.obeys d v
  have spatial := RG17.testedPacketBound Q run.facilities.toServices
    (fun r i => P r (d i) (v i)) h (fun _ => 0) grade compact separated slack distance w
  refine ⟨D,Dn,?_⟩
  filter_upwards [publicCoefficient,spatial] with r coefficient room ψ supported y clear p
  let actual := RG17.basket Q h (fun i => P r (d i) (v i)) r ψ
  have exactField := room ψ supported y clear p
  simp only [Finset.sum_const_zero,sub_zero] at exactField
  exact (norm_sub_le_norm_sub_add_norm_sub _ (upon (spectator F p) h 0 y w actual) _).trans
    (add_le_add exactField (coefficient ψ supported 0 y clear p))

end YM.Integration.WilsonViewerElectedHierarchy
end
