import YM.Integration.WilsonPositionProgramMSMesh
import YM.Integration.WilsonPositionProgramPoint

/-! Compare the original finite Wilson prescription and the independently
issued, fixed-block position directory at their literal common positions and
period, through their common calibrated continuum tensor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramSharedDirectory
open Filter Function Set Finset Metric Maxwell Lattice RG PhysicalNext.Repeat.Legato
open MS MS.Rake MS.Land MS.Dial XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Arrival FVA2.Arrival.Schedule
open WilsonPositionProgramOriginalLanding
open scoped Classical Topology
variable {G : Gauge} (C : Run G) {simple : G.Simple} (Z : WilsonPrescription G)
variable {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (matchMS : Main.Match Z simple M T dial)
variable (Q : Prescription (Press.portDeck G))
    (paid : TaylorOKPl M (YM.FVAAlt2.Lobby.Table (RegulatorIR.FVAAlt2.Lodge.basisR C) (Press.portDeck G)) Q)
variable {n : ℕ} (d : ℕ) (v : Fin n→Dframe.Toon G d) (μ : ℝ) (k : ℕ)
variable (K : Set (Points n)) (compact : IsCompact K) (apart : K⊆conf n)

include matchMS paid compact apart in
theorem original :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ᶠ i in atTop, ∀ cap (P : Handoff.Directory Z i cap),
    Handoff.Directory.budget G n d+k ≤ cap → ∀ (z : Fin n → Cover) (c : Four ℝ), c∈(Z.run.step i).Box →
      (Z.run.step i).rel z c∈K →
      ‖opened C Q (Dframe.flash ∘ v) μ k ⟨Z.run.step i,z,c⟩ -
        WilsonPositionProgramPoint.entry Z (T:=T) P d μ z (Dframe.fill v) k‖ ≤
      A*(Z.run.step i).spacing^Tide.mildG+B*Speed.chip (Z.run.step i) := by
  obtain ⟨A,posA,priceA⟩ := WilsonPositionProgramMSMesh.original C Z.run M Q (Dframe.flash ∘ v)
    μ k K compact apart simple paid
  obtain ⟨B,posB,priceB⟩ := WilsonPositionProgramPoint.priced Z matchMS d μ K compact apart (Dframe.fill v) k
  refine ⟨A,B,posA,posB,?_⟩
  filter_upwards [priceA,priceB] with i measured filed
  intro cap P enough z c hc hz
  have a := measured z c hc hz
  have b := filed cap P z c enough hc hz
  rw [Dframe.ribbon] at b
  rw [norm_sub_rev] at b
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add a b)

end YM.Integration.WilsonPositionProgramSharedDirectory
