import YM.Integration.WilsonPositionProgramOriginalLanding

/-! The original Wilson field dictionary reaches the separated continuum
MS coefficient on every touched compact tuple of the actual position mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramMSMesh
open Filter Set Finset Metric Lattice RG PhysicalNext.Repeat.Legato
open MS MS.Rake MS.Land MS.Dial MS.Tide MS.Orbit MS.Vista
open XSpace XSpace.Cirrus XSpace.Expense FVA2 FVA2.Arrival FVA2.Arrival.Schedule FVA2.Notch
open WilsonPositionProgramOriginalLanding
open scoped Classical Topology
open private grown from YM.FVA2.Notch.Card
variable {G : Gauge} (C : Run G) (D : XSpace.Run)
variable {n : ℕ} {O : Booked (Press.portDeck G)} (M : MS_Data G O)
variable (Q : Prescription (Press.portDeck G)) (labels : Fin n→Label (Press.portDeck G))
variable (μ : ℝ) (k : ℕ) (K : Set (Points n)) (compact : IsCompact K) (sep : K⊆conf n)
local notation "ρ" => (1/16:ℝ)

private theorem clear (v : Sample n) (h : Sized v) : FVA2.Notch.Entry ρ v := by
  left
  intro b
  have bound := MS.Vista.E_n _ (Schedule.cleared v h b)
  change ρ* ((periodN (psi v.F)).val:ℝ) ≤ _
  linarith

include compact sep in
theorem original (simple : G.Simple)
    (paid : TaylorOKPl M (YM.FVAAlt2.Lobby.Table (RegulatorIR.FVAAlt2.Lodge.basisR C) (Press.portDeck G)) Q) :
    ∃ B : ℝ, 0<B ∧ ∀ᶠ i in atTop, ∀ (z : Fin n → Cover) (c : Four ℝ), c ∈ (D.step i).Box →
      (D.step i).rel z c ∈ K →
      ‖opened C Q labels μ k ⟨D.step i,z,c⟩ -
        tour M labels μ (plot ((D.step i).rel z c)) univ k‖ ≤ B*(D.step i).spacing^Tide.mildG := by
  obtain ⟨B,pos,fee⟩ := WilsonPositionProgramOriginalLanding.flight C M Q labels μ k K compact sep simple paid
  let good := fun v : Sample n => ‖opened C Q labels μ k v -
    tour M labels μ (plot (familiar v)) univ k‖ ≤ B*v.F.spacing^Tide.mildG
  have run := Stretched.runs D
  have mesh := (goesFront run).eventually (grown.mp (Pitch.purchase good fee))
  refine ⟨B,pos,?_⟩
  filter_upwards [mesh,run.smaller,run.horizon.eventually_ge_atTop 16] with i heard unit size
  intro z c center loc
  let v : Sample n := ⟨D.step i,z,c⟩
  have hsize : (16:ℕ) ≤ v.F.p.side.val := Nat.cast_le (α:=ℝ) |>.mp (show ((16:ℕ):ℝ) ≤ ((v.F.p.side.val):ℝ) from size)
  exact heard v rfl (clear v ⟨hsize,unit,center⟩) loc

end YM.Integration.WilsonPositionProgramMSMesh
