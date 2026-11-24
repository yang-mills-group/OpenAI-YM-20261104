import YM.Integration.WilsonPositionProgramSubmittedClock
import YM.Integration.WilsonPositionProgramSubmittedSpoken
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedProgram
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramNestedElection.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

include first paid slow in
/-- The complete finite position publication on the current normalized copy and the actual variable
Wilson prescription after all its kinetic, scalar and field changes. The calibration is chosen once
for every submitted label and every compactly supported test on this geometry. -/
theorem original {n : ℕ} (nonempty : 0<n) (K : Set (Points n)) (compact : IsCompact K) :
    ∃ H : ℝ, 0≤H ∧ ∃ start : ℕ, ∀ (m j : X→ℕ) (w : X→ℕ→ℕ) (i : X→ℕ)
      (blocks : ∀ x t, (C.family.S.block (m x+t)).val = D.ratio^(w x t))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      ∃ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p ∧
        ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
          (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
          ∀ {deck : MS.Local.Physical.Deck G} (labels : Fin n → MS.Rake.Label deck) (Q : MS.Land.Prescription deck)
          (q : ℕ), q≤p → ∀ strength : ℕ, ∃ threshold : ℕ, ∀ x, threshold ≤ i x →
          1≤ C.family.path.levels.clock.hatBeta (m x) → RG16.Lambda C.family.path.levels (m x)≤(i x:ℝ)*Real.log D.ratio →
          let ε := fun t => (D.step (i t)).spacing
          let θ := fun t => Real.log (ε t)
          ‖PowerSeries.coeff q (YM.FVAAlt2.Lobby.newEra (chart G) (Lodge.basisR C) Q (θ x) labels
              (wrap (D.step (i x)).p.side ∘ z x) (ε x)) -
            PowerSeries.coeff q (Rocket.adjust S Y Z F (Lodge.basisR C) (WilsonPositionProgramSubmittedCoefficient.final j)
              labels z Q θ ε x)‖ₑ ≤ ENNReal.ofReal ((ε x)^strength) := by
  obtain ⟨H,Hpos,sites⟩ := WilsonPositionProgramSubmittedGeometry.roster K compact
  obtain ⟨start,fund⟩ := WilsonPositionProgramInfraredAtlas.purchased C D first paid slow Z p
  refine ⟨H,Hpos,start,?_⟩
  intro m j w i blocks reach old S
  let L := WilsonPositionProgramInfraredMeter.wallet C D m j w i H
  let ε := fun t => (D.step (i t)).spacing
  let θ := fun t => Real.log (ε t)
  obtain ⟨F,file⟩ := Calibration.tomorrows S Y G Z color (Rocket.native j) p
  refine ⟨F,file,?_⟩
  intro z c box support deck labels Q q hq strength
  obtain ⟨unit,small⟩ := WilsonPositionProgramInfraredCircuit.units C D m j w blocks
  have top (x) := WilsonPositionProgramInfraredCircuit.fine D j w (x:=x) (i:=i x) (reach x)
  let room := fun x => center (D.step (i x)) (c x)
  have hpos (x:X) : (1/8:ℝ)*S.P x ≤ Spatial.singular (S.P x) (room x) := by
    change (1/8:ℝ)*(WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val ≤
      Spatial.singular (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val (room x)
    rw [top]
    simpa only [room,div_eq_mul_inv,mul_comm] using pin (D.step (i x)) (c x) (box x)
  have near (b : Fin n) : Nearest room L (fun x => z x b) :=
    WilsonPositionProgramInfraredMeter.displacements C D m j w i H z c (fun x => sites _ _ _ (support x)) b
  have clock := WilsonPositionProgramSubmittedClock.paid C D m j w i H
  have zero (x:X) : (WilsonPositionProgramInfraredAtlas.budget C D m j w blocks).peak (Page.opening j x)=0 := by change Real.log (S.l _)=0; rw [unit,Real.log_one]
  have scored := Rocket.funded S Y Z F (Lodge.basisR C) (WilsonPositionProgramSubmittedCoefficient.final j) (chart_ok G)
    (fund m j w blocks old) file zero unit (WilsonPositionProgramInfraredMeter.age C D m j w blocks i H)
    small simple (show RegulatorIR.Taping.quantum 1 0 ≤ Lodge.through p by dsimp [RegulatorIR.Taping.quantum,Lodge.through]; omega)
    (show (0:ℝ)<1/8 by norm_num) hpos labels z Q θ ε near ⟨_,near ⟨0,nonempty⟩⟩ clock.2 clock.1
    (fun x => (D.step (i x)).positive.ne')
  obtain ⟨threshold,rate⟩ := WilsonPositionProgramSubmittedRate.original D C simple m j w i blocks reach Z F H (scored q hq) strength
  refine ⟨threshold,fun x hx mature wallet => ?_⟩
  have h := rate x hx mature wallet
  dsimp only at h ⊢
  simp only [map_sub] at h
  change ‖PowerSeries.coeff q (YM.FVAAlt2.Lobby.newEra (chart G) (Lodge.basisR C) Q (θ x) labels
    (wrap (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)) ∘ z x) (ε x)) -
    PowerSeries.coeff q (Rocket.adjust S Y Z F (Lodge.basisR C) (WilsonPositionProgramSubmittedCoefficient.final j)
      labels z Q θ ε x)‖ₑ ≤ ENNReal.ofReal ((ε x)^strength) at h
  rw [top x] at h
  exact h

end YM.Integration.WilsonPositionProgramSubmittedProgram
