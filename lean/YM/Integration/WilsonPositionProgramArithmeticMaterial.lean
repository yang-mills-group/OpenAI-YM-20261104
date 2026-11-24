import YM.Integration.WilsonPositionProgramArithmetic
import YM.Integration.WilsonPositionProgramArithmeticAtlas
import YM.Integration.WilsonPositionProgramSubmittedCoefficient
import YM.Integration.WilsonPositionProgramSubmittedFaces
import YM.Integration.WilsonPositionProgramSubmittedProgram

/-! The original position construction on a run with the two arithmetic receipts.
The same native blocks, circuits, prescriptions and tests are retained in each publication. -/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticSubmittedCoefficient
open WilsonPositionProgramSubmittedCoefficient
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
include first paid slow in
/- The finite tree, field labels, compact profile and all relative sites belong to the submitted Wilson table.
The common age notebook and copies are chosen before those field labels and both physical regulator limits. -/
theorem original {n : ℕ} (nonempty : 0 < n) (K : Set (Points n)) (compact : IsCompact K) : ∃ H : ℝ, 0 ≤ H ∧
    ∃ start : ℕ, ∀ (m j i : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) → ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
      (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      let L := WilsonPositionProgramInfraredMeter.wallet C D m j w i H
      ∃ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p ∧
        ∀ (d : Fin n → ℕ) (v : (b : Fin n) → (C.family.labels.level (d b)).Index)
          (tree : ∀ x, (D.step (i x)).p.Tree) (q : ℕ), q ≤ p →
          Carry L (Rocket.wage S Y Z F (final j) (1/2)) (fun x =>
            ‖PowerSeries.coeff (q+Kick.depthF Finset.univ d v)
              (WilsonPositionProgramCopyTop.normalized C (D.step (i x)).p d (z x) v (tree x)) -
              (Rocket.stopped S Y Z F (Lodge.basisR C) Finset.univ d v (final j) z x q : ℂ)‖ₑ) := by
  obtain ⟨H,hH,sites⟩ := WilsonPositionProgramSubmittedGeometry.roster K compact
  obtain ⟨start,fund⟩ := WilsonPositionProgramArithmeticInfraredAtlas.purchased (X:=X) C D first paid slow Z p
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach old z c box support S L
  let B := WilsonPositionProgramInfraredAtlas.budget C D m j w blocks
  let room := fun x => center (D.step (i x)) (c x)
  obtain ⟨F,file⟩ := Calibration.tomorrows S Y G Z color (Rocket.native j) p
  refine ⟨F,file,?_⟩
  intro d v tree q hq
  obtain ⟨unit,small⟩ := WilsonPositionProgramInfraredCircuit.units C D m j w blocks
  have zero (x : X) : B.peak (Page.opening j x)=0 := by change Real.log (S.l _)=0; rw [unit,Real.log_one]
  have top (x : X) := WilsonPositionProgramInfraredCircuit.fine D j w x (i x) (reach x)
  have hpos : (S.dialect Y G Z (sheet F)).cushion (1/8) room := by
    intro x
    change (1/8:ℝ)*(WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val ≤
      Spatial.singular (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val (room x)
    rw [top]
    exact pin _ (c x) (box x)
  have near (b : Fin n) : Nearest room L (fun x => z x b) :=
    WilsonPositionProgramInfraredMeter.displacements C D m j w i H z c (fun x => sites _ _ _ (support x)) b
  have cash := Rocket.soothe S Y Z F (Lodge.basisR C) Finset.univ d v (final j) (chart_ok G)
    (fund m j w blocks old) file zero unit (WilsonPositionProgramInfraredMeter.age C D m j w blocks i H)
    small simple (show RegulatorIR.Taping.quantum 1 0 ≤ Lodge.through p by dsimp [RegulatorIR.Taping.quantum,Lodge.through]; omega)
    (show (0:ℝ)<1/8 by norm_num) hpos z (fun b _ => near b) ⟨_,near ⟨0,nonempty⟩⟩ q hq
  apply cash.mono
  intro x
  dsimp only
  rw [WilsonPositionProgramCopyTop.original C _ d (z x) v (chart G) (chart_ok G) (tree x) q]
  rw [←Complex.ofReal_sub]
  simp only [←ofReal_norm,Complex.norm_real]
  rw [top]
  rfl

end YM.Integration.WilsonPositionProgramArithmeticSubmittedCoefficient
end

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticSubmittedFaces
open WilsonPositionProgramSubmittedFaces
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
include first paid slow in
/- All proper and full rosters of one compact preparation share the original calendar, table and book.
The lone analytic room probe belongs to the original compact set and remains available on the empty face. -/
theorem original {n : ℕ} (nonempty : 0 < n) (K : Set (Points n)) (compact : IsCompact K) : ∃ H : ℝ, 0 ≤ H ∧
    ∃ start : ℕ, ∀ (m j i : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) → ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
      (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      let L := WilsonPositionProgramInfraredMeter.wallet C D m j w i H
      ∃ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p ∧
        ∀ (I : Type) [Fintype I] [LinearOrder I] (child : I → Fin n)
          (d : I → ℕ) (v : (b : I) → (C.family.labels.level (d b)).Index)
          (tree : ∀ x, (D.step (i x)).p.Tree) (q : ℕ), q ≤ p →
          Carry L (Rocket.wage S Y Z F (final j) (1/2)) (fun x =>
            ‖PowerSeries.coeff (q+Kick.depthF Finset.univ d v)
              (WilsonPositionProgramCopyTop.normalized C (D.step (i x)).p d ((z x) ∘ child) v (tree x)) -
              (Rocket.stopped S Y Z F (Lodge.basisR C) Finset.univ d v (final j) (fun x => (z x) ∘ child) x q : ℂ)‖ₑ) := by
  obtain ⟨H,hH,sites⟩ := WilsonPositionProgramSubmittedGeometry.roster K compact
  obtain ⟨start,fund⟩ := WilsonPositionProgramArithmeticInfraredAtlas.purchased (X:=X) C D first paid slow Z p
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach old z c box support S L
  let B := WilsonPositionProgramInfraredAtlas.budget C D m j w blocks
  let room := fun x => center (D.step (i x)) (c x)
  obtain ⟨F,file⟩ := Calibration.tomorrows S Y G Z color (Rocket.native j) p
  refine ⟨F,file,?_⟩
  intro I _ _ child d v tree q hq
  obtain ⟨unit,small⟩ := WilsonPositionProgramInfraredCircuit.units C D m j w blocks
  have zero (x : X) : B.peak (Page.opening j x)=0 := by change Real.log (S.l _)=0; rw [unit,Real.log_one]
  have top (x : X) := WilsonPositionProgramInfraredCircuit.fine D j w x (i x) (reach x)
  have hpos : (S.dialect Y G Z (sheet F)).cushion (1/8) room := by
    intro x
    change (1/8:ℝ)*(WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val ≤
      Spatial.singular (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val (room x)
    rw [top]
    exact pin _ (c x) (box x)
  have near (b : Fin n) : Nearest room L (fun x => z x b) :=
    WilsonPositionProgramInfraredMeter.displacements C D m j w i H z c (fun x => sites _ _ _ (support x)) b
  have cash := Rocket.soothe S Y Z F (Lodge.basisR C) Finset.univ d v (final j) (chart_ok G)
    (fund m j w blocks old) file zero unit (WilsonPositionProgramInfraredMeter.age C D m j w blocks i H)
    small simple (show RegulatorIR.Taping.quantum 1 0 ≤ Lodge.through p by dsimp [RegulatorIR.Taping.quantum,Lodge.through]; omega)
    (show (0:ℝ)<1/8 by norm_num) hpos (fun x => (z x) ∘ child) (fun b _ => near (child b)) ⟨_,near ⟨0,nonempty⟩⟩ q hq
  apply cash.mono
  intro x
  dsimp only
  rw [WilsonPositionProgramCopyTop.original C _ d ((z x) ∘ child) v (chart G) (chart_ok G) (tree x) q]
  rw [←Complex.ofReal_sub]
  simp only [←ofReal_norm,Complex.norm_real]
  rw [top]
  rfl

end YM.Integration.WilsonPositionProgramArithmeticSubmittedFaces
end

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramArithmeticSubmittedProgram
open WilsonPositionProgramSubmittedProgram
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

include first paid slow in
/- The complete finite position publication on the current normalized copy and the actual variable
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
  obtain ⟨start,fund⟩ := WilsonPositionProgramArithmeticInfraredAtlas.purchased C D first paid slow Z p
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

end YM.Integration.WilsonPositionProgramArithmeticSubmittedProgram
end
