import YM.Integration.WilsonPositionProgramConsultedFaces
import YM.Integration.WilsonPositionProgramSeriesRead
import YM.Integration.WilsonPositionProgramSubmittedRate

/-! Resolve the submitted Wilson coefficients on the same chronological
notebook that supplies both the original stopped and the changed MS tables.
The genuine estimator is valid for every commissioned notebook. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramSharedInversionTariff
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSeriesRead WilsonPositionProgramInversionMaterial
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal BigOperators
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
      let _L := WilsonPositionProgramInfraredMeter.wallet C D m j w i H
      ∀ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p →
        ∀ (I : Type) [Fintype I] [LinearOrder I] (child : I → Fin n) (d : I → ℕ)
          (trees : ∀ x, (D.step (i x)).p.Tree) (q : ℕ), q ≤ p → ∀ strength : ℕ,
        ∃ cutoff : ℕ, ∀ x, cutoff ≤ i x → 1≤C.family.path.levels.clock.hatBeta (m x) →
          RG16.Lambda C.family.path.levels (m x)≤(i x:ℝ)*Real.log D.ratio →
        ∀ (P : ChartRatio G) (_law : LocalRatio P) (ζ : Axes C d → PowerSeries ℂ),
          let edge := fun u : Terms C d q =>
            Rocket.stopped S Y Z F (Lodge.basisR C) Finset.univ d (axis C d u.1)
              (final j) (fun x => z x ∘ child) x u.2.val.2
          ‖PowerSeries.coeff (q+ceiling C d) (XSpace.Bare.normalized (trees x) G
            (finite C (D.step (i x)).p d (z x ∘ child) (trees x) ζ))-
              ∑ u : Terms C d q, weight C d q ζ u * (edge u : ℂ)‖ₑ ≤
            ENNReal.ofReal ((D.step (i x)).spacing^strength) * ∑ u : Terms C d q, ‖weight C d q ζ u‖ₑ := by
  obtain ⟨H,hH,start,publish⟩ := WilsonPositionProgramConsultedFaces.original (X:=X) C D
    first paid slow Z p color nonempty K compact
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach old z c box support S L F file I _ _ child d trees q hq strength
  have parents := publish m j i w blocks reach old z c box support F file
  let A := fun (u : Terms C d q) x =>
    PowerSeries.coeff (u.2.val.2+degree C d u.1) (WilsonPositionProgramCopyTop.normalized C
      (D.step (i x)).p d (z x ∘ child) (axis C d u.1) (trees x))
  let P' := fun (u : Terms C d q) x => Rocket.stopped S Y Z F (Lodge.basisR C) Finset.univ d
    (axis C d u.1) (final j) (fun x => z x ∘ child) x u.2.val.2
  let E := fun (u : Terms C d q) x => ‖A u x-(P' u x : ℂ)‖ₑ
  have receipts (u : Terms C d q) : Carry L (Rocket.wage S Y Z F (final j) (1/2)) (E u) := by
    have sum : u.2.val.1+u.2.val.2=q := Finset.HasAntidiagonal.mem_antidiagonal.mp u.2.property
    exact parents I child d (axis C d u.1) trees u.2.val.2 (by omega)
  have budget := Carry.sum Finset.univ E (fun u _ => receipts u)
  obtain ⟨cutoff,rate⟩ := WilsonPositionProgramSubmittedRate.original D C simple m j w i blocks reach Z F H budget strength
  refine ⟨cutoff,?_⟩
  intro x cut mature room P law ζ edge
  rw [WilsonPositionProgramSeriesRead.original C _ d (z x ∘ child) (trees x) P law q ζ]
  apply WilsonPositionProgramSeriesRead.paid
  have read (u : Terms C d q) : row C (D.step (i x)).p d (z x ∘ child) P q u=A u x := by
    rw [row,reported,PowerSeries.coeff_mk]
    exact (WilsonPositionProgramCopyTop.original C _ d (z x ∘ child) (axis C d u.1) P law (trees x) u.2.val.2).symm
  simpa only [read] using rate x cut mature room

end YM.Integration.WilsonPositionProgramSharedInversionTariff
end
