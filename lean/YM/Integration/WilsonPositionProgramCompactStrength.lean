import YM.Integration.WilsonPositionProgramSubmittedRate
import YM.Integration.WilsonPositionProgramSubmittedFaces
import YM.Integration.WilsonPositionProgramSignedFace

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramCompactStrength
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramNestedElection.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

open Finset WilsonThermometerPositionInversionWords WilsonPositionProgramSignedFace

private theorem weighted {I : Type} [Fintype I] (a E F : I → ℂ) :
    ‖(∑ b, a b * E b) - ∑ b, a b * F b‖ₑ ≤
      (∑ b, ‖E b - F b‖ₑ) * ∑ b, ‖a b‖ₑ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (enorm_sum_le ..).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b _
  rw [enorm_mul,mul_comm]
  exact mul_le_mul_right (Finset.single_le_sum (fun j _ => zero_le (a:=‖a j‖ₑ)) (mem_univ b)) _
include first paid slow in
/-- On one preselected compact hierarchy, all proper subsets, native fitted
columns, tests and their independent placements share the same calendar.
The true finite field amplitude is explicitly charged just once. -/
theorem original {n : ℕ} (nonempty : 0 < n) (K : Set (Points n)) (compact : IsCompact K) : ∃ H : ℝ, 0 ≤ H ∧
    ∃ start : ℕ, ∀ (m j i : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) → ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
      (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      ∃ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p ∧
        ∀ (I : Type) [Fintype I] [LinearOrder I] (child : I → Fin n)
          (d : I → ℕ) (_tree : ∀ x, (D.step (i x)).p.Tree) (k : ℕ), k ≤ p →
          ∀ strength : ℕ, ∃ cutoff : ℕ, ∀ x, cutoff ≤ i x →
            1≤C.family.path.levels.clock.hatBeta (m x) →
            RG16.Lambda C.family.path.levels (m x)≤(i x:ℝ)*Real.log D.ratio →
            ∀ (g τ : ℝ) (v : (j:I) → C.family.label (d j)) (t : I → ℂ),
          let A := fun (b : Basis C d) => amplitude C d g τ v (fun j (_ : Unit) => t j) () b
          let P := fun (b : Basis C d) => Rocket.stopped S Y Z F (Lodge.basisR C) univ
            (fun j : ↥(occupied C d b) => d j.val) (axisOf C d b) (WilsonPositionProgramSubmittedFaces.final j)
            (fun x j => z x (child j.val)) x k
          ‖reading C (D.step (i x)).p d (z x ∘ child) g τ v t k - ∑ b, A b * (P b : ℂ)‖ₑ ≤
            ENNReal.ofReal ((D.step (i x)).spacing^strength) * ∑ b, ‖A b‖ₑ := by
  obtain ⟨H,hH,start,publish⟩ := WilsonPositionProgramSubmittedFaces.original (X:=X) C D
    first paid slow Z p color nonempty K compact
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach old z c box support S
  obtain ⟨F,file,parents⟩ := publish m j i w blocks reach old z c box support
  refine ⟨F,file,?_⟩
  intro I _ _ child d tree k hk strength
  let M := fun (b : Basis C d) x => PowerSeries.coeff (k+WilsonThermometerPositionInversionWords.grade C d b)
    (leaf C (D.step (i x)).p d (z x ∘ child) b (tree x))
  let P := fun (b : Basis C d) x => Rocket.stopped S Y Z F (Lodge.basisR C) univ
    (fun j : ↥(occupied C d b) => d j.val) (axisOf C d b) (WilsonPositionProgramSubmittedFaces.final j)
    (fun x j => z x (child j.val)) x k
  let E := fun (b : Basis C d) x => ‖M b x - (P b x : ℂ)‖ₑ
  have receipt := fun (b : Basis C d) => parents (↥(occupied C d b)) (fun j => child j.val)
    (fun j => d j.val) (axisOf C d b) tree k hk
  have bound := Carry.sum univ E (fun b _ => receipt b)
  obtain ⟨cutoff,rate⟩ := WilsonPositionProgramSubmittedRate.original D C simple m j w i blocks reach Z F H bound strength
  refine ⟨cutoff,?_⟩
  intro x hcut mature room g τ v t A P'
  rw [WilsonPositionProgramSignedFace.original C (D.step (i x)).p d (z x ∘ child) g τ v t (tree x) k]
  apply (weighted A (fun b => M b x) (fun b => (P b x:ℂ))).trans
  exact mul_le_mul_left (rate x hcut mature room) _

end YM.Integration.WilsonPositionProgramCompactStrength
end
