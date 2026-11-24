import YM.Integration.WilsonSurveyedEquationFramePhysicalWick
import YM.Integration.WilsonSurveyedEquationFrameOccupied
import YM.Integration.WilsonSurveyedEquationFrameReturn

/-! The measured physical and equation columns use one genuine finite section.
The physical column carries the Wick subtraction of its own survey, while the
equation is read on the full normalized inversion integral. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option warningAsError true
namespace YM.Integration.WilsonSurveyedEquationFrameRegulated
open Finset Function Lattice RG Wilson Source Labels Maxwell Push MeasureTheory FVA2
open XSpace XSpace.Rose XSpace.Normalize XSpace.Cirrus PertExtension PertExtension.Orb
open FormalOPE.RG10 FormalOPE.RG10.InversionTop FormalOPE.RG10.InversionWard
open PhysicalNext.Repeat.Legato WilsonMaxwellThermometerWardConditional
open WilsonCoeffUV.Cosmos.Polestar
open WilsonSurveyedEquationFrameInlet (bank)
open WilsonSurveyedEquationFrameBasis (projection kernel)
open WilsonSurveyedEquationFramePhysicalWick (chart retune)
open WilsonPositionProgramTrialPublicJointSourceInventory (lifted)
open scoped Classical BigOperators
variable {G : Gauge} (W : Initialize G) {d : ℕ}
local notation "F_" k:arg => (primes G).F k

def file (d : ℕ) : Label G d ≃ₗ[ℂ] Label G d :=
  (chart (W.surveys d) (-1)).trans (bank W d).P

private theorem onfile (v : Label G d) :
  projection (chart (W.surveys d) (-1) v) = (W.surveys d).insertW (-1) (projection v) := by
  change projection ((W.surveys d).insertW (-1) (projection v) + kernel v) = _
  have gone : projection (kernel v) = 0 := by
    rw [kernel,LinearMap.sub_apply,LinearMap.id_apply,map_sub,
      WilsonSurveyedEquationFrameOccupied.idempotent,sub_self]
  rw [map_add,WilsonSurveyedEquationFramePhysicalWick.restored,gone,add_zero]

theorem exact (v : Label G d) :
    (bank W d).joined.evaluate ((F_ d).coords (file W d v)) =
      (bank W d).physical.evaluate ((F_ d).coords ((W.surveys d).insertW (-1) (projection v))) +
      (bank W d).ward.evaluate ((F_ d).coords ((bank W d).A (kernel v))) := by
  rw [show file W d v = (bank W d).P (chart (W.surveys d) (-1) v) from rfl,(bank W d).reads,onfile]
  have eq : kernel (chart (W.surveys d) (-1) v) = kernel v := by
    change chart (W.surveys d) (-1) v - projection (chart (W.surveys d) (-1) v) = kernel v
    rw [onfile]
    exact add_sub_cancel_left _ _
  rw [eq]

theorem bill (d : ℕ) : ∃C : ℝ, 0 ≤ C ∧
    ∀p : Label G d, ‖(F_ d).coords ((file W d).symm p)‖ ≤ C * ‖(F_ d).coords p‖ := by
  let L := (((F_ d).coords.symm.trans (file W d).symm).trans (F_ d).coords).toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖,norm_nonneg _,fun p => ?_⟩
  simpa [L] using L.le_opNorm ((F_ d).coords p)

/-- Exact vanishing of the equation part of this same fitted chart, including
both orientations of every varied edge and the already fixed thermal clock. -/
theorem settled (d : ℕ) : ∃ r M : ℕ, ∀(P : Period), M ≤ P.side.val →
    ∀x : P.Sites, 2*r+4 < separation x (-x) →
    (∀e : Edge P.Sites, e.1 ∈ (bank W d).ward.footprint x → e.1+Lattice.step e.2 ∈ (bank W d).ward.footprint x →
      far r x (reflect e)) →
    ∀(p : Label G d) (L : ℂ →L[ℝ] ℝ) (Y : Config G P.side → ℝ) (s : Set P.Sites),
      PreTest Y → LocalOn s Y →
      (∀e : Edge P.Sites, e.1 ∈ s → e.1+Lattice.step e.2 ∈ s → far r x e ∧ far r x (reflect e)) →
      Bare.normalized (W.tree P) G (BareOrb.stencil (W.tree P) (fun U =>
        L ((bank W d).ward.places ((F_ d).coords ((bank W d).A (kernel ((file W d).symm p)))) x U)) *
        BareOrb.stencil (W.tree P) Y) = 0 := by
  obtain ⟨r,M,pay⟩ := WilsonSurveyedEquationFrameReturn.erases W.hol (F_ d) (bank W d).ward
    (fun h => (bank W h).A) (bank W d).first
  exact ⟨r,M,fun P cut x span clear p L Y s => pay P cut x span clear _
    (WilsonSurveyedEquationFrameBasis.equation ((file W d).symm p)) L (W.tree P) Y s⟩

def print (d : ℕ) (v : On.Grade G d) : Label G d :=
  (W.surveys d).insertW (-1) (lifted d v)

/-- The coefficients are filed before every site, tree, test and other occupied
slot. Each raw term is the literal joined group word after its own suspension. -/
theorem original (v : Sec G d) {n : ℕ} (Y : Sample n) (x : Y.F.Sites) :
    regal W d Y x v =
      ∑k:Fin (d+1), ((Y.F.spacing:ℂ)^k.val)⁻¹ •
        ∑i:(F_ k.val).Index, ((F_ k.val).basis.repr (print W k.val (part d k.val v)) i) •
          Bare.raw (W.tree Y.F.p) (W.surveys k.val) x (projection ((F_ k.val).basis i)).val := by
  unfold regal
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun a : Bare.Series (W.tree Y.F.p) G => ((Y.F.spacing:ℂ)^k.val)⁻¹ • a)
  let F := F_ k.val
  let p := print W k.val (part d k.val v)
  change Bare.raw (W.tree Y.F.p) (W.surveys k.val) x p.val =
    ∑i:F.Index,F.basis.repr p i • Bare.raw (W.tree Y.F.p) (W.surveys k.val) x (projection (F.basis i)).val
  have retained : projection p = p := WilsonSurveyedEquationFramePhysicalWick.kept (W.surveys k.val) (-1) _
  have dec : p = ∑i:F.Index,F.basis.repr p i • projection (F.basis i) := by
    conv_lhs => rw [←retained,←F.basis.sum_repr p]
    rw [map_sum]
    simp only [map_smul]
  conv_lhs => rw [dec]
  change Bare.raw (W.tree Y.F.p) (W.surveys k.val) x
    ((localFields G k.val).subtype (∑i:F.Index,F.basis.repr p i • projection (F.basis i))) = _
  unfold Bare.raw
  rw [map_sum,map_sum]
  simp only [map_smul]
  rfl

end YM.Integration.WilsonSurveyedEquationFrameRegulated
