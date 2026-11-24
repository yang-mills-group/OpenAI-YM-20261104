import YM.Integration.WilsonOriginalStarSceneWords
import YM.Integration.WilsonNeutralCopiedField

/-! Original ultraviolet Wilson words at every configuration and every individual cutoff site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointBareWords
open Function Finset Lattice Wilson RG Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PertExtension ActualRunCurvaturePackets NativeCurvatureTensor
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(d:ℕ)
local notation "F₀"=>R.family.labels.level d
local notation "B₀"=>ofRun R d
local notation "T₀"=>R.family.localSection d

abbrev Term (j:(F₀).Index):=↥((B₀).data.shape j).support

def rank (j:(F₀).Index)(m:Term R d j):ℕ:=m.val.sum fun _ n=>n

def atom (j:(F₀).Index)(m:Term R d j):Atom G (rank R d j m):=
  WilsonOriginalProjectedCurvatureAtom.atom (fun k=>(word m.val k).2)
    (fun k=>(B₀).data.columns j (word m.val k).1)

def weight (j:(F₀).Index)(m:Term R d j):ℝ:=(MvPolynomial.coeff m.val ((B₀).data.shape j)).re

theorem invariant (j:(F₀).Index)(m:Term R d j):(atom R d j m).Invariant:=
  WilsonOriginalProjectedCurvatureAtom.invariant _ _

theorem billed (j:(F₀).Index)(m:Term R d j):
    ActualRunGradedKernels.rank R d j ≤ rank R d j m:=(B₀).data.low j m.val m.property

theorem placed (j:(F₀).Index){n:Side}(z:Site n)(U:Config G n):
    ((T₀).places (Pi.single j 1) z U).re =
      ∑m:Term R d j,weight R d j m*(atom R d j m).unmasked U z:=by
  rw [placed_basis (B₀) j z U]
  unfold basisValue
  rw [←Finset.sum_coe_sort]
  change Complex.reCLM (∑m:Term R d j,MvPolynomial.coeff m.val ((B₀).data.shape j) *
    value (fun k=>(word m.val k).2) (fun k=>(B₀).data.columns j (word m.val k).1 |>.atSite U z)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [←WilsonOriginalProjectedCurvatureAtom.unmasked (fun k=>(word m.val k).2)
    (fun k=>(B₀).data.columns j (word m.val k).1) z U]
  simp [weight,atom,Complex.mul_re]; exact Or.inl rfl

theorem cutoff (N per:ℕ)(x:R.family.label d)(z:Site (R.family.side N per))(U:Config G (R.family.side N per)):
    R.family.O N per x z U =
      ∑j,WilsonNeutralCopiedField.coefficients R N per x j *
        ((∑m:Term R d j,weight R d j m*(atom R d j m).unmasked U z:ℝ):ℂ):=by
  rw [←WilsonNeutralCopiedField.elected R N per x z,WilsonNeutralCopiedField.field]
  simp_rw [placed R d]

end YM.Integration.WilsonMeasuredPointBareWords
