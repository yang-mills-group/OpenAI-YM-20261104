import YM.Integration.WilsonThermometerFrozenRevaluation
import YM.Integration.WilsonThermometerDeclaredSeeds
import YM.Integration.WilsonOriginalStarSceneRead

/-! Read the enrolled numerical Wilson thermometer at each positive formal argument
in the genuine original position basis, before fixing or integrating the field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerProgramBasis
open Function Finset Lattice Wilson RG PhysicalNext.Repeat.Legato
open ActualRunCurvaturePackets NativeCurvatureTensor WilsonOriginalStarSceneWords
open WilsonThermometerDeclaredSeeds
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {V T : Type} (d : V → ℕ)
    (g τ : ℝ) (v : (j : V) → R.family.label (d j)) (t : V → T → ℂ)
    (j : V) {f : Side} (u : ℝ) (x : T) (z : Site f) (U : Config G f)
local notation "F" => R.family.labels.level (d j)
local notation "D" => ofRun R (d j)
local notation "W" => WilsonThermometerFrozenCopies.word R d g τ v t
local notation "divisor" => ((u ^ (d j + 1) : ℝ) : ℂ)⁻¹

def weight (a : (F).Index) : ℂ :=
  let k := ActualRunGradedKernels.rank R (d j) a
  (((g/u)^k : ℝ):ℂ) * (t j x * ((F).core (v j)) a * (((τ⁻¹)^k : ℝ):ℂ))

private lemma unit (hu : u ≠ 0) :
    (divisor) * W (.inl j) u x z U = t j x * v j 0 := by
  simpa [root, pole, raw, rank, scalar, Atom.unmasked, Atom.poly] using
    WilsonThermometerFrozenRevaluation.divided R d g τ v t (.inl j) u x z U hu

private lemma column (hu : u ≠ 0) (a : (F).Index) :
    (∑ m : ↥(((D).data.shape a).support), (divisor) *
      W (.inr ⟨j,a,m⟩) u x z U) =
    weight R d g τ v t j u x a * (R.family.localSection (d j)).places (Pi.single a 1) z U := by
  rw [placed_basis (D),basisValue,Finset.mul_sum]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro m _
  have h := WilsonThermometerFrozenRevaluation.divided R d g τ v t
    (.inr ⟨j,a,m⟩) u x z U hu
  change (divisor) * _ = _ at h
  rw [h]
  change _ * (_ * WilsonOriginalStarLaurentWallet.coefficient R (d j) 1 1
    ((F).core (v j)) ⟨a,m⟩ * _ * ↑((WilsonOriginalProjectedCurvatureAtom.atom _ _).unmasked U z)) = _
  rw [WilsonOriginalProjectedCurvatureAtom.unmasked]
  simp only [WilsonOriginalStarLaurentWallet.coefficient, div_one,one_pow,Complex.ofReal_one,
    one_mul, weight, pole, root, Sum.elim_inr, WilsonOriginalStarLaurentWallet.lag, WilsonOriginalStarLaurentWallet.shape]
  ring_nf
  rfl

/-- The unit and every native curvature column retain their own Laurent degree.
The real fitted coefficients and the child's site are unchanged. -/
theorem placed (hu : u ≠ 0) :
    (divisor) * (∑ b : Choice R d j, W (entry R d j b) u x z U) =
    t j x * v j 0 + ∑ a : (F).Index,
      weight R d g τ v t j u x a * (R.family.localSection (d j)).places (Pi.single a 1) z U := by
  rw [Finset.mul_sum, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_sigma]
  rw [show (divisor) * W (entry R d j (.inl ())) u x z U = t j x * v j 0 from
    unit R d g τ v t j u x z U hu]
  apply congrArg (fun w : ℂ => t j x * v j 0 + w)
  exact Finset.sum_congr rfl fun a _ => column R d g τ v t j u x z U hu a

end YM.Integration.WilsonThermometerProgramBasis
end
