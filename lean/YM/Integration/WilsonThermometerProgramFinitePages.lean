import YM.Integration.WilsonThermometerProgramBasis
import YM.Integration.WilsonThermometerNumericalBank
import YM.Comparison.RG02.Cumulants.Partition
import YM.Comparison.RG02.Bare.Signals

/-! The full physical numerical birth on each actual finite copy, before taking
a logarithm or specializing its temperature. All child translations are retained. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerProgramFinitePages
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Comparison.RG02
open Comparison.RG02.Bulk Next.SectorChange Multi AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords FVA1Physical.TwoReset
open WilsonThermometerFrozenCopies WilsonCoeffUV WilsonThermometerDeclaredSeeds
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
    (d : V → ℕ) {n f : Side} (o : V → Site n) (g τ : ℝ)
    (v : (j : V) → R.family.label (d j)) (t : V → T → ℂ)
    (h : n.val ∣ f.val) (x : T) (L : Layout G) (pay : Finset Age)
    (u : ℝ) (U : Config G f)
local notation "J" => Stock.census V
local notation "W" => WilsonThermometerNumericalBank.bank R d o g τ v t h x L pay
local notation "raw" => WilsonThermometerFrozenCopies.word R d g τ v t

/-- Scalar and nonconstant original position columns at one of the recorded lifted sites. -/
def atSite (j : V) (z : Site f) : ℂ :=
  t j x * v j 0 + ∑ a : (R.family.labels.level (d j)).Index,
    WilsonThermometerProgramBasis.weight R d g τ v t j u x a *
      (R.family.localSection (d j)).places (Pi.single a 1) z U

private abbrev named (j : V) : Multi.Hot (J) := ⟨(J).fire j, Finset.singleton_nonempty j⟩

private theorem roster (j : V) (p : Fin (Pages n f)) :
    (∑ i : Entry R d, if (J).fire (root R d i) = (J).fire j then
      raw i u x (page h (o (root R d i)) p).val U else 0) =
    ∑ b : Choice R d j, raw (entry R d j b) u x (page h (o j) p).val U := by
  simp [Fintype.sum_sum_type,Fintype.sum_sigma,root,entry,Finset.sum_ite_irrel]
  rfl

private theorem one (j : V) (hu : u ≠ 0) :
    (u ^ (W).power (named j))⁻¹ • (W).mark (named j) u U =
      ∑ p : Fin (Pages n f), atSite R d g τ v t x u U j (page h (o j) p).val := by
  change (u ^ (Launch.index J d ((J).fire j)+1))⁻¹ •
    (∑ p : Fin (Pages n f), ∑ i : Entry R d, if (J).fire (root R d i) = (J).fire j then
      raw i u x (page h (o (root R d i)) p).val U else 0) = _
  simp_rw [roster R d o g τ v t h x u U j]
  simp only [Launch.index,Census.fire,sum_singleton,Complex.real_smul,Complex.ofReal_inv,mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simpa only [mul_sum,atSite] using
    WilsonThermometerProgramBasis.placed R d g τ v t j u x (page h (o j) p).val U hu

theorem source (hu : u ≠ 0) :
    Integral.markedLog u U (W) = Multi.lambda (J) (fun j =>
      ∑ p : Fin (Pages n f), atSite R d g τ v t x u U j (page h (o j) p).val) := by
  ext b
  by_cases zero : b = (J).quiet
  · subst b
    rw [Integral.markedLog, part_lit_quiet, lambda_quiet]
  by_cases born : ∃ j : V, (J).fire j = b
  · obtain ⟨j,rfl⟩ := born
    rw [lambda_part]
    exact (Multi.part_lit _ (named j)).trans (one R d o g τ v t h x L pay u U j hu)
  · let a : Multi.Hot (J) := ⟨b,(Cumulants.hot_iff_ne b).2 zero⟩
    have asleep : (W).mark a u U = 0 := by
      change (∑ p : Fin (Pages n f), ∑ i : Entry R d, if (J).fire (root R d i) = b then _ else 0) = 0
      simp [not_exists.mp born]
    rw [show (Integral.markedLog u U (W)).part b = (u ^ (W).power a)⁻¹ • (W).mark a u U
      from Multi.part_lit _ a, asleep, smul_zero, Multi.lambda, Poly.part_sum]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [Poly.part_send, if_neg (fun e => born ⟨j,e.symm⟩)]

/-- The complete ordinary input before its finite, original Gaussian integral. -/
theorem all_faces (hu : u ≠ 0) (s : (J).Mode) :
    (Poly.pass (Integral.markedLog u U (W))).part s =
      ∏ j ∈ s.val, ∑ p : Fin (Pages n f), atSite R d g τ v t x u U j (page h (o j) p).val := by
  rw [source R d o g τ v t h x L pay u U hu, Cumulants.pass_lambda]

end YM.Integration.WilsonThermometerProgramFinitePages
