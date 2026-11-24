import YM.XSpace.Layout
import YM.Integration.ActualOriginalOrbitCoefficients

/-! Exact geometry of a common finite inversion regulator. The physical
period choice and the position scheme's epoch are independently named. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochRegulator

open Lattice PhysicalNext.Repeat.Legato

theorem same {G : Gauge} (R : Run G) (V : XSpace.Run) (N per i : ℕ) :
    (R.family.S.a N = (V.step i).spacing ∧ R.family.side N per = (V.step i).p.side) ↔
      ((R.family.S.denominator N).val = V.ratio ^ i ∧
       (R.family.S.period per).val = V.finalSide.side.val * V.ratio ^ (V.reserve*i*i)) := by
  let n := (R.family.S.denominator N).val
  let p := (R.family.S.period per).val
  have hs : R.family.S.a N = (V.step i).spacing ↔ n = V.ratio ^ i := by
    change (n : ℝ)⁻¹ = ((V.ratio ^ i : ℕ) : ℝ)⁻¹ ↔ _
    simp only [inv_inj, Nat.cast_inj]
  rw [hs]
  constructor
  · rintro ⟨hn,hside⟩
    refine ⟨hn,?_⟩
    have hv := congrArg PNat.val hside
    change p*n = V.finalSide.side.val * V.ratio ^ (i+V.reserve*i*i) at hv
    rw [hn, pow_add, mul_comm (V.ratio ^ i), ←mul_assoc] at hv
    exact Nat.eq_of_mul_eq_mul_right (V.den_pos i) hv
  · rintro ⟨hn,hp⟩
    refine ⟨hn,PNat.eq ?_⟩
    change p*n = V.finalSide.side.val * V.ratio ^ (i+V.reserve*i*i)
    change n = V.ratio ^ i at hn
    change p = V.finalSide.side.val * V.ratio ^ (V.reserve*i*i) at hp
    rw [hn,hp, pow_add]
    ac_rfl

/-- Engineering exponents have no effect on the independent Laurent slot
shift. The placement fee in the historical position scheme is the reciprocal
of the actual product of spacings. -/
theorem units {G : Gauge} (R : Run G) (V : XSpace.Run) (N i : ℕ)
    (hs : R.family.S.a N = (V.step i).spacing) {I : Type*} [Fintype I] (d : I → ℕ) :
    (∏ j, ((V.step i).spacing : ℂ)⁻¹ ^ d j) =
      (ActualLeadingIR.engineeringScale R.family d N : ℂ)⁻¹ := by
  rw [←hs]
  unfold ActualLeadingIR.engineeringScale
  simp [inv_pow, Finset.prod_inv_distrib]

end YM.Integration.WilsonEpochRegulator
end

