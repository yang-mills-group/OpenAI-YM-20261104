import YM.RG05Readout.Planes.Suites
import YM.RG05Readout.Planes.Polish

/-! The physical return of an addressed field over a finite reporting interval.
    The low component is retained at the original upper cutoff. The remaining
    coordinate pays the mesh ratio only to the missing joint weight. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarReturn
open Finset Filter Lattice Wilson RG Source Extra.Histories RG05Readout RG05Readout.Address
open RG05Readout.Native RG05Readout.Planes RG05Readout.Pulse
open scoped Classical Topology
variable {G : Gauge} {C : Family G} {D : Rail C} {B : ℕ → ℕ → ℝ} {b d : ℕ}

theorem returned (h : C.Makes) (wallet : Awake D B b d) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ {u N p : ℕ} (mu : m ≤ u) (uN : u ≤ N)
      {H : Sight C d p} {U : Emblems C d} (_ : Spine D B h b p d N H U)
      {e : ℕ} (_ : e < d) (x : Palette C d) (_ : Address.clear C d e x = 0),
      ∃ v : Palette C d, Address.clear C d e v = v ∧
        let top := finer U uN x
        let marked := (finer U (mu.trans uN)).symm (top-v)
        Address.clear C d e marked = 0 ∧
        size marked ≤ Real.exp (ε*(C.S.scale u-C.S.scale m)) *
          (C.S.a m / C.S.a u)^(d-(e+1))*size x ∧
        ∀ φ : Body,
          fieldC C u N p d (Many.point U x u N) φ =
          fieldC C m N p d
            (Many.point U (lightest C d m u • (marked + (finer U (mu.trans uN)).symm v)) m N) φ := by
  obtain ⟨start, ready⟩ := eventually_atTop.mp (service_fine wallet)
  filter_upwards [eventually_ge_atTop b, eventually_ge_atTop start, tariff wallet ε positive]
    with m base late funded u N p mu uN H U spine e weight x high
  let top := finer U uN x
  have origin : (finer U uN).symm top = x := LinearEquiv.symm_apply_apply _ _
  have tint : Tint B C d m := ⟨fun i hi => ready i (late.trans hi)⟩
  obtain ⟨v,hv,zero,bill⟩ := quotient_move h wallet spine tint base (le_refl m) mu uN
    top weight (origin.symm ▸ high)
  refine ⟨v,hv,zero,?_,?_⟩
  · rw [origin] at bill
    apply (le_of_mul_le_mul_left (a := bounty B d m) ·
      (zero_lt_one.trans_le (bounty_head (B:=B) (d:=d) m)))
    calc
      _ ≤ bounty B d u * (C.S.a m / C.S.a u)^(d-(e+1))*size x := bill
      _ ≤ (bounty B d m * Real.exp (ε*(C.S.scale u-C.S.scale m))) *
            (C.S.a m / C.S.a u)^(d-(e+1))*size x :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (funded u mu) (pow_nonneg (div_nonneg (C.S.a_pos _).le
            (C.S.a_pos _).le) _)) (size_ge _)
      _ = _ := by ring
  · intro φ
    have sum : (finer U (mu.trans uN)).symm (top-v) +
        (finer U (mu.trans uN)).symm v = (finer U mu).symm x := by
      rw [←map_add,sub_add_cancel,Many.sumwalk U mu uN]
      exact congrArg ((finer U mu).symm) origin
    rw [sum]
    exact summit U x mu uN φ

end YM.Integration.WilsonAddressedCollarReturn
