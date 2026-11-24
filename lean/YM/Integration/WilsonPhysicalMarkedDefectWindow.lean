import YM.Integration.WilsonPhysicalMarkedDefectPost
import YM.Integration.WilsonPhysicalMarkedDefectRate

/-! Restore the presold radius on the original common window. The time
threshold precedes all lower endpoints, periods, cutoffs, angles and marks. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect

open Function Filter Finset Lattice RG RG.Supply Precision Wilson Marker ConnectedActivityE6
open AllOrder AllOrder.Transit WheelP PhysicalNext PhysicalNext.Repeat Legato
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open FVA1Physical.MixedResets
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)
include simple

/-- The *actual* varying restoration factor, including all occupied indices,
on a single common window. The factor 72 pays the scalar/regular rooted
publication of the 18-unit signed bill. The second inequality pays the whole
already divided hard field, without separating individual partners. -/
theorem common_radius (p pieces s q : ℕ) (reach ε η δ : ℝ) (hr : 0 ≤ reach) (hε : 0 < ε)
    (regular : η+2*ε < δ) (hard : (p:ℝ)+1-δ+2*ε < ((2*s:ℕ):ℝ)) :
    ∀ᶠ b : ℕ in atTop, ∀ m i : ℕ, m ≤ i → i < b → PaceR.Close R q reach m b →
      ∀ (β : ℝ), β ∈ RG.Shoot.band R.alloy.B.a (i+1) →
        let g := Coat.gStep β
        let c := (Sycamore.battery R pieces (i+1) b)^pieces
        4 * (c * (18 * ((2:ℝ)^((p:ℝ)+1-η) * g^((p:ℝ)+1-η)))) ≤ g^((p:ℝ)+1-δ) ∧
          c * (2*g)^(2*s) ≤ g^((p:ℝ)+1-δ) := by
  let r := (p:ℝ)+1-η
  let t := (p:ℝ)+1-δ
  obtain ⟨B,hB⟩ := eventually_atTop.1 (restored_rate (72*(2:ℝ)^r) r t ε
    (by positivity) (by dsimp [r,t]; linarith))
  obtain ⟨K,hK⟩ := eventually_atTop.1 (restored_rate ((2:ℝ)^(2*s)) ((2*s:ℕ):ℝ) t ε
    (by positivity) (by dsimp [t]; linarith))
  filter_upwards [PaceR.gives R simple q (Sycamore.fire pieces*pieces) reach hr ε hε,
    PaceR.covers_hat R simple q reach,(Sycamore.too R simple).eventually_ge_atTop (4*max B K)]
    with b bill covered grown
  intro m i mi ib near β band g c
  have top : R.alloy.B.a.clock.hatBeta b ≤ 4*β := by
    have middle := covered (i+1) m (Nat.le_succ_of_le mi) ib near
    linarith only [middle,band.1]
  have charge : c ≤ (4*β)^ε := by
    have h := bill m (i+1) (Nat.le_succ_of_le mi) ib near
    exact (show c ≤ (R.alloy.B.a.clock.hatBeta b)^ε by simpa only [c,Sycamore.battery,pow_mul] using h).trans
      (Real.rpow_le_rpow (PaceR.positive R b).le top hε.le)
  have hreg := hB β (by linarith only [grown,top,le_max_left B K]) c charge
  have hhard := hK β (by linarith only [grown,top,le_max_right B K]) c charge
  constructor
  · change 4*(c*(18*((2:ℝ)^r*((Real.sqrt β)⁻¹)^r))) ≤ ((Real.sqrt β)⁻¹)^t
    calc
      _ = (72*(2:ℝ)^r)*c*((Real.sqrt β)⁻¹)^r := by ring
      _ ≤ _ := hreg
  · simpa only [g,Coat.gStep,Real.rpow_natCast,mul_pow,mul_assoc,mul_left_comm,mul_comm] using hhard

end YM.Integration.WilsonPhysicalMarkedDefect

