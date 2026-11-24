import YM.Integration.FVA1Physical.Wilson.PurchasedReadout

/-! Normalize the new forest numerator by its own empty reading. This replaces
the old partition function by a controlled, strictly positive new denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum Pressure
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology
variable {G : Gauge}

def forestMass (A : Mosaic.Issue G) (J : Voice G) (x : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (B : Positions (Primary A.f G) → ℝ) (φ : Config G A.f → ℝ) : ℝ :=
  let X := boxX x b
  let Y := boxY x b
  let V := represent (tint G (Exterior.Body 1 A.c) z)
  let μ := vest (priced A.F A.v A.pre.clip A.pre.path) z
  let copy := chambers A.F Y J V μ
  let area := hotel A.F X Y J V μ (pillow x) (room x)
  let r := woolModel A.F X J A.pre Y A.v V μ (pillow x) (room x)
  let τ := fun U=>B (chartLog A.fClock (copy U))
  ∫ θ : IV A.F (board A.F X) G, A.S.push A.pre.beta (fun U=>Rota.ghat r θ φ area U *
    (A.pre.eval (twirl A.F (board A.F X) θ U)*Real.exp (τ U-τ (twirl A.F (board A.F X) θ U)))) V
    ∂fence A.F (board A.F X) G

variable (A : Mosaic.Issue G) (J : Voice G) (x : ℝ) (z : Positions (Primary A.c G))
variable (b : Site A.f) (B : Positions (Primary A.f G) → ℝ)
local notation "O" => represent (tint G (Exterior.Body 1 A.c) z)
local notation "Z" => A.S.push A.pre.beta A.pre.eval O
local notation "E" => MSbar.Bulk.expect A.S A.pre O
local notation "W" => forestMass A J x z b B

lemma forestTicket_eq (φ : Config G A.f → ℝ) : forestTicket A J x z b B φ=W φ/Z := by
  unfold forestTicket forestMass
  exact integral_div _ _

private lemma stable_ratio {l a v ε : ℝ} (mass : |l-1| ≤ ε) (price : |a-v| ≤ ε)
    (bound : |v| ≤ 1) (cap : ε ≤ 1/2) : 1/2 ≤ l ∧ |a/l-v| ≤ 4*ε := by
  have low : 1/2 ≤ l := by linarith only [(abs_le.mp mass).1,cap]
  have hl : 0<l := lt_of_lt_of_le (by norm_num : 0<(1/2:ℝ)) low
  have hε := (abs_nonneg _).trans mass
  refine ⟨low,?_⟩
  rw [div_sub' hl.ne',abs_div,abs_of_pos hl,div_le_iff₀ hl]
  have cost : |(a-v)-v*(l-1)| ≤ ε+ε := (abs_sub (a-v) (v*(l-1))).trans
    (add_le_add price ((abs_mul v (l-1)).trans_le ((mul_le_mul bound mass (abs_nonneg _) zero_le_one).trans_eq (one_mul ε))))
  have id : (a-v)-v*(l-1) = a-l*v := by ring
  rw [id] at cost
  exact cost.trans (by nlinarith only [mul_le_mul_of_nonneg_left low hε])

/-- The weighted forest has its own stable positive partition function; it can serve
as a step kernel without access to the value of the physical partition function.
Both readings evaluate the same independent Wilson bank and the same forest. -/
theorem forest_normalize {σ C δ Λ w ε : ℝ} (adm : Admitted O A.pre A.S σ C δ Λ w) (cap : ε ≤ 1/2)
    (price : ∀ φ : Config G A.f → ℝ, GaugeLocal A.S (youth A.F (boxY x b)) φ → 0 ≤ φ →
      (∀ U, φ U ≤ 1) → |forestTicket A J x z b B φ-E φ| ≤ ε) :
    Z/2 ≤ W 1 ∧ 0 < W 1 ∧ ∀ φ : Config G A.f → ℝ, GaugeLocal A.S (youth A.F (boxY x b)) φ →
      0 ≤ φ → (∀ U, φ U ≤ 1) → |W φ / W 1 - E φ| ≤ 4*ε := by
  let Y := youth A.F (boxY x b)
  have unit : GaugeLocal A.S Y (1 : Config G A.f → ℝ) := ⟨Envelope.const 1,fun _ _ _=> rfl,fun _ _ _=> rfl⟩
  have blank := price 1 unit (fun _=>zero_le_one) (fun _=>le_rfl)
  have one : E 1=1 := e_const O adm 1
  rw [one,forestTicket_eq] at blank
  have hZ := adm.mass
  have lb : 1/2 ≤ W 1/Z := by linarith only [(abs_le.mp blank).1,cap]
  have floor : Z/2 ≤ W 1 := by simpa only [one_div_mul_eq_div] using (le_div_iff₀ hZ).mp lb
  refine ⟨floor,(half_pos hZ).trans_le floor,?_⟩
  intro φ loc posφ bφ
  have real₀ := (nn O adm loc.currency (Envelope.const 0) posφ)
  have real₁ := (nn O adm (Envelope.const 1) loc.currency bφ)
  rw [e_const O adm 0] at real₀
  rw [e_const O adm 1] at real₁
  have pr := price φ loc posφ bφ
  rw [forestTicket_eq] at pr
  have res := (stable_ratio blank pr ((abs_of_nonneg real₀).trans_le real₁) cap).2
  rwa [div_div_div_cancel_right₀ hZ.ne'] at res
end YM.Integration.FVA1Physical.Wilson
