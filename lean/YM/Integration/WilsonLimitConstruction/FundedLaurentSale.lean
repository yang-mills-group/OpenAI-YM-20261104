import YM.Integration.WilsonLimitConstruction.FundedLaurentRadius

/-! One positive radius for the complete earned finite marked portfolio.
The same investment pays the bare, intermediate and running couplings. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedLaurentSale
open Finset Function Lattice Wilson RG Precision Marker RG3.Script.Picnic
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped BigOperators Classical

variable {B : Type*} [Fintype B] (cash : B→ℝ) (room : ℝ)

def share : ℝ := min 1 (room/(1 + ∑b,|cash b|))

private theorem total_nn : 0 ≤ ∑b,|cash b| := Finset.sum_nonneg fun _ _=>abs_nonneg _

theorem positive (hr : 0<room) : 0<share cash room :=
  lt_min zero_lt_one (div_pos hr (by linarith [total_nn cash]))

theorem floor (hr : 0<room) {L : ℝ} (paid : ∑b,|cash b| ≤ L) :
    min 1 (room/(1+L)) ≤ share cash room := by
  apply min_le_min_left
  exact div_le_div_of_nonneg_left hr.le (by linarith [total_nn cash]) (by linarith)

theorem balance (hr : 0<room) : share cash room*(∑b,|cash b|) ≤ room := by
  have q := (le_div_iff₀ (show 0<1 + ∑b,|cash b| by linarith [total_nn cash])).1
    (min_le_right 1 (room/(1 + ∑b,|cash b|)))
  change share cash room*(1 + ∑b,|cash b|) ≤ room at q
  nlinarith [positive cash room hr]

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
    (F : AnalyticInput J A d) (g gain : ℝ) (k : V→ℕ) (hg : 0<g) (ha : 0<gain)
    (hr : 0<room)

def funded : AnalyticInput J A d :=
  FundedLaurentRadius.funded F g gain k (fun _=>share cash room) hg ha (fun _=>positive cash room hr)

local notation "F₀" => funded cash room F g gain k hg ha hr
local notation "w₀" => fun v => (F₀).outputRadii v/F.kernelCosts v

omit [Fintype V] in
private theorem annulus (positiveG : 0<g) {z : ℝ} (hz : g ≤ z) (hz1 : z ≤ 1) (s : Γ.Mode)
    (i j : ℕ) (law : j ≤ i + ∑v∈s.val,k v) :
    ‖(z:ℂ)^((i:ℤ)-(j:ℤ))‖ ≤ (g^(∑v∈s.val,k v))⁻¹ := by
  have hpos := positiveG.trans_le hz
  rw [norm_zpow,Complex.norm_real,Real.norm_of_nonneg hpos.le]
  calc z^((i:ℤ)-j) ≤ z^(-(↑(∑v∈s.val,k v):ℤ)) :=
         zpow_le_zpow_right_of_le_one₀ hpos hz1 (by omega)
       _=(z^(∑v∈s.val,k v))⁻¹ := by rw [zpow_neg,zpow_natCast]
       _ ≤ _ := (inv_le_inv₀ (pow_pos hpos _) (pow_pos positiveG _)).2 (pow_le_pow_left₀ positiveG.le hz _)

theorem token {z : ℝ} (hz : g ≤ z) (hz1 : z ≤ 1) (s : Γ.Mode) (marked : s.val.Nonempty)
    (i j : ℕ) (law : j ≤ i + ∑v∈s.val,k v) :
    Poly.toll (w₀) s*‖(z:ℂ)^((i:ℤ)-(j:ℤ))‖*gain^s.val.card ≤ share cash room := by
  have hw (v) : 0<(w₀) v :=
    div_pos ((F₀).output_radius_positive v) (F.kernel_positive v)
  have amount := FundedLaurentRadius.word F g gain k (fun _=>share cash room) hg ha
    (fun _=>positive cash room hr) s
  calc Poly.toll (w₀) s*‖(z:ℂ)^((i:ℤ)-(j:ℤ))‖*gain^s.val.card ≤ 
           Poly.toll (w₀) s*(g^(∑v∈s.val,k v))⁻¹*gain^s.val.card :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
             (annulus g k hg hz hz1 s i j law) (Poly.worth hw s).le) (pow_nonneg ha.le _)
       _ ≤ Poly.toll (fun _=>share cash room) s := amount
       _ = share cash room ^ s.val.card := by simp [Poly.toll]
       _ ≤ share cash room ^ 1 := pow_le_pow_of_le_one (positive cash room hr).le
         (min_le_left _ _) (Finset.one_le_card.mpr marked)
       _ = share cash room := pow_one _

theorem portfolio {z : ℝ} (hz : g ≤ z) (hz1 : z ≤ 1) (mode : B→Γ.Mode)
    (marked : ∀b,(mode b).val.Nonempty) (i j : B→ℕ)
    (law : ∀b,j b ≤ i b + ∑v∈(mode b).val,k v) :
    ∑b,Poly.toll (w₀) (mode b)*‖(z:ℂ)^((i b:ℤ)-(j b:ℤ))‖*
      gain^(mode b).val.card*cash b ≤ room := by
  have hw (v) : 0<(w₀) v := div_pos ((F₀).output_radius_positive v) (F.kernel_positive v)
  calc _ ≤ ∑b,share cash room*|cash b| := by
          apply Finset.sum_le_sum
          intro b _
          have pos := mul_nonneg (mul_nonneg (Poly.worth hw (mode b)).le (norm_nonneg ((z:ℂ)^((i b:ℤ)-(j b:ℤ)))))
            (pow_nonneg ha.le (mode b).val.card)
          calc _ ≤ Poly.toll (w₀) (mode b)*‖(z:ℂ)^((i b:ℤ)-(j b:ℤ))‖*
                gain^(mode b).val.card*|cash b| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) pos
               _ ≤ _ := mul_le_mul_of_nonneg_right
                 (token cash room F g gain k hg ha hr hz hz1 (mode b) (marked b) (i b) (j b) (law b))
                 (abs_nonneg _)
       _=share cash room*(∑b,|cash b|) := (Finset.mul_sum ..).symm
       _ ≤ room := balance cash room hr

end YM.Integration.WilsonLimitConstruction.FundedLaurentSale
end
