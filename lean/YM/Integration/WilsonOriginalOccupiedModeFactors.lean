import YM.Integration.WilsonOriginalOccupiedIncidence

/-! Isolate the original numerical source salary on each actually occupied label. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedModeFactors
open Filter Finset Marker QuadraticLocal.Advent PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G)(simple:G.Simple)
local notation "H" i:max => R.alloy.B.a.clock.hatBeta i

include simple in
theorem original (n u v:ℕ):∀ᶠi:ℕ in atTop,
    ∀{V:Type} [DecidableEq V] {J:Marker.Census V} (s:J.Mode), s.val.card ≤ n →
    ∀(w:V → ℝ), (∀j,0<w j) → ∀{D:ℝ}(S:V → ℝ), 0 ≤ D → D ≤ 10*H (i+1) → (∀j,0 < S j) →
    (∀j,(w j)⁻¹ ≤ S j*(H (i+1)+(2:ℝ)^u*(H (i+1))^v)) →
      D^s.val.card ≤ (H i)^((v+3)*n)*(Poly.toll S s*Poly.toll w s):=by
  filter_upwards [WilsonOriginalOccupiedIncidence.original R simple n 0 u v] with
    i fare V dec J s load w wp D S dp dm sp wpay
  let W:V → ℝ:=fun j=>S j*w j
  let T:=H (i+1)+(2:ℝ)^u*(H (i+1))^v
  have roof:∀j,(W j)⁻¹ ≤ 1*T:=by
    intro j
    change (S j*w j)⁻¹ ≤ 1*T
    rw [mul_inv,one_mul]
    calc (S j)⁻¹*(w j)⁻¹ ≤ (S j)⁻¹*(S j*T):=mul_le_mul_of_nonneg_left (wpay j) (inv_nonneg.mpr (sp j).le)
         _=T:=by rw [←mul_assoc,inv_mul_cancel₀ (sp j).ne',one_mul]
  have wallet:=fare s load W (fun j=>mul_pos (sp j) (wp j)) dp dm zero_le_one (by simp) roof
  simpa only [Nat.zero_add,W,Poly.toll,prod_mul_distrib,prod_const] using wallet

end YM.Integration.WilsonOriginalOccupiedModeFactors
