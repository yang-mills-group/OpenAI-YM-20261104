import YM.Integration.CommonStationaryQuotes
import YM.RG12.Burst.Cotton

/-! Purchase the exact stationary table bill before choosing the common Run.
At each stage the request covers every derivative order up to that stage,
uniformly over all later patches with the prescribed stage and block size. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CommonStationaryQuotePurchase

open Filter Lattice RG Pressure Real
open PhysicalNext.Repeat.Daisy.Charity.RG12

variable {G : Gauge}

def Caps (P : Teller G) (L : Side) (x : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ P.j → ∀ A : Patch, A.J = P.j → A.L = L →
    CommonStationaryQuotes.bill
      ((CommonStationaryQuotes.quote G P.top.width P.top.paths P.j P.bind n).tables
        P.top.clip A) ≤ x ^ ((1 : ℝ) / ((P.j : ℝ) + 1))

/-- The full bill is fixed before the hatted inverse coupling tends to infinity. -/
theorem caps_eventually (P : Teller G) (L : Side) :
    ∀ᶠ x : ℝ in atTop, Caps P L x := by
  have hsmall (n : Fin (P.j + 1)) : ∀ᶠ x : ℝ in atTop,
      ∀ A : Patch, A.J = P.j → A.L = L →
        CommonStationaryQuotes.bill
          ((CommonStationaryQuotes.quote G P.top.width P.top.paths P.j P.bind n).tables
            P.top.clip A) ≤ x ^ ((1 : ℝ) / ((P.j : ℝ) + 1)) := by
    obtain ⟨e, B, _hB, hB⟩ := CommonStationaryQuotes.bill_bound
      G P.top.width P.top.paths P.j P.bind n P.top.width_pos P.top.clip
    filter_upwards [(tendsto_rpow_atTop
      (show (0 : ℝ) < 1 / ((P.j : ℝ) + 1) by positivity)).eventually_ge_atTop
        (B * (L.val : ℝ) ^ e)] with x hx A hJ hL
    exact (hB A hJ).trans (by simpa only [hL] using hx)
  filter_upwards [eventually_all.mpr hsmall] with x hx n hn A hJ hL
  exact hx (⟨n, by omega⟩ : Fin (P.j + 1)) A hJ hL

/-- A genuine chronological request, using no new hypothesis on a selected Run. -/
def request (G : Gauge) : Decal G where
  rub P _ _ L _ _ _ _ _ x := Caps P L x
  good P _ _ := ⟨0, fun L _ _ _ _ _ _ _ _ _ => caps_eventually P L⟩

end YM.Integration.CommonStationaryQuotePurchase
