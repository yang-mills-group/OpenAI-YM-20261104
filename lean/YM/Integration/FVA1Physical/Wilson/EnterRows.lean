import YM.Integration.FVA1Physical.Wilson.CoarseRows
import YM.Integration.FVA1Physical.Wilson.CoarseLand

/-! Plant a physical polynomial emitted onto the coarse torus in the full
incoming forest variables of the following block. Its rooted derivative and
degree budgets survive the installation, uniformly over all forests and tori. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open Push Push.Uniform MSbar.Tramp Bloch Laurent
open scoped Classical Topology BigOperators
variable {G:Gauge}

def enterRows (A:Issue G) (src:Nesting G A.f) : PowerSeries (Pot (Joint A.F G)) :=
  PowerSeries.map (rail (taps A.F G)).toRingHom src

def enterFee (G:Gauge) (s:ℕ) := Parma.goalK G (Geneva.spire 1 s) 1

theorem enter_vault (A:Issue G) (s h i:ℕ) {a C:ℝ} (ha:0≤a) (W:Finset (Site A.f))
    (src:Nesting G A.f) (z:View (Joint A.F G))
    (input:Vault (Measuring.chart A.f G) W a s h (taps A.F G *ᵥ z) (PowerSeries.coeff i src) C) :
    Vault (address A.F G) W a s h z (PowerSeries.coeff i (enterRows A src)) ((enterFee G s)^h*C) ∧
    (PowerSeries.coeff i (enterRows A src)).totalDegree ≤ (PowerSeries.coeff i src).totalDegree := by
  simp only [enterRows,PowerSeries.coeff_map]
  exact ⟨rooted_vault_pullback _ _ _ s h ha (stamp_all_periods A.F ha s) z W _ input,
    Rolling.clearD _ _⟩

theorem enter_read (A:Issue G) (src:Nesting G A.f) (z:View (Joint A.F G)) (i:ℕ) :
    MvPolynomial.eval z (PowerSeries.coeff i (enterRows A src)) =
      MvPolynomial.eval (taps A.F G *ᵥ z) (PowerSeries.coeff i src) := by
  simp only [enterRows,PowerSeries.coeff_map]
  exact congr_fun (Rolling.clearL _ _) _

end YM.Integration.FVA1Physical.Wilson
