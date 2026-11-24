import YM.Integration.FVA1Physical.Round2.FieldSparseComparison
import YM.MSbar.Cypress.Vibe

/-! Lower the comparison to the requested physical order after interpolation.
The discarded Wilson terms are priced in the rooted norm on that same chart. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Mosaic MSbar.CrossH MSbar.Rolling MSbar.Bakery MSbar.Bakery.Film
open MSbar.Whisk MSbar.Heath MSbar.Heath.Stock MSbar.Bulk MSbar.Kelvin MSbar.Cacao
open RGComparison.Core16 RGComparison.Core16.Spool Push.Uniform
open YM.Integration.FVA1Physical.Wilson AnalyticBridge.SectorAffine.Offset
open scoped Classical Topology BigOperators ContDiff

theorem vault_word {σ:Type} [Fintype σ] [DecidableEq σ] {n:Side} (site:σ→Site n) (W:Finset (Site n))
    {a B:ℝ} (ha:0≤a) (s k:ℕ) (z:Positions σ) (P:Pot σ) (l:List σ) (hl:l.length≤k)
    (rows:Vault site W a s k z P B) : |buoy (clue P) z l| ≤ B := by
  have fee:=vaulted_operator site W ha s k z P rows
  rw [CrossH.chain (clue P) l k z fee.smooth hl,←Real.norm_eq_abs]
  exact (ContinuousMultilinearMap.le_opNorm ..).trans (by simpa only [norm_bolt,prod_const_one,mul_one] using fee.pay l.length hl)

theorem compared_truncation {σ:Type} [Fintype σ] [DecidableEq σ] {n:Side} (site:σ→Site n)
    (W:Finset (Site n)) (s k p d:ℕ) (z:Positions σ) (l:List σ) (hl:l.length≤k)
    (f:Positions σ→ℝ) (smooth:ContDiffAt ℝ k f z) (hi lo:PowerSeries (Pot σ))
    {g α H ε:ℝ} (hg:0≤g) (unit:g≤1) (ha:0≤α) (same:Lap p hi lo)
    (rows : ∀ i : ℕ, p < i → i≤p+d → Vault site W α s k z (PowerSeries.coeff i hi) H)
    (high:|buoy (f-clue (renderedPolynomial hi (p+d) g)) z l| ≤ ε) :
    |buoy (f-clue (renderedPolynomial lo p g)) z l| ≤ ε + (d:ℝ)*g^(p+1)*H := by
  let A:=renderedPolynomial hi (p+d) g
  let B:=renderedPolynomial lo p g
  have tails:=represented_truncation site W z s k p d hi lo hg unit same rows
  have tail:=vault_word site W ha s k z (A-B) l hl tails
  have eval_sub:clue (A-B)=clue A-clue B:=funext fun x=>_root_.map_sub (MvPolynomial.eval x) A B
  rw [eval_sub,Cypress.remove k l z (clue A) (clue B) (helm A k).contDiffAt (helm B k).contDiffAt hl] at tail
  change |buoy (f-clue A) z l|≤ε at high
  rw [Cypress.remove k l z f (clue A) smooth (helm A k).contDiffAt hl] at high
  change |buoy (f-clue B) z l| ≤ _
  rw [Cypress.remove k l z f (clue B) smooth (helm B k).contDiffAt hl]
  exact (abs_sub_le _ (buoy (clue A) z l) _).trans (add_le_add high tail)

end YM.Integration.FVA1Physical.Round2.Curvature
