import YM.Integration.WilsonOriginalGaussianAngularWallet
import YM.Integration.WilsonVacuumPreResetTorusDepositedMass

/-! A field evaluation of the complete incoming vacuum at a fixed heat order.
All rooted fees precede the ultraviolet cutoff and the periodic side. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalGaussianDatedVacuum
open Function Filter Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Blue WilsonCoeffUV.Fk WilsonCoeffUV.Wheel WilsonCoeffUV.Cosmos
open Next.Foundations Comparison.RG02 Next.SectorChange AllOrder AllOrder.Ker AllOrder.Floe
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusGrade
open WilsonVacuumPreResetTorusDeposit WilsonVacuumPreResetDatedDeposit
open WilsonVacuumPreResetMeasuredCoin FVA1Physical.TwoReset Primitives.TwoWave.RealSlice
open scoped BigOperators Classical Topology
variable {G:Gauge}

def size {n:Side}(x y:rule (Coarse G) n):ℝ:=
  (1+(Fintype.card (Woods G n):ℝ))*(1+max ‖x‖ ‖y‖)

theorem evaluated_price {n:Side}(P:PChart G n)(finite:shellK 2 P){t h:ℕ}
    (limit:t+2≤h){B:ℝ}(nn:0≤B)(entries:∀l<t+2,∀v,|P t (l+1) v|≤B)
    (x y:rule (Coarse G) n):|evaluated P t x-evaluated P t y|≤(2*h*B)*size x y^h:=by
  have high:1≤ size x y:=by
    unfold size
    have nc:(0:ℝ)≤Fintype.card (Woods G n):=Nat.cast_nonneg _
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by have:=norm_nonneg x; have:=le_max_left ‖x‖ ‖y‖;linarith)
  have one(l:ℕ)(hl:l<t+2)(z:rule (Coarse G) n)(hz:‖z‖≤ max ‖x‖ ‖y‖):
      |MvPolynomial.eval z (Blue.paint (l+1) (P t (l+1)))|≤B*size x y^h:=by
    apply (WilsonOriginalGaussianAngularWallet.single _ (entries l hl) z).trans
    apply mul_le_mul_of_nonneg_left _ nn
    apply (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) _ (l+1)).trans
    · exact pow_le_pow_right₀ high (by omega)
    · exact mul_le_mul (by linarith : (Fintype.card (Woods G n):ℝ)≤1+Fintype.card (Woods G n))
        (by linarith : ‖z‖≤1+max ‖x‖ ‖y‖) (norm_nonneg _) (by positivity)
  rw [positive P finite]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _≤∑ _l∈range (t+2),2*(B*size x y^h):=by
      apply sum_le_sum
      intro l hl
      have bx:=one l (mem_range.mp hl) x (le_max_left _ _)
      have bys:=one l (mem_range.mp hl) y (le_max_right _ _)
      exact (abs_sub _ _).trans (by linarith)
    _=(t+2:ℕ)*(2*(B*size x y^h)):=by simp
    _≤(h:ℝ)*(2*(B*size x y^h)):=mul_le_mul_of_nonneg_right (by exact_mod_cast limit) (by positivity)
    _=_:=by ring

variable (R:Run G)
theorem receipt {N j e:ℕ}{Z:SeriesA G}{σ D B:ℝ}(sold:Issued R N j e Z σ D)(nn:0≤B)
    (bill:∀t≤e+2,∀l≤e+4,∀n:Side,∀v,|lagoon (actionW R.family.path.levels R.metals.O N j t (l+1)) n v|≤B)
    {t:ℕ}(ht:t≤e+2)(n:Side)(x y:rule (Coarse G) n):
    |massJets R N j e (bank Z) t n x-massJets R N j e (bank Z) t n y|
      ≤(2*(e+4:ℕ)*B)*size x y^(e+4):=by
  let K:=R.alloy.B.kin.path N j
  let A:=(R.family.path.levels.params j).clip
  have reada(z:rule (Coarse G) n):massJets R N j e (bank Z) t n z=
      evaluated (front K A n+sands Z n) t z:=
    WilsonVacuumPreResetTorusDepositedMass.original K A Z sold.positive sold.purchase sold.lower ht z
  rw [reada x,reada y]
  have frontK:shellK 2 (front K A n):=by
    apply shell_sum (sprig_count _ 2)
    exact fun i r h=>sprig_count _ 0 i r (by omega)
  apply evaluated_price _ (shell_sum frontK (sand_span Z n)) (by omega) nn
  intro l hl v
  rw [sold.periodic t (by omega) n l]
  exact bill t ht l (by omega) n v

end YM.Integration.WilsonOriginalGaussianDatedVacuum
end
