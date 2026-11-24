import YM.Integration.WilsonCapturedPrimaryWeakTrialRadial
import YM.Integration.WilsonOriginalClockFacePosterior

/-! The spring sees only the cropped links of a native radial probe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRadialRaySpring
open Finset Filter Labels Lattice Wilson RG Source Push.Local Push.AbsoluteSums.Animals
open Planned.AtomRegular Next.Foundations WilsonCapturedPrimaryAngles
open WilsonCapturedPrimaryPotential Stationary Comparison.RG02
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{d:ℕ}

def fare (A:Hol G)(p:Probe G d):ℝ:=1+|panelFee A p|

private theorem active_card (o:Site n)(r:ℕ):
    ((active o r).card:ℝ) ≤ 64*(1+(r:ℝ))^4:=by
  have h:active o r⊆ ((neighbors r o) ×ˢ (univ:Finset Axis)):=by
    intro e he
    exact mem_product.mpr ⟨(neighbors_mem r o _).mpr ((separation_comm o e.1) ▸ (mem_filter.mp he).2),mem_univ _⟩
  have hc: (active o r).card ≤ (r+r+1)^4*4 :=by
    apply (card_le_card h).trans
    rw [card_product]
    exact Nat.mul_le_mul (neighbors_card ..) (by decide)
  calc _ ≤ ((r+r+1:ℕ):ℝ)^4*4:=by exact_mod_cast hc
       _ ≤ (2*(1+(r:ℝ)))^4*4:=by push_cast;gcongr;linarith
       _ = _ := by ring

theorem bound (A:Hol G)(b:BudgetPoint)(o:Site n)(r:ℕ)(p:Probe G d)
    {t g β C δ:ℝ}(gp:0<g)(unit:|t|≤1)(bp:0≤β)(balance:β*|t|≤1)
    (cp:0≤C)(lip:∀ v:G.Color,‖v‖ ≤ δ → G.chord (G.lieExp v) ≤ C*‖v‖)
    (short:b.threshold*fare A p*(1+(r:ℝ))^(d+6) ≤ δ):
    let V:=Integral.sample g (Stationary.arm G n 1 (lifted A b o r p g t))
    β*(∑ e:Link n,G.chord (V e)) ≤ 64*C*(b.threshold*fare A p*(1+(r:ℝ))^(d+6)):=by
  intro V
  let u:=1+(r:ℝ)
  have u1:1≤u:=le_add_of_nonneg_right (Nat.cast_nonneg _)
  have up:0≤u:=zero_le_one.trans u1
  have tp:0≤b.threshold:=b.threshold_pos.le
  have fn:0≤fare A p:=by unfold fare;positivity
  have wi:wallet A p r≤fare A p*u^d:=by
    change 1+panelFee A p*u^d≤(1+|panelFee A p|)*u^d
    rw [add_mul,one_mul]
    exact add_le_add (one_le_pow₀ u1) (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (zero_le_one.trans u1) _))
  let dir:=limitAmp (WilsonCapturedPrimaryRough.quadratic b) o (active o r) (angular A b o r p t)
  have idV:V=increment 1 dir:=sampled gp dir
  let localCost:=b.threshold*fare A p*u^(d+2)
  have positive:0≤localCost:=mul_nonneg (mul_nonneg b.threshold_pos.le fn) (pow_nonneg (zero_le_one.trans u1) _)
  have limited:localCost ≤ δ:=by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ u1 (show d+2≤d+6 by omega))
      (mul_nonneg b.threshold_pos.le fn)).trans short
  have loc:∀e∈active o r, ‖dir e‖≤|t| *localCost:=by
    intro e he
    have dist:separation e.1 o≤r:=(mem_filter.mp he).2
    have ww:weight (WilsonCapturedPrimaryRough.quadratic b) o e ≤ b.threshold*u^2:=by
      have h:(1:ℝ)+(separation e.1 o:ℝ)≤u:=by dsimp only [u];exact_mod_cast Nat.add_le_add_left dist 1
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h 2) b.threshold_pos.le
    have ang:‖angular A b o r p t e‖≤ |t| *(fare A p*u^d):=
      ((norm_le_pi_norm _ e).trans (size A b o r p unit)).trans (mul_le_mul_of_nonneg_left wi (abs_nonneg _))
    change ‖limitAmp _ _ _ _ e‖≤_
    rw [limit_hit he,norm_smul,Real.norm_of_nonneg (weight_pos ..).le]
    calc _ ≤ (b.threshold*u^2)*(|t| *(fare A p*u^d)):=mul_le_mul ww ang (norm_nonneg _) (by positivity)
         _ = _:=by dsimp only [localCost];rw [pow_add];ring
  have sums: ∑ e:Link n,G.chord (V e) ≤ (64*u^4)*(C*(|t| *localCost)) :=by
    calc _ = ∑e∈active o r,G.chord (V e):=by
              symm;apply sum_subset (subset_univ _)
              intro e _ he
              rw [idV]
              simp [dir,increment,limit_miss he,G.chord_one]
         _ ≤ ∑_∈active o r,C*(|t| *localCost):=by
              apply sum_le_sum;intro e he
              rw [idV]
              change G.chord (G.lieExp (dir e)*1) ≤ _
              rw [mul_one]
              exact (lip _ ((loc e he).trans ((mul_le_of_le_one_left positive unit).trans limited))).trans
                (mul_le_mul_of_nonneg_left (loc e he) cp)
         _ ≤ _:=by rw [sum_const,nsmul_eq_mul];exact mul_le_mul_of_nonneg_right (active_card o r) (by positivity)
  calc _ ≤ β*((64*u^4)*(C*(|t| *localCost))):=mul_le_mul_of_nonneg_left sums bp
       _ = (64*C*(b.threshold*fare A p*u^(d+6)))*(β*|t|):=by
         dsimp only [localCost];rw [pow_add,pow_add];ring
       _ ≤ _:=mul_le_of_le_one_right (by positivity) balance

end YM.Integration.WilsonOriginalRadialRaySpring
