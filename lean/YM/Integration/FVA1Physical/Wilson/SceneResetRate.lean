import YM.Integration.FVA1Physical.Wilson.SceneBridge
import YM.RG01.Slack

/-! Two extra orders in the scene's coupling ratio pay for the inverse
temperature, uniformly over all physical volumes and cutoffs. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Filter RG Lattice YM.Wilson PhysicalNext.Repeat.Legato Comparison.RG02
open MSbar MSbar.Bakery MSbar.Midpoint
open scoped Classical Topology

variable {G : Gauge} (A : Run G) {p n : ℕ}

/-- The inverse-beta shift predicted by the scene on its measured coarse
coupling. The tilt is the ratio of coarse coupling to fine coupling. -/
def sceneReset (S : Scene A.family.path.levels p n) (N j : ℕ) : ℝ :=
  let β := A.family.path.β N p j
  β * (1 - (taste n (S.action j) (Heath.Stock.cue β))^2)

private theorem squared_ratio {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (Heath.Stock.cue b / Heath.Stock.cue c)^2 = c/b := by
  unfold Heath.Stock.cue
  rw [inv_div_inv,div_pow,Real.sq_sqrt hc.le,Real.sq_sqrt hb.le]

private theorem two_orders {h : ℝ} (hh : 0 < h) (r : ℕ) :
    h * Mosaic.goalP h (r+2) = Mosaic.goalP h r := by
  unfold Mosaic.goalP
  nth_rw 1 [← Real.rpow_one h]
  rw [← Real.rpow_add hh]
  congr 1
  unfold Mosaic.pawn
  push_cast
  ring

/-- The actual scene and physical inverse-temperature shifts agree with
the stated all-order error. The same scene's distance to the cofinal Wilson
kinetic detector is bounded separately by the purchased kinetic reset bill. -/
theorem scene_reset_uniform (hG : G.Simple) {u : G.ColorIndex}
    (D : Docket A.family u A.metals.O A.alloy.B.M A.alloy.B.kin) (r : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N p, k ≤ N →
      (∃ S : Scene A.family.path.levels p (r+2),
        Realized (RunFormalChain.fromRun A).kin N p k (r+2) (Lis.sun G u) S) ∧
      ∀ (S : Scene A.family.path.levels p (r+2)),
        Realized (RunFormalChain.fromRun A).kin N p k (r+2) (Lis.sun G u) S →
        ∀ j, k ≤ j → j < N →
          let h := A.family.path.levels.clock.hatBeta j
          |sceneReset A S N j - measuredReset A N j p| ≤ 14 * Mosaic.goalP h r ∧
          |sceneReset A S N j - (RunFormalChain.fromRun A).kin.alpha N j| ≤
            14 * Mosaic.goalP h r + resetPrice A j := by
  let a := A.family.path.levels
  obtain ⟨k₀,base⟩ := eventually_atTop.mp (RG01.Physical.nextHat hG a)
  filter_upwards [D.purse 6 (r+2) (r+4) le_rfl (by omega) (by omega),
    eventually_ge_atTop k₀] with k paid h₀
  intro N p hk
  obtain ⟨existsS,budgets⟩ := paid N p hk
  refine ⟨existsS,?_⟩
  intro S hS j hj hjN
  let H := a.clock.hatBeta j
  let b := A.family.path.β N p j
  let c := A.family.path.β N p (j+1)
  let t := Heath.Stock.cue b / Heath.Stock.cue c
  let v := taste (r+2) (S.action j) (Heath.Stock.cue b)
  let ε := Mosaic.goalP H (r+2)
  have hH : 1 ≤ H := (a.fits.delayed j).le
  have bb := (A.makes.wilson.represents N p j hjN.le).band
  have bc := (A.makes.wilson.represents N p (j+1) hjN).band
  have hb : 0 < b := Local.RealStep.actual_positive A.family N p j A.makes hjN.le
  have hc : 0 < c := Local.RealStep.actual_positive A.family N p (j+1) A.makes hjN
  have close : |t-v| ≤ ε := ((budgets S hS).2.1 j hj hjN)
  have next : a.clock.hatBeta (j+1) ≤ 2*H := base j (h₀.trans hj)
  have blow : H/2 ≤ b := bb.1
  have cupp : c ≤ 2*a.clock.hatBeta (j+1) := bc.2
  have bhigh : b ≤ 2*H := bb.2
  have zero : 0 ≤ ε := Real.rpow_nonneg (zero_le_one.trans hH) _
  have small : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hH (by
    unfold Mosaic.pawn
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by norm_num))
  have ident : t^2 = c/b := squared_ratio hb hc
  have tb : t^2 ≤ 8 := ident ▸ (div_le_iff₀ hb).2 (by linarith [cupp,next,blow])
  have ts : |t| ≤ 3 := abs_le.2 ⟨by nlinarith [sq_nonneg (t+3)],by nlinarith [sq_nonneg (t-3)]⟩
  have other : |t+v| ≤ 7 := by
    calc
      |t+v| = |(2*t)-(t-v)| := by ring_nf
      _ ≤ |2*t| + |t-v| := abs_sub _ _
      _ ≤ 7 := by rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith
  have orig : measuredReset A N j p = b*(1-t^2) := by
    change b-c = b*(1-t^2)
    rw [ident]
    field_simp
  have bill : |sceneReset A S N j - measuredReset A N j p| ≤ 14*Mosaic.goalP H r := by
    rw [orig]
    change |b*(1-v^2) - b*(1-t^2)| ≤ _
    rw [show b*(1-v^2) - b*(1-t^2) = b*((t-v)*(t+v)) by ring,
      abs_mul,abs_mul,abs_of_pos hb]
    calc
      b*(|t-v| * |t+v|) ≤ (2*H)*(ε*7) :=
        mul_le_mul bhigh (mul_le_mul close other (abs_nonneg _) zero) (by positivity) (by linarith)
      _ = 14*Mosaic.goalP H r := by rw [show (2*H)*(ε*7) = 14*(H*ε) by ring, two_orders (zero_lt_one.trans_le hH)]
  refine ⟨bill,?_⟩
  have otherPrice := measured_reset_price A hG (p:=p) hjN
  rw [abs_sub_comm] at otherPrice
  exact (abs_sub_le (sceneReset A S N j) (measuredReset A N j p) _).trans (add_le_add bill otherPrice)

end YM.Integration.FVA1Physical.Wilson
