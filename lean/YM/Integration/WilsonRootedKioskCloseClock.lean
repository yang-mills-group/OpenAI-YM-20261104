import YM.QuadraticLocal.Close
import YM.Integration.WilsonRootedKioskHardWeights

/-! One original close window has a common enlarged marked radius. All its genuine hard
quotes retain their dated forced divisors, independently of the finest cutoff and period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRootedKioskCloseClock
open Function Filter Finset Lattice Wilson RG Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open ConnectedActivityE6 Extra.Histories Integration.LocalComparison
open AllOrder.Floe AllOrder.Floe.Step AnalyticBridge VerifiedReset Push.PriceCompiler
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "Φ" => R.alloy.B.a.clock.hatBeta

/-- The enlargement is fixed before either regulator. Its factor at an occupied set
of cardinality h is exactly enlargement^h. -/
def enlargement (b q:ℕ):ℝ := (Φ b)^(q+2)

include simple
private theorem rising : Tendsto Φ atTop atTop :=
  tendsto_atTop_add_const_left _ _ (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))

theorem late (l:ℕ) (Q:ℝ) (start:ℕ):
    ∀ᶠ b:ℕ in atTop,∀ m ≤ b,PaceR.Close R l Q m b → start ≤ m := by
  filter_upwards [PaceR.covers_hat R simple l Q,
    (rising R simple).eventually_gt_atTop (2*Φ start)] with b cover hot m before closed
  by_contra! earlier
  have lo:=cover m m le_rfl before closed
  have hi:=PaceR.clock_mono R simple earlier.le
  linarith only [lo,hi,hot]

theorem original (l h q:ℕ) {Q ε:ℝ} (nonnegative:0 ≤ Q) (positive:0 < ε)
    (way:WayStation R.kit):
    ∀ᶠ b:ℕ in atTop,let L:=enlargement R b q
      1 ≤ L ∧ ∀ m ≤ b,PaceR.Close R l Q m b → 
      h ≤ R.alloy.B.a.clock.J m ∧ 
      (∀ (i:ℕ), m ≤ i → i ≤ b → 1 ≤ L/PaceR.roof R i b) ∧ 
      ∀ (i:ℕ), m ≤ i → i < b → ∀ (N per:ℕ), b ≤ N → 
      let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
      (L/PaceR.roof R i b)⁻¹ ≤ ε*g^q ∧ 
      ∀ (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (H:(s:ℕ) → Rep G (R.family.side s per))
        (start k:ℕ), start ≤ m → 
        Concourse R.alloy R.kit R.T π Γ start N per k H → 
        quoteR R (H (i+1)).beta i ≤ ε*g^q*forcedDivisor R.family i := by
  filter_upwards [PaceR.gives R simple l 1 Q nonnegative 1 zero_lt_one,
    PaceR.covers_hat R simple l Q,PaceR.on_tail R simple l Q (max h (q+1)),
    (rising R simple).eventually_ge_atTop (2*(max 2 ε⁻¹))]
    with b cap cover deep hot
  let x:=Φ b
  have large:2*(max 2 ε⁻¹) ≤ x:=hot
  have x2:2 ≤ x:=by linarith only [large,le_max_left (2:ℝ) ε⁻¹]
  have x1:1 ≤ x:=by linarith only [x2]
  have xp:0 < x:=zero_lt_one.trans_le x1
  have cheap:x⁻¹ ≤ ε:=by
    have lo:ε⁻¹ ≤ x:=by linarith only [large,le_max_right (2:ℝ) ε⁻¹,inv_pos.mpr positive]
    exact (inv_anti₀ (inv_pos.mpr positive) lo).trans_eq (inv_inv ε)
  let L:=enlargement R b q
  have one:1 ≤ L:=one_le_pow₀ x1
  have lp:0 < L:=zero_lt_one.trans_le one
  have wide:x ≤ L:=by
    change x ≤ x^(q+2)
    nth_rw 1 [←pow_one x]
    exact pow_le_pow_right₀ x1 (by omega)
  refine ⟨one,?_⟩
  intro m before closed
  have stage:=deep m before closed
  have shell (i:ℕ) (hi:m ≤ i) (endp:i ≤ b): PaceR.roof R i b ≤ x:=by
    simpa only [pow_one,Real.rpow_one] using cap m i hi endp closed
  refine ⟨(le_max_left h (q+1)).trans stage,fun i hi endp=>
    (one_le_div (zero_lt_one.trans_le (PaceR.roof_ge R i b))).mpr ((shell i hi endp).trans wide),?_⟩
  intro i hi endp N per top g
  let y:=Φ (i+1)
  let β:=(R.family.path.rep N per (i+1)).beta
  have yx:y ≤ x:=PaceR.clock_mono R simple endp
  have near:x/2 ≤ y:=cover (i+1) m (Nat.le_succ_of_le hi) endp closed
  have y2:2 ≤ y:=by linarith only [near,large,le_max_left (2:ℝ) ε⁻¹]
  have yp:0 < y:=by linarith only [y2]
  have beneficiary:y⁻¹ ≤ ε:=by
    have small:ε⁻¹ ≤ y:=by linarith only [near,large,le_max_right (2:ℝ) ε⁻¹]
    exact (inv_anti₀ (inv_pos.mpr positive) small).trans_eq (inv_inv ε)
  have live : i+1 ≤ N:=(show i+1 ≤ b from endp).trans top
  obtain ⟨low,high⟩:=(R.makes.wilson.represents N per (i+1) live).band
  change y/2 ≤ β at low
  change β ≤ 2*y at high
  have beta:0 < β:=by linarith only [low,yp]
  have xpays:=WilsonRootedKioskHardWeights.temperature x2 beta (high.trans (by linarith only [yx])) q
  have ypays:=WilsonRootedKioskHardWeights.temperature y2 beta high q
  rw [Real.rpow_neg xp.le,Real.rpow_natCast] at xpays
  rw [Real.rpow_neg yp.le,Real.rpow_natCast] at ypays
  constructor
  · calc
      _ = PaceR.roof R i b/L:=inv_div _ _
      _ ≤ x/L:=div_le_div_of_nonneg_right (shell i hi endp.le) lp.le
      _ = x⁻¹*(x^q)⁻¹:=by
        change x/x^(q+2)=_
        rw [pow_add,pow_two];field_simp
      _ ≤ ε*g^q:=mul_le_mul cheap xpays (inv_nonneg.mpr (pow_nonneg xp.le _)) positive.le
  · intro π Γ H first k start course
    have jq:q+1 ≤ R.alloy.B.a.clock.J i:=
      ((le_max_right h (q+1)).trans stage).trans (R.alloy.B.a.fits.mono hi)
    have funded:=force_bill R way π Γ H course (start.trans hi) (Nat.lt_of_succ_le live) jq
    change quoteR R (H (i+1)).beta i ≤ y^(-((q+1:ℕ):ℝ))*forcedDivisor R.family i at funded
    apply funded.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [Real.rpow_neg yp.le,Real.rpow_natCast,pow_succ,mul_inv_rev]
    exact mul_le_mul beneficiary ypays (inv_nonneg.mpr (pow_nonneg yp.le _)) positive.le

end YM.Integration.WilsonRootedKioskCloseClock
