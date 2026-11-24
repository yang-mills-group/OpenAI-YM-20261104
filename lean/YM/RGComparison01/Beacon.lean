import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Revenue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Tryouts

/-!
# Vacuum: keep grades and count prices *before* a threshold/log cut.

The construction's `Height.completed` pays a particular (roughly,
third-order) tail. Here exploit its underlying estimate (`Height.stable`)
**without first spending the weights**. This lets one cut to every fixed
order, and exploit actual depth and seed penalties as well as arity. This
is positive estimation, not complex-parameter variation of seeds or masks.

Unmarked. `N.markΦ` is a *price* for real jets, not a source entry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open PhysicalNext.Repeat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

namespace Beacon
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ}
    {k j n ℓ : ℕ} {χ : Chi} {H : Cash W s μ L Q o α T R}

variable (N : Captain H j C' d v Y A b r B q k χ)
local notation "gZ" => Height.grow G L s

lemma beacon_nonneg (hd : 1 ≤ gZ) (z : H.fragrances) : 0 ≤ Height.beacon H z :=
  mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hd) _) (Real.exp_nonneg _)) (Real.exp_nonneg _)
lemma jetPrice_nonneg (z : H.fragrances) (n : ℕ) : 0 ≤ N.markΦ z n := by
  have he : 0 ≤ shiftG s := by unfold shiftG; positivity
  unfold Captain.markΦ
  exact mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)

/-- Joint bill, per hit site, complete weighted derivatives. -/
theorem weighted (hd : 1 ≤ gZ) (hc : Heavy N.conduit) (n : ℕ)
    (ht : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (gZ * (Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1 / 2)
    (hp : degreePrice (radiusB s) (gZ * salary Q L μ B s j k) i ≤ 1 / 2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z => Height.beacon H z * N.markΦ z n) a
      (collars G i s j n * (gZ * salary Q L μ B s j k * (1 - 1/2)⁻¹)) := by
  intro x
  have hy := log_hit_tail _ _ _ H.testS (Height.stable N hd hc i a ht.delta ht.little ht.earned hs hp)
    (add_nonneg ht.gain ht.delta.le) 0 x
  simp only [pow_zero, mul_one] at hy
  have he : 0 ≤ shiftG s := by unfold shiftG; positivity
  have hv : 0 ≤ collars G i s j n := by
    unfold collars Reserves.polyPrice; have he := ht.delta; positivity
  have hb := budget_scale hv hy
  refine budget_mono hb (fun z => ?_) (fun z => ?_)
  · split
    next => exact mul_nonneg (mul_nonneg (beacon_nonneg hd z) (jetPrice_nonneg N z n)) (Real.exp_nonneg _)
    next => exact le_rfl
  dsimp only; split
  next hx =>
    rw [if_pos (show 0 ≤ z.fst ∧ x ∈ unionOf H.smallAt z.snd from ⟨Nat.zero_le _, hx⟩), Height.wield N]
    let c0 : ℝ := coverNumber (radiusB s) (Captain.reachability (H:=H) z)
    have hc0 : 0 ≤ c0 := Nat.cast_nonneg _
    have Hc : (1 + c0) ^ (n*j) ≤ polyPrice i (n*j) * Real.exp (i*c0) :=
      polynomial_cost ht.delta hc0 (n*j)
    change _ * ((shiftG s * (1+c0))^(n*j) * N.design z) * Real.exp (a*c0) ≤ _ * (_ * Real.exp ((a+i)*c0))
    rw [mul_pow]
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hc (pow_nonneg he _)) (N.pvc _))
        (beacon_nonneg hd z)) (Real.exp_nonneg (a*c0))) ?_
    rw [add_mul, Real.exp_add]; unfold collars; apply le_of_eq; ring
  next => exact hb.1 z

theorem recover (Sel : H.fragrances → Prop)
    {invoice pay : ℝ} (hpay : 0 < pay) (charge : ∀ z, Sel z → pay ≤ Height.beacon H z)
    (h : Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z => Height.beacon H z * N.markΦ z n) a invoice) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z => if Sel z then N.markΦ z n else 0)
      a (pay⁻¹ * invoice) := by
  intro x
  have hb := budget_scale (inv_pos.mpr hpay).le (h x)
  refine budget_mono hb (fun z => ?_) (fun z => ?_)
  · dsimp only
    split_ifs
    · exact mul_nonneg (jetPrice_nonneg N z n) (Real.exp_nonneg _)
    · rw [zero_mul]
    · exact le_rfl
  dsimp only
  split
  next hx =>
    split
    next hz =>
      rw [le_inv_mul_iff₀ hpay, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (charge z hz) (jetPrice_nonneg N z n))
        (Real.exp_nonneg _)
    next => rw [zero_mul]; simpa only [if_pos hx] using hb.1 z
  next => rw [mul_zero]

/-- `ℓ` is an *internal count order*, not the final expansion order. Include
long depth also. Incoming E may be rough; nothing put that function through
a coupling Taylor test. NB micro/warning costs with no such count, depth or
overlap (at this ℓ) are **not** discarded here. -/
def Exceptional (H : Cash W s μ L Q o α T R) (ℓ : ℕ) (z : H.fragrances) : Prop :=
  ℓ ≤ Height.degree H z ∨ 1 ≤ Height.overlap H z ∨
    (ℓ : ℝ) * Pressure.Stores.till s ≤ Height.depth H z

theorem cashout (hd : 1 ≤ gZ)
    (hseed : gZ ^ ℓ ≤ Real.exp (Q.mark L μ s))
    (hlong : gZ ^ 3 ≤ Real.exp (Q.ε * Pressure.Stores.till s)) :
    ∀ z, Exceptional H ℓ z → gZ ^ ℓ ≤ Height.beacon H z := by
  intro z hz
  have hp := one_le_pow₀ (n:=Height.degree H z) hd
  have hmark : 0 ≤ Q.mark L μ s := H.laws.acquired.marked
  have h_ov : 1 ≤ Real.exp (Q.mark L μ s * Height.overlap H z) :=
    Real.one_le_exp (mul_nonneg hmark (Nat.cast_nonneg _))
  have h_depth : 1 ≤ Real.exp (Q.ε * Height.depth H z) :=
    Real.one_le_exp (mul_nonneg Q.usable.le (sum_nonneg fun t _ => H.positive_volume _))
  rcases hz with h | h | h
  · exact (pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right (zero_le_one.trans hp) h_ov).trans
      (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hp h_ov)) h_depth))
  · exact hseed.trans ((Real.exp_monotone (le_mul_of_one_le_right hmark (show (1:ℝ) ≤ Height.overlap H z by exact_mod_cast h))).trans
      ((le_mul_of_one_le_left (zero_le_one.trans h_ov) hp).trans
        (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le hp h_ov)) h_depth)))
  have he : gZ ≤ Real.exp (Q.ε * Pressure.Stores.till s) := (le_self_pow₀ hd (by decide)).trans hlong
  refine (pow_le_pow_left₀ (zero_le_one.trans hd) he ℓ).trans (le_trans ?_
    (le_mul_of_one_le_left (zero_le_one.trans h_depth) (one_le_mul_of_one_le_of_one_le hp h_ov)))
  rw [← Real.exp_nat_mul]
  exact Real.exp_monotone (by linarith only [mul_le_mul_of_nonneg_left h Q.usable.le])
end Beacon
end YM.RGComparison01
