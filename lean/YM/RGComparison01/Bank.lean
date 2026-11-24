import YM.RGComparison01.Beacon
import YM.RGComparison01.Sail

/-!
# Log tail with additional growth/profile tickets.

 No assumption of price transfer between Captains. Extended bills are
 existential on the *same* sector/workspace and coefficients estimate.
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

open Height.Sail

def ups (V : ℕ → ℝ) (t : ℝ) (z : H.fragrances) : ℝ := ∏ i, ∏ v∈ (z.2 i).val,policyP V t v

def spire (V : ℕ → ℝ) (t : ℝ) (z : H.fragrances) : ℝ := ups V t z * Height.beacon H z

lemma ups_paid (V : ℕ → ℝ) (t : ℝ) (ht : 1 ≤ t) (hV : ∀ i, 1 ≤ V i) (z : H.fragrances) :
    1 ≤ ups V t z := one_le_prod (fun _ _=> one_le_prod fun v _ => policy_ge V t ht hV v)
lemma higher (hd : 1 ≤ gZ) (V : ℕ → ℝ) (t : ℝ) (ht : 1 ≤ t) (hV : ∀ i, 1 ≤ V i) (z : H.fragrances) :
    Height.beacon H z ≤ spire V t z := le_mul_of_one_le_left (beacon_nonneg hd z) (ups_paid V t ht hV z)
lemma spire_positive (hd : 1 ≤ gZ) (V : ℕ → ℝ) (t : ℝ) (ht : 1 ≤ t) (hV : ∀ i, 1 ≤ V i) (z : H.fragrances) :
    0 ≤ spire V t z := (beacon_nonneg hd z).trans (higher hd V t ht hV z)
lemma rises (V : ℕ → ℝ) (t : ℝ) (z : H.fragrances) :
    clusters H.seam (fun u:H.ThinP=> third H V t u.val*N.stone u) z.2 = spire V t z*N.design z := by
  unfold spire; rw [mul_assoc, ← Height.wield N]; unfold third ups clusters; simp_rw [Finset.prod_mul_distrib]; ring
/-- Joint bill, per hit site, complete weighted derivatives. -/
theorem spire_weighted (hd : 1 ≤ gZ) (V : ℕ→ℝ) (t : ℝ) (ht' : 1 ≤ t) (hO : ∀ i, 1 ≤ V i)
    (hc : Worthy N.conduit V t) (n : ℕ)
    (ht : Armada Q L μ a s i B j k)
    (hs : degreePrice (radiusB s) (gZ * (Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1 / 2)
    (hp : degreePrice (radiusB s) (gZ * salary Q L μ B s j k) i ≤ 1 / 2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z => spire V t z * N.markΦ z n) a
      (collars G i s j n * (gZ * salary Q L μ B s j k * (1 - 1/2)⁻¹)) := by
  intro x
  have hy := log_hit_tail _ _ _ H.testS (orbits N hd V t ht' hO hc i a ht.delta ht.little ht.earned hs hp)
    (add_nonneg ht.gain ht.delta.le) 0 x
  simp only [pow_zero, mul_one] at hy
  have he : 0 ≤ shiftG s := by unfold shiftG; positivity
  have hv : 0 ≤ collars G i s j n := by
    unfold collars Reserves.polyPrice; have he := ht.delta; positivity
  have hb := budget_scale hv hy
  refine budget_mono hb (fun z => ?_) (fun z => ?_)
  · split
    next => exact mul_nonneg (mul_nonneg (spire_positive hd V t ht' hO z) (jetPrice_nonneg N z n)) (Real.exp_nonneg _)
    next => exact le_rfl
  dsimp only; split
  next hx =>
    rw [if_pos (show 0 ≤ z.fst ∧ x ∈ unionOf H.smallAt z.snd from ⟨Nat.zero_le _, hx⟩), rises N]
    let c0 : ℝ := coverNumber (radiusB s) (Captain.reachability (H:=H) z)
    have hc0 : 0 ≤ c0 := Nat.cast_nonneg _
    have Hc : (1 + c0) ^ (n*j) ≤ polyPrice i (n*j) * Real.exp (i*c0) :=
      polynomial_cost ht.delta hc0 (n*j)
    change _ * ((shiftG s * (1+c0))^(n*j) * N.design z) * Real.exp (a*c0) ≤ _ * (_ * Real.exp ((a+i)*c0))
    rw [mul_pow]
    refine le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hc (pow_nonneg he _)) (N.pvc _))
        (spire_positive hd V t ht' hO z)) (Real.exp_nonneg (a*c0))) ?_
    rw [add_mul, Real.exp_add]; unfold collars; apply le_of_eq; ring
  next => exact hb.1 z

theorem recover_spire (V : ℕ → ℝ) (t : ℝ) (Sel : H.fragrances → Prop)
    {invoice pay : ℝ} (hpay : 0 < pay) (charge : ∀ z, Sel z → pay ≤ spire V t z)
    (h : Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z => spire V t z * N.markΦ z n) a invoice) :
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

end Beacon
end YM.RGComparison01
