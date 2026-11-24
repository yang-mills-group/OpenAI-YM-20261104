import YM.Integration.CappedRegularReset

/-! Capped prices for the original clipped kinetic rows. Only the numerical
moment and hit-summation parameters are capped. The path, norm, threshold,
supports, width geometry, and every low/high row remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeCappedKineticQuotes
open Function Set Lattice Wilson RG Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection Averaging Quotes Residual WilsonStartup Geo
open Ovens Progress.DirectedRecipe Extra.Iteration Next.Scheduling
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

private lemma radius_pos {σ : ℝ} (h : 0 < σ) : 0 < CappedRegularReset.radius σ :=
  lt_min (half_pos h) zero_lt_one
private lemma moment_pos (s : ℕ) {σ : ℝ} (h : 0 < σ) : 0 < CappedRegularReset.moment s σ :=
  momentPrice_pos s (radius_pos h)
private lemma spend (s : ℕ) {σ z : ℝ} (hσ : 0 < σ) (hz : 0 ≤ z) :
    (1 + z) ^ s ≤ CappedRegularReset.moment s σ * Real.exp ((σ / 2) * z) := by
  refine (spendMoment s (radius_pos hσ) hz).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.exp_monotone (mul_le_mul_of_nonneg_right (min_le_left _ _) hz))
    (moment_pos s hσ).le

variable (G : Gauge) (p : BudgetPoint) (R : PathData G)

private lemma highFee_pos (p k) {σ : ℝ} (h : 0 < σ) : 0 < CappedRegularReset.highFee G k p σ := by
  have := Wages.slot_ge G p.power p.order 0; have := moment_pos (Wages.grade k p.power p.order) h
  unfold CappedRegularReset.highFee Wages.startup; positivity
private lemma both_pos (p) {σ : ℝ} (h : 0 < σ) : 0 < CappedRegularReset.both G p σ := add_pos (highFee_pos G p 3 h) (highFee_pos G p 4 h)
private lemma high_allow (d : High) {σ : ℝ} (hs : 0 < σ) : High.price R d p * Real.exp ((σ/2)*d.length R) ≤
    CappedRegularReset.both G p σ * ((High.term R d).budget σ) := by
  have := Wages.slot_ge G p.power p.order 0
  have h := highFee_pos G p (High.arity d) hs
  let a := High.term R d
  have hA : 0 ≤ a.budget σ := by unfold Atom.budget Atom.magnitude; positivity
  let g := Wages.grade d.arity p.power p.order
  let v := Wages.startup G d.arity p.power p.order
  have hn : 0 ≤ v*a.magnitude := by unfold v Wages.startup Atom.magnitude; positivity
  have he := mul_le_mul_of_nonneg_left (spend g hs (Nat.cast_nonneg a.length)) hn
  have hle : CappedRegularReset.highFee G d.arity p σ ≤ CappedRegularReset.both G p σ := by
    unfold CappedRegularReset.both; rcases d.significant with hi|hi <;> rw [hi] <;> linarith only [highFee_pos G p 3 hs, highFee_pos G p 4 hs]
  calc _ ≤ (v*a.magnitude*(CappedRegularReset.moment g σ * Real.exp ((σ/2)*a.length))) * Real.exp ((σ/2)*a.length) := by
            rw [High.price,add_comm (High.length R d:ℝ)]; exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
       _ = CappedRegularReset.highFee G d.arity p σ * a.budget σ := by
            unfold Atom.budget; rw [show σ*(a.length:ℝ)=σ/2*a.length+σ/2*a.length by ring,Real.exp_add]; unfold CappedRegularReset.highFee v g; ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hle hA
private lemma high_budget {c σ C Λ} (h : R.Bounds c σ C Λ) :
    SumBudget (fun d => High.price R d p * Real.exp ((σ/2)*d.length R)) (CappedRegularReset.both G p σ * (C+C)) := by
  apply YM.Push.AbsoluteSums.budget_mono (YM.Push.AbsoluteSums.budget_scale (both_pos _ p h.width).le (f:=fun d => (High.term R d).budget σ) (Cost.sum h.three h.four))
  · exact fun i => mul_nonneg (High.price_nn ..) (Real.exp_pos _).le
  exact fun d => high_allow G p R d h.width

private lemma lowFee_nonneg {σ : ℝ} (hs : 0 < σ) : 0 ≤ CappedRegularReset.lowFee G p σ := mul_nonneg (low_nonneg ..) (moment_pos _ hs).le
private lemma low_budget {c σ C Λ} (h : R.Bounds c σ C Λ) : SumBudget
    (fun d : Low => |d.mark R c| * lowCost G p (d.length R) * Real.exp ((σ/2)*d.length R)) (CappedRegularReset.lowFee G p σ * lowerSize c C) := by
  apply Cost.mono (YM.Push.AbsoluteSums.budget_scale (lowFee_nonneg G p h.width) (lower_budget G R h))
  · exact fun i => mul_nonneg (mul_nonneg (abs_nonneg _) (low_nonneg ..)) (Real.exp_pos _).le
  intro d; let l := d.length R
  have ht := (low_vs G p l).trans (mul_le_mul_of_nonneg_left (spend _ h.width (Nat.cast_nonneg _)) (low_nonneg ..))
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg (d.mark R c))) (Real.exp_pos _).le)
  rw [show σ*((d.length R):ℝ)=σ/2*l+σ/2*l by unfold l; ring,Real.exp_add,CappedRegularReset.lowFee]
  unfold l; ring_nf; rfl

def hitRadius (σ : ℝ) : ℝ := min (σ / 4) 1

def lowHitCost (p : BudgetPoint) (c : Clip) (σ C : ℝ) : ℝ :=
  Footprint.payment 1 p.B 0 (hitRadius σ) 1
    (Fintype.card Signed * Geo.lowerSize c C) (p.supportExponent + 1) Geo.lowCount

def highHitCost (p : BudgetPoint) (σ C : ℝ) : ℝ :=
  Footprint.payment 1 1 0 (hitRadius σ) 1
    (Fintype.card Signed * (C + C)) (p.supportExponent + 1) Geo.highCount

private lemma high_distance (d : High) {y : Site n}
    (hy : y ∈ d.home R (0 : Site n)) : separation y 0 ≤ d.length R := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  change z ∈ insert 0
    (Finset.univ.biUnion fun j => ((High.term R d).leg j).stencil) at hz
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    simp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hz
  have hs : wrap n z + 0 ∈ Wages.walkCuts ((High.term R d).leg j) (0 : Site n) :=
    Finset.mem_image.mpr ⟨z, hj, rfl⟩
  refine (VerifiedReset.slot_length ((High.term R d).leg j) 0 hs).trans ?_
  exact Finset.single_le_sum
    (f := fun i : Fin d.arity => ((High.term R d).leg i).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

variable {G p R} {c : Clip} {σ C Λ : ℝ}

/-- The complete original anchored low/high prices, with capped moments. -/
theorem regular_rows (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ) :
    Quotes.anchored p (n := n) (Quotes.lowEntry G R p)
      (fun i => |i.2.mark R c| * lowCost G p (i.2.length R))
      (CappedRegularReset.lowBase G c p σ C) ∧
    Quotes.anchored p (n := n) (Quotes.highEntry G R)
      (fun i => i.2.price R p) (CappedRegularReset.highBase G p σ C) := by
  have hB : 0 < (p.B : ℝ) := Nat.cast_pos.mpr p.B_pos
  have hM : p.supportExponent / p.B ≤ σ / 2 :=
    (div_le_div_of_nonneg_right
      (by linarith : p.supportExponent ≤ p.supportExponent + 1) hB.le).trans
      (hw.2.2.trans (by linarith [h.width]))
  exact ⟨Quotes.channel_mass (Low.length R)
    (fun i => i.home R p (0 : Site n)) _
    (fun i => mul_nonneg (abs_nonneg _) (low_nonneg ..))
    (low_budget G p R h) Geo.lowCount hM (fun i => Geo.low_geometry p R i _),
    Quotes.channel_mass (High.length R)
      (fun i => i.home R (0 : Site n)) (fun i => i.price R p)
      (fun i => High.price_nn ..) (high_budget G p R h)
      Geo.highCount hM (fun i => Geo.high_geometry p R i _)⟩

/-- Both complete global-hit families are paid at the stronger exponent +1.
The cap is a summation parameter, not a new width for the original path. -/
theorem full_hits (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ) :
    Ac.Hit (fun i : Seat n × Low => i.1.spread (i.2.home R p 0)) p.B
      (fun i => Real.exp ((i.2.length R : ℝ) / c.relaxation) * |i.2.mark R c|)
      (p.supportExponent + 1) (lowHitCost p c σ C) ∧
    Ac.Hit (fun i : Seat n × High => i.1.spread (i.2.home R 0)) p.B
      (fun i => i.2.charge R) (p.supportExponent + 1)
      (highHitCost p σ C) := by
  have hB : 0 < (p.B : ℝ) := Nat.cast_pos.mpr p.B_pos
  have he : 0 < hitRadius σ := lt_min (by linarith [h.width]) zero_lt_one
  have he' : hitRadius σ ≤ σ / 4 := min_le_left _ _
  have hp : 0 ≤ p.supportExponent + 1 := by linarith [p.exponent_pos]
  have hrLow : Footprint.reserve (3 * σ / 4) (p.supportExponent + 1)
      (p.B : ℝ)⁻¹ (hitRadius σ) := by
    refine ⟨hp, he, ?_⟩
    rw [← div_eq_mul_inv]
    linarith [hw.2.2]
  have hrHigh : Footprint.reserve σ (p.supportExponent + 1)
      (p.B : ℝ)⁻¹ (hitRadius σ) := by
    refine ⟨hp, he, ?_⟩
    rw [← div_eq_mul_inv]
    linarith [hw.2.2, h.width]
  constructor
  · let g (i : Low) := Real.exp ((i.length R : ℝ) / c.relaxation) * |i.mark R c|
    have hg i : 0 ≤ g i := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    have hK := Quotes.channel_anchored (n := n) _ g hg (Geo.kept_debit G p R hw h)
    unfold lowHitCost
    refine Footprint.assigned (id : Site n → Site n) 1
      (fun Y : Support n => by simp)
      (fun i : Seat n × Low => i.1.2) (fun i => g i.2) (fun i => hg i.2)
      (fun i => i.2.length R)
      (fun i : Seat n × Low => i.1.spread (i.2.home R p (0 : Site n)))
      hK p.B 0 p.B (C := 1) (v := Geo.lowCount)
      (a := p.supportExponent + 1) (ε := hitRadius σ) (v' := (p.B : ℝ)⁻¹)
      ?_ ?_ zero_le_one hrLow (fun i => g i.2) (fun i => hg i.2)
      (fun _ => by simp)
    · rintro i y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      simpa only [affine, separation_translate, Signed.act_zero, zero_add, id_eq]
        using! (spin_separation i.1.1 i.1.2 j (0 : Site n)).trans_le
          (Geo.low_dist p R _ hj)
    intro i
    rw [Seat.visit_count]
    apply le_of_mul_le_mul_left (a := (p.B : ℝ)) ?_ hB
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
    exact_mod_cast Geo.low_geometry p R i.2 (0 : Site n)
  · let g (i : High) := i.charge R
    have hg i : 0 ≤ g i := by unfold g High.charge Atom.magnitude; positivity
    have hb : SumBudget (fun i => g i * Real.exp (σ * i.length R)) (C + C) :=
      Cost.sum h.three h.four
    have hK := Quotes.channel_anchored (n := n) (High.length R) g hg hb
    unfold highHitCost
    refine Footprint.assigned (id : Site n → Site n) 1
      (fun Y : Support n => by simp)
      (fun i : Seat n × High => i.1.2) (fun i => g i.2) (fun i => hg i.2)
      (fun i => i.2.length R)
      (fun i : Seat n × High => i.1.spread (i.2.home R (0 : Site n)))
      hK 1 0 p.B (C := 1) (v := Geo.highCount)
      (a := p.supportExponent + 1) (ε := hitRadius σ) (v' := (p.B : ℝ)⁻¹)
      ?_ ?_ zero_le_one hrHigh (fun i => g i.2) (fun i => hg i.2)
      (fun _ => by simp)
    · rintro i y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hd := (high_distance (G := G) R i.2 hj).trans (Nat.le_succ _)
      simpa only [affine, separation_translate, Signed.act_zero, zero_add,
        id_eq, one_mul, Nat.add_comm 1]
        using! (spin_separation i.1.1 i.1.2 j (0 : Site n)).trans_le hd
    intro i
    rw [Seat.visit_count]
    apply le_of_mul_le_mul_left (a := (p.B : ℝ)) ?_ hB
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
    exact_mod_cast Geo.high_geometry p R i.2 (0 : Site n)

end YM.Integration.NativeCappedKineticQuotes
end
