import YM.Integration.VacuumGermReset

/-! The same native regular reset with a capped moment parameter. The original
profile width, path, listing, input, shell and forced family are unchanged.
Only the numerical quote is sharpened; no upper bound on profile width is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CappedRegularReset
open Function Set Lattice Wilson RG
open AnalyticBridge VerifiedReset Collection Averaging Quotes Residual WilsonStartup Geo
open Ovens Progress.DirectedRecipe Extra.Iteration Next.Scheduling
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def radius (σ : ℝ) : ℝ := min (σ / 2) 1
def moment (s : ℕ) (σ : ℝ) : ℝ := momentPrice s (radius σ)
private lemma radius_pos {σ : ℝ} (h : 0 < σ) : 0 < radius σ :=
  lt_min (half_pos h) zero_lt_one
private lemma moment_pos (s : ℕ) {σ : ℝ} (h : 0 < σ) : 0 < moment s σ :=
  momentPrice_pos s (radius_pos h)
private lemma spend (s : ℕ) {σ z : ℝ} (hσ : 0 < σ) (hz : 0 ≤ z) :
    (1 + z) ^ s ≤ moment s σ * Real.exp ((σ / 2) * z) := by
  refine (spendMoment s (radius_pos hσ) hz).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.exp_monotone (mul_le_mul_of_nonneg_right (min_le_left _ _) hz))
    (moment_pos s hσ).le

/-- A fixed-degree polynomial in the original reciprocal width. -/
theorem moment_bound (s : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    moment s σ ≤ Real.exp 1 * s.factorial * (1 + 2 * σ⁻¹) ^ s := by
  have hi : (radius σ)⁻¹ ≤ 1 + 2 * σ⁻¹ := by
    by_cases h : σ / 2 ≤ 1
    · have he : (σ / 2)⁻¹ = 2 * σ⁻¹ := by field_simp [hσ.ne']
      rw [radius, min_eq_left h, he]
      linarith
    · norm_num [radius, min_eq_right (le_of_not_ge h)]
      positivity
  have hp : ((radius σ)⁻¹) ^ s ≤ (1 + 2 * σ⁻¹) ^ s :=
    pow_le_pow_left₀ (inv_nonneg.mpr (radius_pos hσ).le) hi s
  unfold moment momentPrice
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (Real.exp_monotone (min_le_right _ _))
      (Nat.cast_nonneg _)) hp (pow_nonneg (inv_nonneg.mpr (radius_pos hσ).le) _)
    (by positivity)

variable (G) (p : BudgetPoint) (R : PathData G)
def highFee (k : ℕ) (p : BudgetPoint) (σ : ℝ) := Wages.startup G k p.power p.order * moment (Wages.grade k p.power p.order) σ
def both p σ := highFee G 3 p σ + highFee G 4 p σ
private lemma highFee_pos (p k) {σ : ℝ} (h : 0 < σ) : 0 < highFee G k p σ := by
  have := Wages.slot_ge G p.power p.order 0; have := moment_pos (Wages.grade k p.power p.order) h
  unfold highFee Wages.startup; positivity
private lemma both_pos (p) {σ : ℝ} (h : 0 < σ) : 0 < both G p σ := add_pos (highFee_pos G p 3 h) (highFee_pos G p 4 h)
private lemma high_allow (d : High) {σ : ℝ} (hs : 0 < σ) : High.price R d p * Real.exp ((σ/2)*d.length R) ≤
    both G p σ * ((High.term R d).budget σ) := by
  have := Wages.slot_ge G p.power p.order 0
  have h := highFee_pos G p (High.arity d) hs
  let a := High.term R d
  have hA : 0 ≤ a.budget σ := by unfold Atom.budget Atom.magnitude; positivity
  let g := Wages.grade d.arity p.power p.order
  let v := Wages.startup G d.arity p.power p.order
  have hn : 0 ≤ v*a.magnitude := by unfold v Wages.startup Atom.magnitude; positivity
  have he := mul_le_mul_of_nonneg_left (spend g hs (Nat.cast_nonneg a.length)) hn
  have hle : highFee G d.arity p σ ≤ both G p σ := by
    unfold both; rcases d.significant with hi|hi <;> rw [hi] <;> linarith only [highFee_pos G p 3 hs, highFee_pos G p 4 hs]
  calc _ ≤ (v*a.magnitude*(moment g σ * Real.exp ((σ/2)*a.length))) * Real.exp ((σ/2)*a.length) := by
            rw [High.price,add_comm (High.length R d:ℝ)]; exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
       _ = highFee G d.arity p σ * a.budget σ := by
            unfold Atom.budget; rw [show σ*(a.length:ℝ)=σ/2*a.length+σ/2*a.length by ring,Real.exp_add]; unfold highFee v g; ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hle hA
private lemma high_budget {c σ C Λ} (h : R.Bounds c σ C Λ) :
    SumBudget (fun d => High.price R d p * Real.exp ((σ/2)*d.length R)) (both G p σ * (C+C)) := by
  apply YM.Push.AbsoluteSums.budget_mono (YM.Push.AbsoluteSums.budget_scale (both_pos _ p h.width).le (f:=fun d => (High.term R d).budget σ) (Cost.sum h.three h.four))
  · exact fun i => mul_nonneg (High.price_nn ..) (Real.exp_pos _).le
  exact fun d => high_allow G p R d h.width

def lowFee (σ : ℝ) := lowCost G p 0 * moment (rowDegree p) σ
private lemma lowFee_nonneg {σ : ℝ} (hs : 0 < σ) : 0 ≤ lowFee G p σ := mul_nonneg (low_nonneg ..) (moment_pos _ hs).le
private lemma low_budget {c σ C Λ} (h : R.Bounds c σ C Λ) : SumBudget
    (fun d : Low => |d.mark R c| * lowCost G p (d.length R) * Real.exp ((σ/2)*d.length R)) (lowFee G p σ * lowerSize c C) := by
  apply Cost.mono (YM.Push.AbsoluteSums.budget_scale (lowFee_nonneg G p h.width) (lower_budget G R h))
  · exact fun i => mul_nonneg (mul_nonneg (abs_nonneg _) (low_nonneg ..)) (Real.exp_pos _).le
  intro d; let l := d.length R
  have ht := (low_vs G p l).trans (mul_le_mul_of_nonneg_left (spend _ h.width (Nat.cast_nonneg _)) (low_nonneg ..))
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg (d.mark R c))) (Real.exp_pos _).le)
  rw [show σ*((d.length R):ℝ)=σ/2*l+σ/2*l by unfold l; ring,Real.exp_add,lowFee]
  unfold l; ring_nf; rfl

def lowBase (c : Clip) (p : BudgetPoint) (σ C : ℝ) :=
  Quotes.anchoredFee p Geo.lowCount * (lowFee G p σ * Geo.lowerSize c C)
def highBase (p : BudgetPoint) (σ C : ℝ) :=
  Quotes.anchoredFee p Geo.highCount * (both G p σ * (C + C))
def regularNeed (p : BudgetPoint) (c : Clip) (σ C α H : ℝ) :=
  Quotes.resetFee G p * H + Collection.turnFee p *
    (H * lowBase G c p σ C + (|α| * p.threshold ^ 3 + H) * highBase G p σ C)

variable {G p R} {c : Clip} {σ C Λ H : ℝ} {X : Listing G n}
    {v : Collection.Source G n}
private lemma regular_quotes (hx : R.Bounds c σ C Λ) (hc : Decent c p)
    (hw : Width p c σ) (α Δ : ℝ) {u : ℕ → ℝ}
    (h1 : ∀ i, p.supBounds (X.reg i).site (X.reg i).support (v.logRead i) (u i))
    (hu : Quotes.early p X.reg u H) (hΔ : p.threshold ^ 2 * |Δ| ≤ H) :
    Quotes.anchored p (incoming X R p) (Collection.quoteE R p c α Δ u)
      (regularNeed G p c σ C α H) := by
  have hC := Cost.nonneg hx.three
  have he := (Quotes.enlarging G X.reg hc.radius (fun i => (h1 i).1) hu).1
  have hB : 0 < (p.B : ℝ) := Nat.cast_pos.mpr p.B_pos
  have hM : p.supportExponent / p.B ≤ σ / 2 :=
    (div_le_div_of_nonneg_right (by linarith : p.supportExponent ≤ p.supportExponent + 1)
      hB.le).trans (hw.2.2.trans (by linarith [hx.width]))
  have ha := Quotes.channel_mass (n := n) (Low.length R)
    (fun i => i.home R p (0 : Site n)) _
    (fun i => mul_nonneg (abs_nonneg _) (low_nonneg ..))
    (low_budget G p R hx) Geo.lowCount hM (fun i => Geo.low_geometry p R i _)
  have hb := Quotes.channel_mass (n := n) (High.length R)
    (fun i => i.home R (0 : Site n)) (fun i => i.price R p)
    (fun i => High.price_nn ..) (high_budget G p R hx) Geo.highCount hM
    (fun i => Geo.high_geometry p R i _)
  have hL : 0 ≤ lowBase G c p σ C := by
    have := lowFee_nonneg G p hx.width
    have := c.quadratic_pos
    unfold lowBase Quotes.anchoredFee Geo.lowerSize
    positivity
  have hH : 0 ≤ highBase G p σ C := by
    have := both_pos G p hx.width
    unfold highBase Quotes.anchoredFee
    positivity
  have ht := Collection.turnFee_pos p
  have hp := p.threshold_pos
  intro o
  refine Cost.enlarge (Cost.sum (he o) (Cost.sum
    (Quotes.anchored_scale (r := Collection.turnFee p * (|Δ| * p.threshold ^ 2))
      (by positivity) ha o)
    (Quotes.anchored_scale (r := Collection.turnFee p * (|α + Δ| * p.threshold ^ 3))
      (by positivity) hb o))) ?_
  change Quotes.resetFee G p * H +
    (Collection.turnFee p * (|Δ| * p.threshold ^ 2) * lowBase G c p σ C +
      Collection.turnFee p * (|α + Δ| * p.threshold ^ 3) * highBase G p σ C) ≤ _
  unfold regularNeed
  nlinarith only [mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hΔ hL) ht.le,
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (Collection.fresh_allow hΔ (α := α)) hH) ht.le]

/-- The original shell, with its original forced bound and the capped regular bill. -/
theorem lawful (g : G.Simple) (hn : 20 < n.val)
    (h : R.Bounds c σ C Λ) {w : ℝ} (hv : Local X p v H w)
    (hc : Decent c p) (hw : Width p c σ) (β τ α : ℝ) :
    (VacuumGermReset.shell R c p X v β τ α).Lawful σ C Λ
      (regularNeed G p c σ C 0 H) w := by
  let Y := shelves X R p
  let Δ := delta (X.read v)
  have hm : p.threshold ^ 2 * |Δ| ≤ H := delta_bound g hv.projects
  have hF := hv.fittings g h hc hn 0 Δ
  have hE : (Y.pours (fill X R c p v 0 Δ)).EBound p
      (regularNeed G p c σ C 0 H) := by
    obtain ⟨u, hu, hb⟩ := hv.cheap
    exact ⟨_, fun i => Local.quote_regular g h hc 0 Δ hu hv.smooth (numbering _ i),
      fun x => Cost.equiv (numbering _) (regular_quotes h hc hw 0 Δ hu hb hm x)⟩
  have hK : (Y.pours (fill X R c p v 0 Δ)).KBound p w := by
    obtain ⟨k, hk, hK⟩ := hv.expensive
    exact ⟨k, hk, Payments.drop_reserve p (fun i => (X.hard i).support)
      (fun i => (hk i).1) hK⟩
  exact ⟨h, ⟨hF.regular, hF.support, hF.moves, hE, hK⟩⟩

end YM.Integration.CappedRegularReset
end
