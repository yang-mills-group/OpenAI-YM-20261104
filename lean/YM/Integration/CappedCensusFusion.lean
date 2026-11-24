import YM.Integration.RequestedCensusSource

/-! Recombine the actual signed hard and soft rows. The local tail budget
uses a capped counting parameter and keeps the original path width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CappedCensusFusion

open Function Set Lattice Wilson RG Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection Averaging Quotes Residual WilsonStartup Geo
open Ovens Progress.DirectedRecipe Extra.Iteration Next.Scheduling IterationFour.Vacuum
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p : BudgetPoint}

def radius (σ : ℝ) : ℝ := min (σ/4) 1

def low (p : BudgetPoint) (c : Clip) (σ C : ℝ) : ℝ :=
  Footprint.payment 1 p.B 0 (radius σ) 1
    (Fintype.card Signed * lowerSize c C) (p.supportExponent+1) lowCount

def soft (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C H : ℝ) : ℝ :=
  Quotes.softReset G p H + hitNeed p G 0 H * low p c σ C

/-- The individual low forced supports keep the same genuine logarithm,
path length, anchors and reserve. Only the numerical counting radius is capped. -/
theorem rows (W : PathData G) (c : Clip) (p : BudgetPoint) {σ C Λ : ℝ}
    (h : W.Bounds c σ C Λ) (hw : Width p c σ) :
    Ac.Hit (fun i : Seat n × Low => i.1.spread (i.2.home W p 0)) p.B
      (fun i => Real.exp ((i.2.length W : ℝ)/c.relaxation) * |i.2.mark W c|)
      (p.supportExponent+1) (low p c σ C) := by
  let f (i : Low) := Real.exp ((i.length W : ℝ)/c.relaxation) * |i.mark W c|
  have hf i : 0 ≤ f i := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hK := channel_anchored (n := n) _ f hf (kept_debit G p W hw h)
  have hb : 0 < (p.B : ℝ) := Nat.cast_pos.mpr p.B_pos
  have hr : 0 < radius σ := lt_min (by linarith [h.width]) zero_lt_one
  have hr' : radius σ ≤ σ/4 := min_le_left _ _
  have hs : Footprint.reserve (3*σ/4) (p.supportExponent+1) (p.B : ℝ)⁻¹
      (radius σ) := by
    refine ⟨by linarith [p.exponent_pos],hr,?_⟩
    rw [← div_eq_mul_inv]
    linarith [hw.2.2]
  unfold low
  refine Footprint.assigned (id : Site n → Site n) 1 (fun Y : Support n => by simp)
    (fun i : Seat n × Low => i.1.2) (fun i => f i.2) (fun i => hf i.2)
    (fun i => i.2.length W) (fun i : Seat n × Low => i.1.spread (Low.home W i.2 p 0))
    hK p.B 0 p.B (C := 1) (v := lowCount) (a := p.supportExponent+1)
    (ε := radius σ) (v' := (p.B : ℝ)⁻¹) ?_ ?_ zero_le_one hs
    (fun i => f i.2) (fun i => hf i.2) (fun _ => by simp)
  · rintro i y hy
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    simpa only [affine,separation_translate,Signed.act_zero,zero_add,id_eq] using!
      (spin_separation i.1.1 i.1.2 j (0 : Site n)).trans_le (low_dist p W _ hj)
  · intro i
    rw [Seat.visit_count]
    apply le_of_mul_le_mul_left (a := (p.B : ℝ)) ?_ hb
    rw [mul_add,← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul]
    exact_mod_cast low_geometry p W i.2 (0 : Site n)

variable {X : Listing G n} {v : Collection.Source G n}
  {W : PathData G} {c : Clip} {σ C Λ H w γ κ : ℝ}

/-- The existing fuser accepts the capped numerical quote on the original
soft and flagged values, together with the sharper regular estimate. -/
theorem combine (g : G.Simple) (hn : 20 < n.val) (h : W.Bounds c σ C Λ)
    (hv : Local X p v H w) (hc : Decent c p) (hw : Width p c σ)
    (hr : Payments.Rates p.B γ w (soft G p c σ C H) κ) (β τ : ℝ) :
    let Z := Reset.after W c p X v β τ 0
    Z.Lawful σ C Λ (CappedRegularReset.regularNeed G p c σ C 0 H) γ ∧
      ∀ z, Z.eval z = earlyValue X W c p v β τ 0 z := by
  let Y := shelves X W p
  let Δ := delta (X.read v)
  let d := fill X W c p v 0 Δ
  have hΔ := delta_bound g hv.projects
  obtain ⟨u,hu,hE⟩ := hv.cheap
  obtain ⟨k,hk,hK⟩ := hv.expensive
  have hrow := rows (n := n) W c p h hw
  have hin := (enlarging G X.reg hc.radius (fun i => (hu i).1) hE).2
  have hsoft : Ac.Hit (Collection.soft X W p) p.B (quoteL W p c 0 Δ u)
      (p.supportExponent+1) (soft G p c σ C H) := by
    intro x
    refine Cost.enlarge (Cost.sum (hin x) ((hit_scale (hitPower_pos p G 0 Δ) hrow) x)) ?_
    exact add_le_add_right (mul_le_mul_of_nonneg_right (hit_allow hΔ)
      (Cost.nonneg (hrow (0 : Site n)))) _
  have hQ (i : ℕ) := Local.quote_soft (R := W) (c := c) g 0 Δ hu hv.smooth (numbering _ i)
  have hl := CappedRegularReset.lawful g hn h hv hc hw β τ 0
  have hi : Ingredients Y d p (CappedRegularReset.regularNeed G p c σ C 0 H) γ :=
    Payments.tender (hv.fittings g h hc hn 0 Δ) hl.labels.boundE
      (show Payments.hardCost p Y k w from ⟨fun i => (hk i).1,hK⟩)
      ⟨fun i => (norm_nonneg _).trans (hQ i 1), fun x => Cost.equiv (numbering _) (hsoft x)⟩
      (fun i z => ⟨(hk i).2 z, hQ i z⟩) hr
  intro Z
  refine ⟨⟨h, hi.gates W c _ _⟩, ?_⟩
  intro z
  have he := hi.unshifted W c (β+0+Δ) (vac v τ) z
  have ha := VacuumGermReset.raw_eval g hn h hv hc hw β τ 0 z
  exact he.trans (ha.trans (by simp only [Reset.supplied, neg_zero,zero_mul,Real.exp_zero,mul_one]))

end YM.Integration.CappedCensusFusion
end
