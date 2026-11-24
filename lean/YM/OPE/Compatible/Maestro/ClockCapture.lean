import YM.OPE.Compatible.Maestro.Recall
/-!
# Native timer on real c; gap reconstruction

Pick LAST level that needs a union. Works even if successive ratios in a sequence are logarithmically incomparable. No simultaneous caps chosen before the layout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot
variable {G:Gauge}{C:Family G}{I : Type}{l:Filter I}{T r : I→ℝ}{q:I→ℕ}{i n b:ℕ}
variable (hG:G.Simple)(A:Allot C)
-- ξ exposure. when r=a/M. select high where r≤η exposing. accounts log poly.
def scopeR (C:Family G)(b i:ℕ) : ℝ := (atLevel C i b + 2:ℝ) -- b orders right?
def touch (C:Family G)(b i:ℕ):= 8*C.S.a i*scopeR C b i
lemma scopeR_up (C:Family G)(b i:ℕ):1 ≤ scopeR C b i:=by unfold scopeR; linarith only [Nat.cast_nonneg (α:=ℝ) (atLevel C i b)]
lemma touch_pos (C:Family G)(b i:ℕ):0< touch C b i:= mul_pos (mul_pos (by norm_num) (C.S.a_pos _)) (zero_lt_one.trans_le (scopeR_up ..))
include hG A
lemma round_time (b:ℕ)(ht:Tendsto T l atTop) (hq: Score l T (fun i=>β C (q i))): Round l T (fun i=>scopeR C b (q i)):=by
    have hp:=gap_score ht (stepβ A hG ht hq|>.up) b; have hz := tick_score ht hq; apply Round.if_inv (Eventually.of_forall fun _=> zero_lt_one.trans_le (scopeR_up ..)) _ ht (Eventually.of_forall fun _=> scopeR_up ..); simpa only [scopeR,atLevel,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using! (((hp.plus (Score.steady (3:ℝ) ht) ht).product hz).plus (Score.steady (2:ℝ) ht) ht)
lemma timer_pol (b:ℕ): Score atTop C.S.scale (scopeR C b):=by
   have ht:=C.S.divergent; exact (round_time (q:=id) hG A b ht (scale_coin (C:=C) (q:=id) hG tendsto_id ht (Score.time ht)|>.up)).up
lemma timer_rate (b:ℕ) : ∀ᶠ i:ℕ in atTop,touch C b i ≤ Real.exp (-(1/2)*C.S.scale i):=by
   obtain ⟨u,h⟩:= ((Score.steady (8:ℝ) C.S.divergent).product (timer_pol hG A b)).fitsQ C.S.divergent
   let c:ℝ:=1/2; have hc:0<c:=by norm_num [c]
   have hp₀: Tendsto (fun x:ℝ=>x^u/Real.exp (c*x)) atTop (𝓝 0):=by
       have h:= (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (u:ℝ) c hc); simp_rw [Real.rpow_natCast,neg_mul, Real.exp_neg,← div_eq_mul_inv] at h; exact h
   filter_upwards [h,(hp₀.comp C.S.divergent).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1))] with i hi hp -- le_mem?
   let x:=C.S.scale i; have ht:x^u ≤ Real.exp (c*x):=(div_le_one (Real.exp_pos _)).mp hp; have hz:C.S.a i= Real.exp (-x):=by unfold x Schedule.scale; rw [Real.log_inv,neg_neg,Real.exp_log (C.S.a_pos _)]
   unfold touch
   rw [mul_right_comm, hz]; refine (mul_le_mul_of_nonneg_right (le_trans ((Real.le_norm_self _).trans hi) ht) (Real.exp_nonneg _)).trans_eq ?_; rw [← Real.exp_add]; ring_nf; unfold c x; ring_nf
lemma timer_stops (b:ℕ): Tendsto (touch C b) atTop (𝓝 0):=by
    apply squeeze_zero' (Eventually.of_forall fun i=>(touch_pos C b i).le) (timer_rate hG A b); exact Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by norm_num) C.S.divergent)
omit hG A
private def Listable (C:Family G)(b:ℕ)(x:ℝ) : Prop:= ∃ i:ℕ, x ≤ touch C b i ∧ ∀ z, x ≤ touch C b z→ z ≤ i
def topClock (C:Family G)(b:ℕ)(x:ℝ):= if h:Listable C b x then Classical.choose h else 0
include hG A
lemma wins {x:ℝ}(hp:0<x)(hx:∃ i,x ≤ touch C b i) : let m:=topClock C b x; x ≤ touch C b m ∧ ∀ i,x ≤ touch C b i→ i ≤ m:=by
   obtain ⟨N,hN⟩:=eventually_atTop.1 ((timer_stops hG A b).eventually (gt_mem_nhds hp)); have he:Listable C b x:=by
      let s:= (Finset.range N).filter fun i=> x ≤ touch C b i; have hh(i):i∈s↔ x ≤ touch C b i := ⟨fun h=> (Finset.mem_filter.mp h).2,fun h=> Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_not_ge fun hz=> not_lt.mpr h (hN i hz)),h⟩⟩
      obtain ⟨i,hi⟩:=hx; have ht:s.Nonempty:= ⟨i,(hh i).2 hi⟩; exact ⟨_,(hh _).1 (Finset.max'_mem s ht),fun i h=> Finset.le_max' s i ((hh _).2 h)⟩
   unfold topClock; rw [dif_pos he]; exact he.choose_spec
end YM.OPE.Arboreal
