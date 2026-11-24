import YM.GapsContact.Slab.Along
/-!
# No determinant or slab norm leak over long length ratios

Arbitrary small *real* lengths on a single Trace fork: diagonalize against increasing alleged
failures when selecting with Bliss; it is not necessary to bound the curve constants uniformly
as the curve is reselected.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Ascent
open Function Filter Set Extraction Table Climb Spec MeasureTheory Trace Trace.Pilot
open Trace.Terrace Trace.Over Next.UVStress MergeProof.East
open scoped Topology BigOperators InnerProductSpace Classical NNReal ContDiff

variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {d : ℕ}
variable (F : Final C f S) (hG:G.Simple)
variable {H:(Climb.Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}
variable (X: Bliss F 𝓛 Z H)

lemma Lodge.increase {r a b B A:ℝ} (h:Lodge F r d a b B) (ha:B ≤ A): Lodge F r d a b A :=
    ⟨fun p hp hs x=> (h.before p hp hs x).trans (mul_le_mul_of_nonneg_right ha (cost_pos ..)),fun x s hs=> (h.advance x s hs).trans (mul_le_mul_of_nonneg_right ha (cost_pos ..)), h.definitive⟩

include hG X
lemma all_heights (d:ℕ)(a b:ℝ)(ha:0<a): ∃ A:ℝ,1 ≤ A ∧ ∀ᶠ s in trail, Lodge F s d a b A := by
  by_contra! h
  have hx(i:ℕ):∃ s : ℝ, 0 < s ∧ s < costHint i ∧ ¬ Lodge F s d a b (sizeHint i) := by
    have hi : ∃ᶠ s in trail, ¬ Lodge F s d a b (sizeHint i):= h _ (by unfold sizeHint; simp)
    obtain ⟨t,ht,hp,hx⟩:= (hi.and_eventually ((show ∀ᶠ s in trail, 0<s from self_mem_nhdsWithin).and ((gt_mem_nhds (Next.UVStress.cost_pos i)).filter_mono nhdsWithin_le_nhds))).exists
    exact ⟨t,hp,hx,ht⟩
  choose s hs hh he using hx
  obtain ⟨m,hm,J,hJ,V,hV⟩:= X.picks s (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun i=> (hs i).le) (fun i=>(hh i).le)) hs
  obtain ⟨A,hA,hK⟩:= open_lodge F hG X.lies hV X.budgets d a b ha
  obtain ⟨i,hi,hp⟩:= (hK.and ((size_ascends.comp hm.tendsto_atTop).eventually_ge_atTop A)).exists
  rw [hJ] at hi
  exact he (m i) (hi.increase F hp)

omit hG X in
lemma bounded_all {M:ℝ} (h: ∀ᶠ r in trail,M < LogV r): ∃ R:ℝ,0<R ∧ ∀ r∈ Ioc 0 R, M < LogV r := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨r,hr,hR⟩:= Metric.eventually_nhds_iff.mp h
  exact ⟨r/2,half_pos hr,fun s ⟨hs,hK⟩=> hR (by rw [Real.dist_eq,sub_zero,abs_of_pos hs]; exact hK.trans_lt (half_lt_self hr)) hs⟩ -- optional just convenience later

local notation "I"=> Work.C01.single F.α.unselected F.room.kernel.laws.toSymmetric

structure Billing (R:ℝ) (d:ℕ) (A:ℝ) (m:ℕ) : Prop where
    octave (r:ℝ)(hr:r∈Ioc 0 R) : Lodge F r d (1/2) 1 A
    all (t r:ℝ)(hr:r∈Ioc 0 R) (ht:t∈Ioc 0 r) (v:S.Field d) : cost F d t v ≤ A * (r/t)^m * cost F d r v

omit X hG in
lemma opened {r:ℝ}(hr:0<r)(P:ℝ→ℝ)(hP:∀ s, 0 ≤ P s)(A:ℝ)(hA:1 ≤ A)(m:ℕ)(hm: A ≤ (2:ℝ)^m)
    (hx:∀ s∈Ioc 0 r,∀ t:ℝ,s/2≤ t→ t ≤ s → P t ≤ A*P s) (s:ℝ)(hs:s∈Ioc 0 r): P s ≤ A*(r/s)^m * P r := by
  -- dyadic without logger floors. No assertion about physical r outside the Lodge interval.
  have hE : Tendsto (fun i:ℕ=> r/(2:ℝ)^i) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  obtain ⟨i,hi⟩:= (hE.eventually (ge_mem_nhds hs.1)).exists
  suffices hy: ∀ i:ℕ,∀ t:ℝ,∀ a:ℝ, a∈ Ioc 0 r→ t∈ Ioc 0 a→ a/2^i ≤ t → P t ≤ A*(a/t)^m * P a from hy i _ _ ⟨hr,le_rfl⟩ hs hi
  intro i; induction i with
  | zero=>
    rintro t a ha ⟨ht,ht'⟩ he; rw [pow_zero,div_one] at he; obtain rfl:= ht'.antisymm he; rw [div_self ht.ne',one_pow, mul_one]; exact le_mul_of_one_le_left (hP t) hA
  | succ i ih=>
    rintro t a ha ⟨ht,ht'⟩ he
    by_cases h:a/2 ≤ t
    · refine (hx a ha t h ht').trans (mul_le_mul_of_nonneg_right ?_ (hP a))
      have hv:= one_le_pow₀ ((one_le_div ht).2 ht') (n:=m)
      exact le_mul_of_one_le_right (zero_le_one.trans hA) hv
    have h₁: t ≤ a/2:= (lt_of_not_ge h).le
    have h₂: a/2 ≤ a:= (half_lt_self ha.1).le
    have h₃: (a/2) / 2^i ≤ t:=by rw [div_div, ← pow_succ']; exact he
    obtain ⟨hz,hp⟩:= ha
    calc
      P t ≤ A*(a/2/t)^m * P (a/2) := ih _ _ ⟨half_pos hz,h₂.trans hp⟩ ⟨ht,h₁⟩ h₃
      _ ≤ A*(a/2/t)^m * (2^m * P a) := mul_le_mul_of_nonneg_left ((hx a ⟨hz,hp⟩ (a/2) le_rfl h₂).trans (mul_le_mul_of_nonneg_right hm (hP a))) (by positivity)
      _ = A*(a/t)^m * P a:=by rw [←mul_assoc, mul_assoc A,←mul_pow, show (a/2/t)*2 = a/t from by ring]

lemma bills (d:ℕ) : ∃ (R:ℝ) (A:ℝ) (m:ℕ),0<R∧ 1 ≤ A ∧ Billing F R d A m := by
  obtain ⟨A,hA,hS⟩:= all_heights F hG X d (1/2) 1 (by norm_num)
  rw [eventually_nhdsWithin_iff] at hS
  obtain ⟨r,hr,hR⟩:= Metric.eventually_nhds_iff.mp hS
  have h(r':ℝ)(ht:r' ∈ Ioc 0 (r/2)): Lodge F r' d (1/2) 1 A:= hR (by rw [Real.dist_eq,sub_zero,abs_of_pos ht.1]; exact ht.2.trans_lt (half_lt_self hr)) ht.1
  obtain ⟨m,hm⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 from one_lt_two)).eventually_ge_atTop A).exists
  refine ⟨r/2,A,m,half_pos hr,hA,h,fun t s hs ht v=> opened hs.1 (fun t=>cost F d t v) (fun _=>cost_pos ..) A hA m hm (fun a ha b hx he=>?_) t ht⟩
  have hb : 1/2 ≤ b/a := by apply (le_div_iff₀ ha.1).mpr; simpa only [one_div, div_eq_mul_inv,one_mul,mul_comm] using hx
  have hC:= (h a ⟨ha.1,ha.2.trans hs.2⟩).advance v _ ⟨hb,(div_le_one ha.1).2 he⟩
  rw [mul_div_cancel₀ _ ha.1.ne'] at hC
  exact hC
end YM.GapsContact.Ascent
