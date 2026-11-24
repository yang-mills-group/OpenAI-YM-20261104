import YM.MatchingLedger.Review.Stencils

/-!
# Pricing scales for physically arbitrarily large cutoff budget and actual angles

True post-L functions slow in actual funding, independent of volume, not independent of order.
Check that e.g. raising M uniformly may also consume deadline powers of scaled labels in d.
No pre-book change implied; no ongoing omega big-oh. Simple G needed now for growth assertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Review.Clock
open Function Filter Set MeasureTheory Lattice RG Wilson Tree Pressure
open Precision Action Top Home Cooling Gazette Periodical Kiosk Books Push.Uniform
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {G : Gauge}

-- polynomial (≥1 id), independent bills witnesses.
def Tariff (f : ℝ→ℝ) := ∃ M : ℝ, 0≤M ∧ ∃ d : ℕ, ∀ x:ℝ,1≤x → ‖f x‖≤ M*x^d
namespace Tariff
lemma fixed (c : ℝ) : Tariff (fun _=>c) := ⟨‖c‖,norm_nonneg _,0,fun x _=>by simp⟩
lemma lift : Tariff (fun x=>x):= ⟨1,zero_le_one,1,fun x hx=>by rw [Real.norm_of_nonneg (zero_le_one.trans hx)];simp⟩
variable {f g:ℝ→ℝ}
lemma add (h:Tariff f)(he:Tariff g): Tariff (fun x=> f x+g x):= by
  obtain ⟨M,h₁,d,u⟩:= h; obtain ⟨N,h₂,k,v⟩:= he; refine ⟨M+N,add_nonneg h₁ h₂,d+k,fun x hx=>?_⟩; rw [add_mul]; apply (norm_add_le ..).trans; exact add_le_add ((u x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by omega)) h₁)) ((v x hx).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by omega)) h₂))
lemma times (h:Tariff f)(he:Tariff g): Tariff (fun x=>f x*g x):= by
  obtain ⟨M,h₁,d,u⟩:= h; obtain ⟨N,h₂,k,v⟩:= he; refine ⟨M*N,mul_nonneg h₁ h₂,d+k,fun x hx=>?_⟩; rw [norm_mul]; apply le_trans (mul_le_mul (u x hx) (v x hx) (norm_nonneg _) (mul_nonneg h₁ (pow_nonneg (zero_le_one.trans hx) _))); rw [pow_add]; exact Eq.le (by ring)
lemma pow (h:Tariff f)(k:ℕ): Tariff (fun x=>f x^k):= by induction k with
 | zero=> simpa using fixed 1
 | succ k ih=> simp_rw [pow_succ]; exact ih.times h
lemma money {ι : Type*} (s : Finset ι)(f:ι→ℝ→ℝ)(h:∀ i,Tariff (f i)): Tariff (fun x=> ∑ i∈s,f i x):=by
  induction s using Finset.induction_on with | empty=> simpa using fixed 0 | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i).add ih
lemma power (d : ℕ) : Tariff (refund d):= (lift.pow (3*d+8)).pow _
lemma bill {Q} (h:Tariff Q)(n k l:ℕ): Tariff (fun x=> FPS.bill n (Q x) k l):= by
  unfold FPS.bill FPS.board; exact (h.times ((((h.add (fixed _)).add h).add ((fixed _).times h)))).pow _
lemma ann (d k : ℕ)(l:ℕ)(M:ℝ)(G : Gauge) : Tariff (fun x=>ticket G d k l M x):= by
  unfold ticket; refine (((fixed _).times (lift.pow _|>.pow (k+1))).add (fixed _)).add ?_
  unfold annotation; exact money _ _ (fun i=> (fixed (M*(height G l : ℝ)^i.2)).times (bill (power d) d i.1 i.2))
lemma bounded_on_cent (h : Tariff f){ε : ℝ} (he:0<ε) : ∀ᶠ b:ℝ in atTop, ∀ t:ℝ, Span b t → f (clock b)*t⁻¹≤ ε:= by
  obtain ⟨M,hM,k,hk⟩:= h
  filter_upwards [infinite_meter.eventually_ge_atTop 1, fund (M/ε) k] with b hb ht t hv
  have hh := zero_lt_one.trans_le hv.starts
  have hx := ht t hv; rw [← div_eq_mul_inv,div_le_iff₀ hh]; apply ((le_abs_self _).trans (hk _ hb)).trans
  rw [div_mul_eq_mul_div] at hx
  exact ((div_le_iff₀ he).1 hx).trans_eq (mul_comm ..)
end Tariff

variable (C:Family G)

lemma hat_deep (hG:G.Simple) : Tendsto C.path.levels.clock.hatBeta atTop atTop := tendsto_atTop_add_const_left _ _ (C.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
lemma ruler_deep (hG:G.Simple): Tendsto (ruler C) atTop atTop :=
  (infinite_meter.comp (hat_deep C hG)).comp (Filter.tendsto_add_atTop_nat 1)
end YM.MatchingLedger.Review.Clock
