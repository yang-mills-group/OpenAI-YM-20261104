import YM.RGComparison.Core16.Therm.Gauze
/-!
# Complete a Wick calculation at this seam.

Interchanging shock-up jets on the mixing ray and Hessian+determinant price. Use moments, not raw
score: order 1 nonlinear term and part of order 2 on this fiber are centered odd terms. Prove
EXACT relation between raw center-shift Gaussian series and centered pure-quadratic calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Therm
open Function Filter MeasureTheory Set Metric Asymptotics Analysis
open scoped Topology ContDiff NNReal
open PertExtension PertExtension.Series Tested Radial
section raw
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
   (K f : E→ℝ) (x : E)
private lemma diag0 : (Finset.antidiagonal 0 : Finset (ℕ×ℕ))={(0,0)}:= by decide
private lemma diag1 : (Finset.antidiagonal 1 : Finset (ℕ×ℕ))={(0,1),(1,0)}:= by decide
private lemma diag2 : (Finset.antidiagonal 2 : Finset (ℕ×ℕ))={(0,2),(1,1),(2,0)}:= by decide
lemma nil_bill : Radial.integrandSeries f K 0 x = K 0:= by simp [integrandSeries,expsum,Zone.TaylorPow,Zone.mul]
lemma first_bill : Radial.integrandSeries f K 1 x = jet K 1 x-K 0 * jet f 3 x:= by
  unfold integrandSeries; simp [expsum,Zone.TaylorPow,layers,Zone.mul ,diag1,Finset.sum_range_succ]; ring
lemma second_bill : Radial.integrandSeries f K 2 x= jet K 2 x - jet K 1 x * jet f 3 x + K 0 * ((1/2:ℝ)*jet f 3 x ^ 2 - jet f 4 x) := by
  unfold integrandSeries; simp [expsum,Zone.TaylorPow,layers,Zone.mul ,diag1,diag2,Finset.sum_range_succ]; ring

lemma add_jet (h : ContDiffAt ℝ ω K 0)(g : ContDiffAt ℝ ω f 0)(i : ℕ) : jet (K+f) i x=jet K i x+jet f i x:= score_add x h g
lemma sub_jet (h : ContDiffAt ℝ ω K 0)(g : ContDiffAt ℝ ω f 0)(i : ℕ) : jet (K-f) i x=jet K i x-jet f i x:= score_sub x h g
lemma odd_jet (i : ℕ) (hi : Odd i) : jet f i (-x)=-jet f i x:= by rw [← neg_one_smul ℝ x,jet_smul,hi.neg_one_pow,neg_one_mul]
end raw
section plane
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E]
      {f g K L q : ℝ × E→ℝ} (τ : ℝ) (z : E)

omit τ in
lemma germ_reflected (h : ContDiffAt ℝ ω f 0) : ContDiffAt ℝ ω (f ∘ reflects) 0 := (show ContDiffAt ℝ ω f (reflects 0) from (reflects (E:=E)).map_zero.symm ▸ h).comp 0 (reflects (E:=E)).contDiff.contDiffAt
lemma jet_reflect (h : ContDiffAt ℝ ω f 0) (i) : jet (f ∘ reflects) i (τ,z) = jet f i (τ,-z):= by
  have hz : Prod.mk (0:ℝ) (0:E)=0 := rfl
  rw [←score_jet,←score_jet,← hz,score_reflect,neg_zero]; simpa [neg_zero,hz]

lemma jet_even (h : ContDiffAt ℝ ω f 0)(i : ℕ) : jet (evened f) i (τ,z)=jet f i (τ,z)+jet f i (τ,-z):= by
  rw [evened, add_jet _ _ _ h (germ_reflected h), jet_reflect τ z h]
lemma the_sign (h : ContDiffAt ℝ ω f 0) (he : f= f ∘ reflects) (i : ℕ) : jet f i (τ,-z)=jet f i (τ,z):= by
  rw [←jet_reflect τ z h,← he]

structure Candle (K L f q : ℝ × E→ℝ): Prop where
  deed : Secured f K
  duty : Secured q L
  wafer : q= q ∘ reflects
  wick : L= L ∘ reflects
  wick_margin (v : E) : Held (K-L) 1 v
  heat_margin (v : E) : Held (f-q) 3 v
  temporary (x : ℝ)(v : E) : jet q 2 (x,v) = x^2 + jet q 2 (0,v)

namespace Candle
variable (h : Candle K L f q)
include h
lemma wick_zero : K 0=L 0 := sub_eq_zero.mp (score_base (0,(0:E))|>.symm.trans ((h.wick_margin (0:E) 0 (by decide)).self_of_nhds))
lemma heat (k : ℕ) (he : k<3) : jet f k (τ,z) = jet q k (τ,z) := sub_eq_zero.mp <| Eq.trans
  (sub_jet _ _ (τ,z) h.deed.paid.2.1 h.duty.paid.2.1 k).symm ((h.heat_margin _).each _ (ContDiffAt.sub h.deed.paid.2.1 h.duty.paid.2.1) _ he)
lemma kernel_heat : kernel f (τ,z)=kernel q (τ,z) := by rw [kernel,h.heat _ _ 2 (by decide)]; rfl
lemma kernel_pad : kernel q (τ,z)=Real.exp (-(τ^2))*kernel q (0,z) := by rw [kernel, h.temporary, neg_add,Real.exp_add]; rfl
lemma kernel_change : kernel q (τ,-z)=kernel q (τ,z):= by rw [kernel,kernel,the_sign _ _ h.duty.paid.2.1 h.wafer 2]
lemma paired (k : ℕ) : normTerm K f k (τ,z)+normTerm K f k (τ,-z)=(integrandSeries f K k (τ,z)+integrandSeries f K k (τ,-z))*kernel q (τ,z):= by rw [normTerm,normTerm,add_mul,h.kernel_heat,h.kernel_heat,h.kernel_change]
lemma packed (k : ℕ) : normTerm L q k (τ,z)+normTerm L q k (τ,-z)=(integrandSeries q L k (τ,z)+integrandSeries q L k (τ,-z))*kernel q (τ,z):= by rw [normTerm,normTerm,add_mul,h.kernel_change]

omit h in
private lemma evenLead {g : ℝ × E→ℝ} (h : ContDiffAt ℝ ω g 0){i : ℕ} (he : Held g i z) (hi : Odd i) : jet g (i+1) (τ,z)+jet g (i+1) (τ,-z)=jet g (i+1) (0,z)+jet g (i+1) (0,-z) := by
  rw [←jet_even _ _ h,←jet_even 0 z h]; exact (he.odd_gain h hi).at_lead τ (ContDiffAt.add h (germ_reflected h))
omit h in
private lemma transfer (H J : ℝ×E→ℝ) (hf : ContDiffAt ℝ ω H 0)(hv : ContDiffAt ℝ ω J 0)(hj:J=J∘reflects){i : ℕ}
   (hi : Odd i) (he : ∀ z : E, Held (H-J) i z) :
      let a:= jet J i (τ,z); let b:= jet (H-J) i (0,z);
      jet H i (τ,z) = a+b ∧ jet H i (τ,-z)=a-b := by
   dsimp only
   have hk(v : E): jet H i (τ,v) - jet J i (τ,v)=jet (H-J) i (0,v):= (sub_jet H J (τ,v) hf hv i).symm.trans ((he v).at_lead τ (hf.sub hv))
   have ha:= hk z; have hb:= hk (-z); rw [the_sign τ z hv hj, show ((0,-z):ℝ × E)=-((0,z):ℝ×E) from by simp, odd_jet (H-J) _ _ hi] at hb; constructor <;> linarith
omit h in
private lemma doubleTransfer (H J : ℝ×E→ℝ)(hf : ContDiffAt ℝ ω H 0)(hv : ContDiffAt ℝ ω J 0){i : ℕ}
   (hi : Odd i) (he : ∀ z : E, Held (H-J) i z) :
   jet H (i+1) (τ,z)+jet H (i+1) (τ,-z) = jet J (i+1) (τ,z)+jet J (i+1) (τ,-z) + (jet (H-J) (i+1) (0,z)+jet (H-J) (i+1) (0,-z)):= by
   have h:= evenLead τ z (g:=H-J) (hf.sub hv) (he z) hi; rw [sub_jet _ _ (τ,z) hf hv,sub_jet _ _ (τ,-z) hf hv] at h; linarith
omit h in
private lemma burn (A A' J I G M L L' B' D C : ℝ) : (L - (A + I)*(A' + G)+ C*((1/2:ℝ) * (A' + G)^2-M)) + (J-(A-I)*(A'-G)+C*((1/2:ℝ)*(A'-G)^2-D))=
       L' - A*A'+C*((1/2:ℝ)*A'^2-B') + ((L+J-L')-A*A'+C*((1/2:ℝ)*A'^2-(M+D-B'))) + C*G^2-2*I*G := by ring

lemma matches_zero : normTerm K f 0 (τ,z)=normTerm L q 0 (τ,z):= by rw [normTerm,normTerm,nil_bill,nil_bill,h.wick_zero,h.kernel_heat]
lemma matches_one : normTerm K f 1 (τ,z)+normTerm K f 1 (τ,-z)=normTerm L q 1 (τ,z)+normTerm L q 1 (τ,-z) := by
  rw [h.paired,h.packed,first_bill,first_bill,first_bill,first_bill]
  obtain ⟨a,b⟩:=transfer τ z _ _ h.deed.paid.1 h.duty.paid.1 h.wick (by decide) h.wick_margin
  obtain ⟨c,d⟩:=transfer τ z _ _ h.deed.paid.2.1 h.duty.paid.2.1 h.wafer (by decide) h.heat_margin
  rw [a,b,c,d,h.wick_zero,the_sign τ z h.duty.paid.1 h.wick,the_sign τ z h.duty.paid.2.1 h.wafer]; ring

private lemma matchesInner :
    (integrandSeries f K 2 (τ,z)+integrandSeries f K 2 (τ,-z)) -
      (integrandSeries q L 2 (τ,z)+integrandSeries q L 2 (τ,-z))=
       jet (evened (K-L)) 2 (0,z) - 2*jet (K-L) 1 (0,z)*jet (f-q) 3 (0,z) + L 0 * ((jet (f-q) 3 (0,z))^2 - jet (evened (f-q)) 4 (0,z)) := by
  obtain ⟨a,b⟩:=transfer τ z _ _ h.deed.paid.1 h.duty.paid.1 h.wick (by decide) h.wick_margin; obtain ⟨c,d⟩:=transfer τ z _ _ h.deed.paid.2.1 h.duty.paid.2.1 h.wafer (by decide) h.heat_margin
  have he:= doubleTransfer τ z _ _ h.deed.paid.1 h.duty.paid.1 (by decide) h.wick_margin; have hg:= doubleTransfer τ z _ _ h.deed.paid.2.1 h.duty.paid.2.1 (by decide) h.heat_margin
  simp only [show 1+1=2 from rfl,show 3+1=4 from rfl] at he hg
  rw [second_bill,second_bill,second_bill,second_bill,a,b,c,d,h.wick_zero,the_sign τ z h.duty.paid.1 h.wick 1,the_sign τ z h.duty.paid.2.1 h.wafer 3]
  rw [burn (jet L 1 (τ,z)) _ _ _ _ _ _ (jet L 2 (τ,z)) (jet q 4 (τ,z))]
  rw [he,hg,← jet_even _ _ (show ContDiffAt ℝ ω (f-q) 0 from h.deed.paid.2.1.sub h.duty.paid.2.1),← jet_even _ _ (show ContDiffAt ℝ ω (K-L) 0 from h.deed.paid.1.sub h.duty.paid.1)]; ring
lemma matches_two :
    (normTerm K f 2 (τ,z)+normTerm K f 2 (τ,-z))-(normTerm L q 2 (τ,z)+normTerm L q 2 (τ,-z)) = Real.exp (-(τ^2))*
       ((normTerm K f 2 (0,z)+normTerm K f 2 (0,-z))-(normTerm L q 2 (0,z)+normTerm L q 2 (0,-z))) := by
  rw [h.paired,h.packed,h.paired 0,h.packed 0,←sub_mul,←sub_mul,matchesInner τ z h,matchesInner 0 z h,h.kernel_pad τ z]; ring

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit h in
private lemma doubleMass {H R : ℝ × E → ℝ}(F : Secured H R) (i) :
    (∫ z:E,normTerm R H i (τ,z)+ normTerm R H i (τ,-z) ∂μ)=2*stamp μ R H τ i := by
  rw [stamp_moment]; have ht:= affordability μ _ _ i τ F.spread (F.paid.1.of_le le_top) F.slope
  rw [integral_add ht ht.comp_neg,integral_neg_eq_self (fun z=>normTerm R H i (τ,z))]; ring
lemma WickMass : stamp μ K f τ 0=stamp μ L q τ 0 ∧ stamp μ K f τ 1=stamp μ L q τ 1 ∧
    stamp μ K f τ 2= stamp μ L q τ 2+ Real.exp (-(τ^2))*(stamp μ K f 0 2-stamp μ L q 0 2):= by
  refine ⟨by rw [stamp_moment,stamp_moment]; simp_rw [h.matches_zero], Eq.symm ?_, ?_⟩
  · apply mul_left_cancel₀ (show (2:ℝ)≠0 by norm_num); rw [← doubleMass _ _ h.deed,← doubleMass _ _ h.duty]; simp_rw [h.matches_one]
  have hi {H R : ℝ × E → ℝ}(F : Secured H R)(k : ℝ): Integrable (fun z:E=>normTerm R H 2 (k,z)+normTerm R H 2 (k,-z)) μ :=
    let ht:= affordability μ _ _ 2 k F.spread (F.paid.1.of_le le_top) F.slope; ht.add ht.comp_neg
  have hb x : (∫ z:E,(normTerm K f 2 (x,z)+normTerm K f 2 (x,-z)) -(normTerm L q 2 (x,z)+normTerm L q 2 (x,-z)) ∂μ)=2*(stamp μ K f x 2-stamp μ L q x 2):= by rw [integral_sub (hi h.deed x) (hi h.duty x),doubleMass _ _ h.deed,doubleMass _ _ h.duty, mul_sub]
  have hx:= hb τ; simp_rw [h.matches_two τ,integral_const_mul,hb 0] at hx; linarith
end Candle
end plane
end YM.RGComparison.Core16.Therm
