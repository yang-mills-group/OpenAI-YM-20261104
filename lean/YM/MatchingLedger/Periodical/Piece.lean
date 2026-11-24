import YM.MatchingLedger.Periodical.Survey

/-!
# Schwinger-Dyson patch integrand on the full theory

Measurable and exact; no assertion that *actual log density* is globally analytic or has
perturbative jets. Before dropping weights on χ complement, keep term `div_shutter`.
No unconditioned expectation claims here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Periodical
open Function Filter Lattice RG Wilson Tree Pressure Pressure.Stores Precision Push.Uniform
open PatchArea Action Books MvPolynomial Gazette Set Metric MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius ContDiff Finset
variable {c f : Side}{G : Gauge}{S : StepData c f} (F : Forest S.ratio) (s : S.Choices)
    (A : ChartRatio G) (Y : Chip (Page G c)) (t r : ℝ) (R : Support c) (i : Needle F G) (p : Poly (Needle F G))
local notation "I" => Sum.inl i
local notation "D" => depot F (Sum.inl i)

section preparable
variable {ι : Type} [Fintype ι][DecidableEq ι]

lemma highlighted {n : ℕ}{f : Chip ι→ℝ}{x : Chip ι}{u : ℝ}(h : Allows (n+1) f x u)(i : ι) : Allows n (Books.derivative f i) x u:=by
  let q : (Chip ι→L[ℝ]ℝ)→L[ℝ]ℝ := ContinuousLinearMap.apply ℝ ℝ (axis i)
  have he : Allows n (fderiv ℝ f) x u := by
    refine ⟨h.analytic.fderiv_right le_top,fun _ hk=>?_⟩; rw [norm_iteratedFDeriv_fderiv]; exact h.norm_le _ (Nat.succ_le_succ hk)
  have hx := Allows.linear q (K:=1) he (q.opNorm_le_bound zero_le_one fun v=> (v.le_opNorm (axis i)).trans (by rw [one_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_axis i)))
  rw [one_mul] at hx; exact hx
lemma neg_allowed {n : ℕ} {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{v : E→ℝ}{u : ℝ} (h:Allows n v x u) : Allows n (fun x=> -v x) x u:= by
  have he := h.smul (-1:ℝ); simpa only [abs_neg,abs_one,one_mul,neg_one_smul] using he
end preparable

def cost (P : Patch)(v t : ℝ) : ℝ := park (belt P) * ((t^2+1)*v)
lemma cost_nn (P : Patch){v t : ℝ}(hv:0≤v): 0≤cost P v t := by unfold cost; positivity [park_nn (belt P)]

section derive
variable {A} {n:ℕ}(H : Budget G A n)
local notation "B" => H.income S.patch S.kernel
variable {X : Chip (Meter F G)} (h:‖X‖≤H.space S.patch S.kernel)

include h in
lemma sew : Allows n (sat F s A t i) X (cost S.patch B t):= by
  have hB:= H.income_one S.patch S.kernel
  let M:= H.income S.patch S.kernel; let a:=depot F (Sum.inl i)
  let f(v : Chip (Meter F G)):= ∑ z∈a, dues S F G s z v; let ξ(v:Chip (Meter F G)):=∑ z∈a, salary F A z v
  have he0 : sat F s A t i=(fun x=>t^2*f x+ -ξ x):= by ext x; unfold sat f ξ a; ring
  rw [he0]
  have hp := ((allows_sum (s:=a) (fun i _=> H.duty F h s i)).smul (t^2)).add (neg_allowed (allows_sum (s:=a) (fun i _=> H.issued F h i)))
  apply hp.mono; rw [Finset.sum_const,nsmul_eq_mul,abs_of_nonneg (sq_nonneg _)]
  have ha : (a.card:ℝ)≤ park (belt S.patch):=by unfold park; exact_mod_cast mag (atlas F I) (belt S.patch)
  exact le_trans (b:= (a.card:ℝ)*((t^2+1)*B)) (le_of_eq (by ring)) (mul_le_mul_of_nonneg_right ha (by positivity [zero_le_one.trans hB]))
end derive

def distill (v : Chip (Meter F G)) := Books.derivative (sat F s A t i) (Sum.inl i) v
lemma sample {A} {n:ℕ} (H : Budget G A n){X : Chip (Meter F G)}(h:‖X‖≤H.space S.patch S.kernel) :
    Allows (n-1) (distill F s A t i) X (cost S.patch (H.income S.patch S.kernel) t):=by
  have he:= H.nn; exact highlighted ((sew F s t i H h).order (show n-1+1≤n from by omega)) I

def run (U : F.Slice G) := read (t • crawl F A U) p
def scatter (U : F.Slice G) := shutter G r (boxLog A (U i.1))
def arrow (U : F.Slice G) := fderiv ℝ (shutter G r) (boxLog A (U i.1)) (pluck (G:=G) i.2)
def radix (U : F.Slice G) := scatter F A r i U * (run F A t p U * (t⁻¹*distill F s A t i (column F A Y R U)) - run F A t (pderiv i p) U)
                                  - t⁻¹ * arrow F A r i U * run F A t p U
def milled := (fieldTest F R r).indicator (radix F s A Y t r R i p)
lemma run_pass : Envelope (run F A t p) := envelope_repaired (L:=fun U=>t • crawl F A U) (coordinated F A t) (smooth_read p).continuous
lemma spot : Envelope (fun U:F.Slice G=> boxLog A (U i.1)) :=
  ⟨(gauge_log A).comp (measurable_pi_apply _),1,fun _=> range_bound A _⟩
lemma scatter_pass : Envelope (scatter F A r i) := envelope_repaired (X:=shutter G r) (L:=fun U:F.Slice G=>boxLog A (U i.1)) (spot F A i) (smooth_cut G r).continuous
lemma arrow_pass : Envelope (arrow F A r i) := by
  exact envelope_repaired (X:=fun x=>fderiv ℝ (shutter G r) x (pluck (G:=G) i.2)) (L:=fun U:F.Slice G=>boxLog A (U i.1)) (spot F A i) ( ((smooth_cut G r).continuous_fderiv (by simp)).clm_apply continuous_const)
lemma milled_pass {A} {n:ℕ} (H : Budget G A n) (hr:r ≤ dial A) (hY:‖Y‖≤r) (hh:r ≤ H.space S.patch S.kernel): Envelope (milled F s A Y t r R i p):=by
  let f:= distill F s A t i; let X:= closedBall (0:Chip (Meter F G)) (H.space S.patch S.kernel)
  have hx(v) (he:v∈X) := sample F s t i H (mem_closedBall_zero_iff.mp he)
  have hg:=close_env (s:=X) isClosed_closedBall.measurableSet (fun v h=>(hx v h).analytic.continuousAt.continuousWithinAt) (cost_nn S.patch (zero_le_one.trans (H.income_one ..))) (fun v h=>(hx v h).value)
  let k(U:F.Slice G):= column F A Y R U
  let g:= X.indicator f
  let q (U:F.Slice G):= scatter F A r i U*(run F A t p U*(t⁻¹*g (k U))-run F A t (pderiv i p) U)- t⁻¹*arrow F A r i U *run F A t p U
  let Z:= fieldTest (G:=G) F R r
  have hP : milled F s A Y t r R i p=Z.indicator q:=by
    ext1 v; unfold milled; by_cases hv:v∈Z
    · rw [indicator_of_mem (s:=Z) hv,indicator_of_mem hv]; unfold q radix; rw [show g (k v)=f (k v) from indicator_of_mem (mem_closedBall_zero_iff.mpr ((column_range F Y hr hY hv).trans hh)) _]
    rw [indicator_of_notMem (s:= Z) hv,indicator_of_notMem hv]
  have hu : Envelope q:=
    envelope_sub ((scatter_pass F A r i).mul (envelope_sub ((run_pass F A t p).mul ((Envelope.const _).mul (envelope_comp hg (script F A Y R)))) (run_pass F A t _))) (((Envelope.const _).mul (arrow_pass F A r i)).mul (run_pass F A t p))
  rw [hP]; exact Envelope.piece (p:=fun x=> x∈Z) (sense F hr) hu (Envelope.const 0)

lemma envelope_sector {A} {n:ℕ} (H : Budget G A n)(hr:r ≤ dial A)(hY:‖Y‖ ≤ r)(hh:r ≤ H.space S.patch S.kernel): Envelope (milled F s A Y t r R i p) := milled_pass F s Y t r R i p H hr hY hh

end YM.MatchingLedger.Periodical
