import YM.GapsContact.Series.Loft
import YM.Analysis.Polydisc
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
/-!
# Limit extraction from successive zoom errors. All analytical costs are H-independent!

In `Collapse`, parameter n is the dyadic scale sample, q the extrapolation grade.
At high orders estimates must be maintained along the same samples for the putative
Euclidean input, not involving analytic input. Successive increments sufficient since the dyadic
samples have the uniform price levels needed for summability. Order-independent output G on the
whole open set. At EACH compact set a sufficiently high extrapolation grade is needed -- no single
q works all the way to the boundary modulus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Pattern
open Function Set Filter Metric
open scoped Topology Classical BigOperators ContDiff
variable {ι Ω:Type*}{E H:Type}[NormedAddCommGroup E][NormedAddCommGroup H][CompleteSpace H]
variable {F:ℕ→E→ H}{s K U:Set E}

def wage (n:ℕ):= (2:ℝ)⁻¹^n
lemma wage_pos (n):0<wage n:=by unfold wage; positivity
lemma wage_short (n): wage n≤1:= pow_le_one₀ (by norm_num) (by norm_num)
lemma wage_limit : Tendsto wage atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma wage_add (m n):wage (m+n)=wage m*wage n:= pow_add ..
-- convergence with geometric rate *_differences*. convenient for boundary estimates too
omit [NormedAddCommGroup E] in
lemma cadence (h:TagPrice atTop (fun i x => F (i+1) x - F i x) s wage): ∃ H:E→H, TendstoUniformlyOn F H atTop s:=by
   obtain ⟨C,hC,h⟩:=h; obtain ⟨N,h⟩:= eventually_atTop.mp h
   let L(n:ℕ):= F (n+N)
   have hp(x)(hx:x∈s)(n:ℕ):dist (L n x) (L n.succ x)≤(C*wage N)*wage n:=by
      have he : (C*wage N)*wage n=C*wage (n+N):=by rw [wage_add]; ring
      rw [he,dist_comm,dist_eq_norm]; change ‖F _ _- F _ _‖ ≤ _; rw [show n.succ+N=n+N+1 by omega]; exact h _ (Nat.le_add_left ..) x hx
   have he(x)(hx:x∈s):∃ y:H,Tendsto (fun n:ℕ=> F n x) atTop (𝓝 y):=by
      obtain ⟨y,hy⟩:= cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ (show (2:ℝ)⁻¹<1 by norm_num) (hp x hx)); exact ⟨y,(tendsto_add_atTop_iff_nat _).mp hy⟩
   let g(x:E):= if h:x∈s then (he x h).choose else 0
   have ht(x)(hx:x∈s): Tendsto (fun i=>L i x) atTop (𝓝 (g x)) :=by unfold g; rw [dif_pos hx]; exact (tendsto_add_atTop_iff_nat N).mpr (he x hx).choose_spec
   have hh(x)(hx:x∈s)(n:ℕ):dist (g x) (F (n+N) x) ≤ C*wage N*wage n/(1-2⁻¹):=by rw[dist_comm]; exact dist_le_of_le_geometric_of_tendsto _ _ (show (2:ℝ)⁻¹<1 by norm_num) (hp x hx) (ht x hx) n
   refine ⟨g,tendstoUniformlyOn_iff.mpr ?_⟩; intro ε hε
   obtain ⟨K,hK⟩:=eventually_atTop.mp ((show Tendsto (fun n=> C*wage N*wage n/(1-2⁻¹)) atTop (𝓝 0) from by simpa using ((wage_limit.const_mul (C*wage N)).div_const (1-2⁻¹))).eventually_lt_const hε)
   filter_upwards [eventually_ge_atTop (K+N)] with i hi x hx
   obtain ⟨i,rfl⟩:=Nat.exists_eq_add_of_le (show N ≤ i by omega)
   rw [Nat.add_comm N]; exact (hh x hx i).trans_lt (hK i (by omega))

variable [NormedSpace ℂ E] [ProperSpace E] [FiniteDimensional ℂ E] -- Proper redundant?
variable [NormedSpace ℂ H] [FiniteDimensional ℂ H]

lemma rhythm {z:E}{r:ℝ}(hr:0<r)(h:TagPrice atTop (fun i x => F (i+1) x - F i x) (ball z r) wage) (ht:∀ᶠ i in atTop,AnalyticOnNhd ℂ (F i) (ball z r)){G:E→H}(hg:∀ x∈ball z r,Tendsto (fun i=> F i x) atTop (𝓝 (G x))) : AnalyticAt ℂ G z:=by
   have hh : Scoped atTop (fun i x => F (i+1) x-F i x) (ball z r) wage:= fun _ _ hx=>h.parent hx
   have hH : ∀ᶠ i:ℕ in atTop,∀ x∈ball z r, fderiv ℂ (fun x=> F (i+1) x - F i x) x= fderiv ℂ (F (i+1)) x- fderiv ℂ (F i) x ∧ AnalyticAt ℂ (fun x=> F (i+1) x - F i x) x:=by
     filter_upwards [(tendsto_add_atTop_nat 1).eventually ht,ht] with i hi hk x hx; have he:AnalyticAt ℂ (F (i+1)) x:=hi x hx; have hw:=hk x hx; exact ⟨fderiv_fun_sub he.differentiableAt hw.differentiableAt, he.sub hw⟩
   let V:= closedBall z (r/2); let D(n:ℕ):= fderiv ℂ (F n); have hu:V⊆ball z r:= closedBall_subset_ball (half_lt_self hr)
   obtain ⟨g,hg'⟩:= cadence (F:=D) ((hh.diff (Eventually.of_forall fun i=>(wage_pos i).le) isOpen_ball (hH.mono fun i h x hx=>(h x hx).2) V (isCompact_closedBall ..) hu).congr (hH.mono fun i h x hx=>(h x (hu hx)).1))
   let S:= ball z (r/2); obtain ⟨N,hN⟩:= eventually_atTop.mp ht; let L(i:ℕ):=F (i+N)
   have hp: TendstoUniformlyOn (fderiv ℂ ∘ L) g atTop S:=(fun u hu=> (tendsto_add_atTop_nat N).eventually ((hg'.mono ball_subset_closedBall) u hu))
   have hv(x)(hx:x∈S):HasFDerivAt G (g x) x:= hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_ball hp.tendstoLocallyUniformlyOn (fun n=> (hN (n+N) (by omega)).differentiableOn.mono (ball_subset_closedBall.trans hu)) (fun x hx=> (tendsto_add_atTop_iff_nat N).mpr (hg x (hu (ball_subset_closedBall hx)))) hx
   apply YM.PolyDisc.finiteD; exact Eventually.mono (show ∀ᶠ x in 𝓝 z,x∈S from ball_mem_nhds z (half_pos hr)) fun x hx=>(hv x hx).differentiableAt

-- consumer for approximate extrapolations, local errors have already been propagated
variable {A:ℕ→ℕ→E→H}
structure River (A:ℕ→ℕ→ E→H)(U:Set E) : Prop where
   hol : ∀ᶠ q:ℕ in atTop,∀ᶠ i:ℕ in atTop,AnalyticOnNhd ℂ (A q i) U
   pace : ∀ K:Set E, IsCompact K→K⊆U→∀ᶠ q in atTop,TagPrice atTop (fun i x=> A q (i+1) x - A q i x) K wage
   kiss : ∀ K:Set E, IsCompact K→K⊆U→∀ᶠ b:ℕ × ℕ in atTop,TagPrice atTop (fun i x=> A b.1 i x - A b.2 i x) K wage
variable (h: River A U)
include h
-- pair cofinal high-order estimates; local choices of limits eventually agree
-- (uniform on ANY given compact)
omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ H] [ProperSpace E] in
lemma River.held (hq:IsCompact K)(hp:K⊆U):∃ F:E→ H,∀ᶠ q in atTop,∀ x∈K,Tendsto (fun i=> A q i x) atTop (𝓝 (F x)):=by
  obtain ⟨q,hq⟩:= eventually_atTop.mp (h.pace K hq hp)
  obtain ⟨m,hm⟩:= eventually_atTop.mp (h.kiss K (by assumption) hp)
  let Q:=q+m.2; obtain ⟨F,hF⟩:= cadence (hq Q (Nat.le_add_right ..))
  refine ⟨F,?_⟩; filter_upwards [eventually_ge_atTop m.1] with t ht x hx
  have hT:= (hm (t,Q) (show m≤(t,Q) from ⟨ht,Nat.le_add_left ..⟩)).tends wage_limit x hx; simpa using (hT.add (hF.tendsto_at hx))
lemma River.gleam (hU:IsOpen U): ∃ F:E→H,AnalyticOnNhd ℂ F U ∧ ∀ K:Set E,IsCompact K→K⊆U→∀ᶠ q in atTop,∀ x∈K,Tendsto (fun i=> A q i x) atTop (𝓝 (F x)) :=by
  choose W hW using fun x:U=> h.held (isCompact_singleton (x:=x.val)) (Set.singleton_subset_iff.mpr x.property)
  let F(x:E):= if h:x∈U then W ⟨x,h⟩ x else 0
  have he(x)(hx:x∈U): ∀ᶠ q in atTop,Tendsto (fun i=> A q i x) atTop (𝓝 (F x)) := by unfold F; rw [dif_pos hx]; exact (hW ⟨x,hx⟩).mono fun i ht=> ht x (Set.mem_singleton _)
  have ht(K)(hk:IsCompact K)(h₀:K⊆U):∀ᶠ q in atTop,∀ x∈K,Tendsto (fun i=> A q i x) atTop (𝓝 (F x)) := by
     obtain ⟨B,hB⟩:= h.held hk h₀; have hu : EqOn F B K:=by
        intro x hx; obtain ⟨i,p,q⟩:= ((he x (h₀ hx)).and hB).exists; exact tendsto_nhds_unique p (q x hx)
     exact hB.mono fun q hp x hx=> (hu hx).symm ▸ hp x hx
  refine ⟨F,fun z hz=>?_,ht⟩
  obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp (hU.mem_nhds hz);
  let K:=closedBall z (r/2); have hk:IsCompact K:= isCompact_closedBall ..; have h₀:= (closedBall_subset_ball (half_lt_self hr)).trans hR
  obtain ⟨q,hA,hB,hC⟩:= (h.hol.and ((h.pace K hk h₀).and (ht _ hk h₀))).exists
  exact rhythm (half_pos hr) (hB.parent ball_subset_closedBall) (hA.mono fun i h=> h.mono (ball_subset_closedBall.trans h₀)) (fun x hx=> hC x (ball_subset_closedBall hx))
end YM.GapsContact.Pattern
