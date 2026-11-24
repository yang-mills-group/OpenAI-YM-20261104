import YM.Contacts.Power.Costs
/-!
# Flexible cost inequalities

Allow tightening rates through continuous dependence, proximity perturbations at finer scales, later selections. Do not require cut laws stronger than filter membership.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Power.Pace
open Filter Function
open scoped Topology BigOperators
variable {α β X Y Z:Type*}{P:Pace α}{a b c:ℝ}{f g:α→ℝ}{x y:α→X}
lemma Longer.decrease (h:P.Longer a f)(hh:b≤a): P.Longer b f:= fun c hv=>h c (hv.trans_le hh)
lemma Longer.move (h:P.Longer a f)(hh:f ≤ᶠ[P.net] g): P.Longer a g:=fun c hc=> ((h _ hc).and hh).mono fun i hi=>hi.1.trans hi.2
lemma Longer.congr (h:P.Longer a f)(hh:f =ᶠ[P.net] g): P.Longer a g:= h.move hh.le
lemma Longer.strict (h:P.Longer a f)(hg:P.Priced b g)(he:b<a): ∀ᶠ i in P.net,g i < f i:= by
   obtain ⟨v,hv,hx⟩:=exists_between he; obtain ⟨t,ht,hg'⟩:= exists_between hx
   filter_upwards [hg.upper hv,h t hg',P.rate_gt ht] with i hi hp hh; linarith
lemma Longer.pos (h:P.Longer a f): ∀ᶠ i in P.net,0<f i:=(h (a-1) (by linarith)).mono fun i hi=> lt_of_lt_of_le (P.rate_pos _ _) hi
lemma Longer.between {y:α→ℝ}(h:P.Longer a f)(hx:P.Priced b g)(he:b<a)(ht:∀ᶠ i in P.net,f i≤ y i+g i): P.Longer a y:= by
   intro c hc
   filter_upwards [h.strict ((P.rate_grade c).priced.add hx) (max_lt hc he),ht] with i hi hh; linarith
lemma Longer.inv_Priced (h:P.Longer a f): P.Priced (-a) (fun i=> (f i)⁻¹) := by
    intro b hb; have ht: - b<a:= by linarith
    filter_upwards [h (-b) ht,h.pos] with i hi he
    rw [Real.norm_of_nonneg (inv_nonneg.mpr he.le)]
    have hy:=inv_anti₀ (P.rate_pos (-b) i) hi -- check
    simpa [rate,Real.exp_neg,neg_mul] using hy
lemma Rating.less (h:P.Rating a f)(hg:P.Rating b g)(hb:a<b): ∀ᶠ i in P.net,f i < g i:= hg.longer.strict h.priced hb

lemma Priced.shift [Norm X](h:P.Priced a x)(he:a=b): P.Priced b x:= he ▸ h
lemma Priced.capped_by [Norm X](h:P.Priced a f)(he:∀ᶠ i in P.net,‖x i‖ ≤ f i): P.Priced a x:= fun b hb=> (he.and (h.upper hb)).mono fun i hi=> hi.1.trans hi.2
lemma Priced.latitude [Norm X]{g:β→ℝ}{τ:Filter β}[τ.NeBot](h:∀ᶠ i in τ,P.Priced (g i) x)(he:Tendsto g τ (𝓝 a)) : P.Priced a x:= by intro c hc; obtain ⟨i,hi,hx⟩:= (h.and (he.eventually (gt_mem_nhds hc))).exists; exact hi c hx
lemma Priced.latitude0 [Norm X]{g:ℝ→ℝ}(h:∀ᶠ i in 𝓝[>] 0,P.Priced (g i) x)(he:ContinuousAt g 0) : P.Priced (g 0) x:= Priced.latitude h he.continuousWithinAt
lemma Priced.with_norm [SeminormedAddCommGroup X][SeminormedAddCommGroup Y] {y:α→Y} (h:P.Priced a x)(B:ℝ)(he:∀ᶠ i in P.net,‖y i‖ ≤ B* ‖x i‖): P.Priced a y:= by simpa only [zero_add] using (((Priced.constants (P:=P) B).mul h.abs_cost).capped_by he) -- edit
lemma Priced.maps {H:Type*}[NontriviallyNormedField H] [SeminormedAddCommGroup X][SeminormedAddCommGroup Y]
    [NormedSpace H X][NormedSpace H Y] (L:X →L[H] Y) (h:P.Priced a x): P.Priced a (L ∘ x):= h.with_norm ‖L‖ (Eventually.of_forall fun i=> L.le_opNorm _)
lemma Priced.product [NontriviallyNormedField X](t:Finset β)(f:β→α→X)(g:β→ℝ)(h:∀ i∈t,P.Priced (g i) (f i)): P.Priced (∑ i∈t,g i) fun i=> ∏ j∈t,f j i:=by
   classical
   induction t using Finset.induction_on with
   | empty=>simpa using (constants (P:=P) (1:X))
   | insert i t hi ih=> simp_rw [Finset.sum_insert hi,Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).mul (ih (fun _ hx=>h _ (Finset.mem_insert_of_mem hx)))
/-- Uniform versions are an admissible use of filter pricing, including velocity in valuation without any compact selector assumptions. -/
lemma Priced.holdsFor [Norm X] [Nonempty β](t:α→Set β)(f:α→β→X)
    (he:∀ᶠ i in P.net,(t i).Nonempty)
    (H:∀ y:α→β,(∀ᶠ i in P.net, y i ∈ t i)→ P.Priced a (fun i=> f i (y i))) :
    ∀ b:ℝ,a<b→ ∀ᶠ i in P.net, ∀ y∈ t i, ‖f i y‖ ≤ P.rate b i :=by
   classical
   intro b hb
   let bad (i:α)(y:β):= y∈t i ∧ P.rate b i< ‖f i y‖
   let y (i:α):= if h:∃ y,bad i y then h.choose else if h:(t i).Nonempty then h.choose else Classical.arbitrary β
   have ht: ∀ᶠ i in P.net,y i∈ t i:= he.mono fun i hi=>by unfold y; rw [dif_pos hi]; split; rename_i h; exact h.choose_spec.1; exact hi.choose_spec
   filter_upwards [H y ht b hb] with i hi y' hx
   by_contra! hk
   have hv: ∃ y,bad i y:=⟨y',hx,hk⟩
   simp only [y,dif_pos hv] at hi
   exact hv.choose_spec.2.not_ge hi
end YM.Contacts.Power.Pace
