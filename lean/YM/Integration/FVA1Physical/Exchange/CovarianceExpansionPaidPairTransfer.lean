import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPairDetectorPrice
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFundedRegularWindow

/-! Insert the whole registered actual regular residual into the unlike-law
two-particle comparison, retaining the full original normalization in the
exceptional invoice. All its fields, including previously failed masks and
the correlated three-field test, are admitted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Lattice RG Wilson RoseCut RoseCut.FiledAction Replica
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{X:Type*}[MeasurableSpace X]
local notation "Fld" => Config G n

def residualCost (p:BudgetPoint)(e:Edge (Site n))(ε:ℝ):ℝ:=
  ((halo 8 {e.1}).card:ℝ)*(Push.GridApprox.Attach.hitConstant p.B*ε)

private theorem cap_var (s d:ℝ):cap (s-d) ≤ cap s+|d|/2:=by
  unfold cap
  by_cases large:1 ≤ |s|/2
  · rw [min_eq_left large];exact (min_le_left ..).trans (le_add_of_nonneg_right (by positivity))
  rw [min_eq_right (le_of_not_ge large)]
  exact (min_le_right ..).trans (by linarith only [abs_sub s d])

/-- For any one common measurable pair of positive submitted and reference
densities, restore the actual masked smooth remainder on the initial side.
A true charged EBound pays every field, independent of all marked test choices.
The bad pair remains a subset of the bad event from the uncorrected comparison,
but its price is in the genuinely corrected true × independent measure. -/
theorem paid_regular_pair (p:BudgetPoint)(e:Edge (Site n))(outside:Fld)(link:X→G.El)(lm:Measurable link)
    (μ:Measure X)[IsFiniteMeasure μ](R:Activities G n){ε ξ:ℝ}(valid:R.Valid p ε ξ)
    (width:1 ≤ p.supportExponent){k a b:X→ℝ}(ke:Envelope k)(ae:Envelope a)(be:Envelope b)
    (kn:∀x,0 ≤ k x)(ap:∀x,0 < a x)(bp:∀x,0 < b x)(kp:0 < ∫x,k x ∂μ)
    (c t:ℝ)(h:Fin 3→X→ℂ)(eh:∀i,Envelope (h i))(L:Fin 3→ℝ)(ln:∀i,0 ≤ L i)(cash:∀i x,‖h i x‖ ≤ L i):
    let U:=fun x=>update outside e (link x)
    let a':=fun x=>Real.exp (c-R.additive p (U x))*a x
    let u:=fun x=>k x*a' x;let v:=fun x=>k x*b x
    let r:=fun x=>Real.log (a x)-Real.log (b x);let r':=fun x=>Real.log (a' x)-Real.log (b x)
    let E:=pairExcess r t;let t':=min 1 (max 0 t+residualCost p e ε);let E':=pairExcess r' t'
    let F:=physicalProperRows h;let A:=fun i=>FrozenRead.meanOn μ u (F i);let B:=fun i=>FrozenRead.meanOn μ v (F i)
    let z:=∫x,u x ∂μ;let q:=∫x,v x ∂μ
    MeasurableSet E' ∧ E'⊆E ∧
      ‖properThree A-properThree B‖ ≤ 26*L 0*L 1*L 2*(t'+(∫s in E',(cost u v s+cost v u s) ∂μ.prod μ)/(2*z*q)):=by
  intro U a' u v r r' E t' E' F A B z q
  have um:Measurable U:=by
    apply measurable_pi_lambda;intro i
    by_cases eq:i=e
    · subst i;simpa only [U,update_self] using lm
    simpa only [U,update_of_ne eq] using (measurable_const (a:=outside i):Measurable (fun _:X=>outside i))
  have ereg:Envelope (fun x=>R.additive p (U x)):=by
    obtain ⟨B,hb⟩:=(Activities.ESeries valid).bound
    exact ⟨(R.E_measurable valid.regular).comp um,B,fun x=>hb (U x)⟩
  have ea':Envelope a':=(((Envelope.const c).add ereg.neg).exp.mul ae)
  have pa'(x:X):0 < a' x:=mul_pos (Real.exp_pos _) (ap x)
  have rm':Measurable r':=ea'.meas.log.sub be.meas.log
  have change(x:X):r' x=c-R.additive p (U x)+r x:=by
    dsimp only [r',a',r];rw [Real.log_mul (Real.exp_ne_zero _) (ap x).ne',Real.log_exp];ring
  have one(x y:X):|R.additive p (U x)-R.additive p (U y)| ≤ 2*residualCost p e ε:=by
    have keep:Kept (U x) (U y) {e.1}:=by
      intro l hl;have ne:l≠e:=fun eq=>hl (eq ▸ Finset.mem_singleton_self _)
      simp only [U,update_of_ne ne]
    exact (funded_edit p width valid _ _ keep).trans_eq (by dsimp only [residualCost];ring)
  have n0:0 ≤ residualCost p e ε:=by
    have base:=funded_edit (L:={e.1}) p width valid outside outside (fun _ _=>rfl)
    simp only [sub_self,abs_zero] at base
    dsimp only [residualCost];linarith only [base]
  have paid(x y:X):cap (r' x-r' y) ≤ cap (r x-r y)+residualCost p e ε:=by
    rw [change,change,show c-R.additive p (U x)+r x-(c-R.additive p (U y)+r y)=
      (r x-r y)-(R.additive p (U x)-R.additive p (U y)) by ring]
    have half:|R.additive p (U x)-R.additive p (U y)|/2 ≤ residualCost p e ε:=by linarith only [one x y]
    exact (cap_var ..).trans (add_le_add (le_refl _) half)
  have positive {w:X→ℝ}(ew:Envelope w)(pw:∀x,0 < w x):0 < ∫x,k x*w x ∂μ:=by
    apply (integral_pos_iff_support_of_nonneg (fun x=>mul_nonneg (kn x) (pw x).le) ((ke.mul ew).integrable μ)).2
    have equal:Function.support (fun x=>k x*w x)=Function.support k:=by
      ext x;change k x*w x≠0 ↔ k x≠0
      exact ⟨left_ne_zero_of_mul,fun h=>mul_ne_zero h (pw x).ne'⟩
    rw [equal];exact (integral_pos_iff_support_of_nonneg kn (ke.integrable μ)).1 kp
  refine ⟨pair_excess_borel rm' t',?_,?_⟩
  · rintro ⟨x,y⟩ ex
    by_contra missing
    have inside:cap (r x-r y) ≤ t:=le_of_not_gt missing
    apply (not_lt_of_ge ?_) (show t' < cap (r' x-r' y) from ex)
    exact le_min (min_le_left ..) ((paid x y).trans (add_le_add (inside.trans (le_max_right ..)) (le_refl _)))
  have t0:0 ≤ t':=le_min zero_le_one (add_nonneg (le_max_left ..) n0)
  exact pair_excess_seven μ ke.meas ea'.meas be.meas kn pa' bp rm' 0 (fun _=>by simp only [add_zero];rfl)
    t' t0 h eh L ln cash ((ke.mul ea').integrable μ) ((ke.mul be).integrable μ) (positive ea' pa') (positive be bp)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
