import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFullPhysicalMask
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionTwoSidedGauge

/-! Conditional comparison of the fully masked and unmasked filed actions on
one fixed-exterior physical bond. The same arbitrary nonnegative gas and held
kernel stay inside both integrals; no inverse price for that gas is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function Set MeasureTheory Lattice RG Wilson Precision WilsonStartup RoseCut
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{ι:Type*}
local notation "Fld" => Config G n

/-- Local regular contribution to the signed connected three-field reading
even with interacting remote failures. Positive masses are the actual two
normalizations, and there is one undivided tail from each positive law. -/
theorem full_action_cold_hearing (p:BudgetPoint)(c:Clip)(P:PathData G){σ C Λ σ' C':ℝ}
    (pay:P.Bounds c σ C Λ)(licensed:Decent c p)(β:ℝ)(rank:ι→ℕ)
    (A:(v:ι)→ℕ→Atom G (rank v))(coef:ι→ℝ)(L:List ι)(sp:0<σ')
    (stock:∀v∈L,SumBudget (fun i=>(A v i).budget σ') C')
    (reset:∀v∈L,∀h:rank v=2,zeroContact (h ▸ A v))
    (e:Edge (Site n))(D:ℕ)(outside:Fld){X:Type*}[MeasurableSpace X](μ:Measure X)[SFinite μ]
    (link:X→G.El)(B:Set X)(measB:MeasurableSet B)
    (cold:∀x∈B,Healthy p.threshold (halo (D+p.B) {e.1}) (update outside e (link x)))
    (joint:X→ℝ)(jb:Measurable joint)(jp:∀x,0≤joint x)
    (h:Fin 3→X→ℂ)(env:∀i,Envelope (h i))(M:Fin 3→ℝ)(mn:∀i,0≤M i)(bound:∀i x,‖h i x‖≤M i):
    let U:=fun x=>update outside e (link x)
    let f:=fun x=>fullPhysical p c P β rank A coef L (U x)
    let w:=fun x=>fullIndependent c P β rank A coef L (U x)
    let a:=fun x=>joint x*Real.exp (-f x);let b:=fun x=>joint x*Real.exp (-w x)
    let F:=physicalProperRows h;let actual:=fun i=>FrozenRead.meanOn μ a (F i)
    let uncut:=fun i=>FrozenRead.meanOn μ b (F i)
    let rate:=min 1 ((pathCash σ C Λ β D+passengerCash rank σ' C' coef D L)/2)
    let z:=∫x,a x ∂μ;let q:=∫x,b x ∂μ
    Measurable f → Measurable w → Integrable a μ → Integrable b μ → 0<z → 0<q →
    0<(∫x in B,a x ∂μ) → 0<(∫x in B,b x ∂μ) →
    ‖properThree actual-properThree uncut‖≤(26*M 0*M 1*M 2)*
      (((∫x in B,a x ∂μ)/z)*rate+(∫x in Bᶜ,a x ∂μ)/z+(∫x in Bᶜ,b x ∂μ)/q):=by
  intro U f w a b F actual uncut rate z q fm wm ai bi zp qp za qb
  let t:=pathCash σ C Λ β D+passengerCash rank σ' C' coef D L
  have room:B.Nonempty:=by
    by_contra! empty
    rw [empty] at za;simp at za
  have oscillate(x:X)(hx:x∈B)(y:X)(hy:y∈B):|(f x-w x)-(f y-w y)|≤t:=by
    have same(edge:Edge (Site n))(he:edge≠e):U x edge=U y edge:=by simp only [U,update_of_ne he]
    have after:e.1∉flags p.threshold (U y):=Finset.disjoint_left.mp (cold y hy)
      (halo_subset _ _ (Finset.mem_singleton_self _))
    exact complete_physical_mask_price p c P pay licensed β rank A coef L sp stock reset e D _ _ same (cold x hx) after
  obtain ⟨x,hx⟩:=room
  have tn:0≤t:=(abs_nonneg _).trans (oscillate x hx x hx)
  have rn:0≤rate:=le_min zero_le_one (div_nonneg tn (by norm_num))
  apply full_two_tail_seven (μ:=μ) B measB jb (Real.measurable_exp.comp fm.neg) (Real.measurable_exp.comp wm.neg)
    jp (fun _=>Real.exp_pos _) (fun _=>Real.exp_pos _) rate rn h env M mn bound ai bi zp qp za qb
  intro x hx y hy
  simp only [Function.comp_apply,Pi.neg_apply,Real.log_exp,Replica.cap]
  apply min_le_min_left 1
  rw [show -f x- -w x-(-f y- -w y)=-((f x-w x)-(f y-w y)) by ring,abs_neg]
  exact div_le_div_of_nonneg_right (oscillate x hx y hy) (by norm_num)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
