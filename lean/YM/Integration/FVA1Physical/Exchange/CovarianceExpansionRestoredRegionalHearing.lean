import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPaidPairTransfer
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPhysicalRegionalHearing
import YM.Push.BETA_TRANSPORT.Noise

/-! The full regulated two-vacuum hearing, including the genuine Haar
one-bond conditional, the measured blocking kernel, the signed complete
physical regular remainder, and the common filed geometric/passenger bank. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Lattice RG Wilson Precision WilsonStartup RoseCut
open Marked Marked.RemoteRoster YM.Integration.FVA1Physical.Replica
open scoped Classical BigOperators
variable {G:Gauge}{c n:Side}{ι:Type*}
local notation "Fld" => Config G n

/-- A cost stated in actual one-bond Haar units. The signed deficit in
the numerator is taken only on a localized exceptional pair, after
normalizing by both real partition functions. -/
def sevenFare (μ:Measure G.El)(u v:G.El→ℝ)(h:Fin 3→G.El→ℂ)(L:Fin 3→ℝ)(E:Set (G.El×G.El))(t:ℝ):Prop:=
  let F:=physicalProperRows h
  let A:=fun i=>FrozenRead.meanOn μ u (F i)
  let B:=fun i=>FrozenRead.meanOn μ v (F i)
  ‖properThree A-properThree B‖ ≤ 26*L 0*L 1*L 2*(t+
    (∫s in E,(cost u v s+cost v u s) ∂μ.prod μ)/(2*(∫x,u x ∂μ)*(∫x,v x ∂μ)))

def bondObstruction (p:BudgetPoint)(S:Activities G n)(e:Edge (Site n))(D r:ℕ)(U V:Fld):Prop:=
  let Y:=halo (max (D+p.B) (r*Push.GridApprox.Attach.leg p.B)) {e.1}
  let H:=jointTerritory S e U V
  ¬Healthy p.threshold Y U ∨ ¬Healthy p.threshold Y V ∨
    ((longFiled S p e r U ∨ longFiled S p e r V) ∧
      max |scalarParcel S p U H ∅| |scalarParcel S p V H ∅| < 4*Real.exp (-(p.supportExponent*(r:ℝ))/2))

def filedTolerance (p:BudgetPoint)(e:Edge (Site n))(r:ℕ)(price w ε:ℝ):ℝ:=
  min 1 (max 0 (min 1 (price/2+(w/2)*Real.exp (-(p.supportExponent*(r:ℝ))/2)))+residualCost p e ε)

private theorem env_pull {X:Type*}[MeasurableSpace X]{f:Fld→ℝ}(h:Envelope f){J:X→Fld}(JM:Measurable J):
    Envelope (fun x=>f (J x)):=by
  obtain ⟨b,hb⟩:=h.cost
  exact ⟨h.meas.comp JM,b,fun x=>hb _⟩

private theorem draw_meas (outside:Fld)(e:Edge (Site n)): Measurable (fun z:G.El=>update outside e z):=by
  apply measurable_pi_lambda;intro i
  by_cases eq:i=e
  · subst i;simp only [update_self];intro s hs;exact hs
  simpa only [update_of_ne eq] using (measurable_const (a:=outside i):Measurable (fun _:G.El=>outside i))

theorem restored_regional_hearing (op:StepData c n)(branch:op.patch.Branches op.kernel G)(held:Config G c)
    (p:BudgetPoint)(clip:Clip)(P:PathData G){σ C Λ s' B:ℝ}(pay:P.Bounds clip σ C Λ)(licensed:Decent clip p)
    (β:ℝ)(rank:ι→ℕ)(bank:(v:ι)→ℕ→Atom G (rank v))(coef:ι→ℝ)(book:List ι)(pos:0<s')
    (stock:∀v∈book,SumBudget (fun i=>(bank v i).budget s') B)(reset:∀v∈book,∀h:rank v=2,zeroContact (h ▸ bank v))
    (e:Edge (Site n))(D r:ℕ)(outside:Fld)(S R:Activities G n){w δ ε ξ:ℝ}
    (gas:S.Valid p δ w)(small:w≤1)(gp:∀U,0<S.gas p U)(reg:R.Valid p ε ξ)(width:1 ≤ p.supportExponent)
    (offset:ℝ)(h:Fin 3→G.El→ℂ)(eh:∀i,Envelope (h i))(L:Fin 3→ℝ)(ln:∀i,0≤L i)(cash:∀i x,‖h i x‖≤L i):
    let J:=fun z:G.El=>update outside e z
    let k:=fun z=>op.density β (J z) held
    let a:=fun z=>Real.exp (offset-R.additive p (J z))*(Real.exp (-fullPhysical p clip P β rank bank coef book (J z))*S.gas p (J z))
    let b:=fun z=>Real.exp (-fullIndependent clip P β rank bank coef book (J z))
    let t:=filedTolerance p e r (pathCash σ C Λ β D+passengerCash rank s' B coef D book) w ε
    let E:=pairExcess (fun z=>Real.log (a z)-Real.log (b z)) t
    MeasurableSet E ∧ (∀s∈E,bondObstruction p S e D r (J s.1) (J s.2)) ∧
      sevenFare G.probHaar (fun z=>k z*a z) (fun z=>k z*b z) h L E t:=by
  intro J k a b t E
  have jm:Measurable J:=draw_meas outside e
  have ks(z:G.El):0<k z:=(inv_pos.mpr (Push.BetaTransport.noiseCost_pos op _)).trans_le
    (Push.BetaTransport.density_bounds op branch (β:=β) le_rfl (J z) held).1
  let kernel:=fun z:Fld×Config G c=>op.density β z.1 z.2
  have km:Measurable kernel:=op.density_meas branch β
  have pairm:Measurable (fun z:G.El=>(J z,held)):=jm.prodMk (measurable_const (a:=held))
  have km':Measurable k:=Measurable.comp (g:=kernel) (f:=fun z:G.El=>(J z,held)) km pairm
  have ke:Envelope k:=by
    obtain ⟨B,bd⟩:=op.density_bound (G:=G) branch β
    refine ⟨km',B,fun z=>?_⟩
    rw [Real.norm_of_nonneg (ks z).le];exact bd .. 
  have kp:0<∫z,k z ∂G.probHaar:=by
    apply (integral_pos_iff_support_of_nonneg (fun z=>(ks z).le) (ke.integrable G.probHaar)).2
    rw [show Function.support k=Set.univ from Set.eq_univ_of_forall (fun z=>(ks z).ne')]
    simp
  let f:=fun z=>fullPhysical p clip P β rank bank coef book (J z)
  let bare:=fun z=>Real.exp (-f z)*S.gas p (J z)
  have ⟨fe,be⟩:=filed_action_envelopes (n:=n) p clip P pay β rank bank coef book pos stock
  have gs:Envelope (S.gas p):=⟨S.gas_measurable gas.forced,(Activities.gasSeries_of_KBound gas.boundK).bound⟩
  have baree:Envelope bare:=(env_pull fe jm).neg.exp.mul (env_pull gs jm)
  have relevante:Envelope b:=(env_pull be jm).neg.exp
  have before:=original_wilson_regional_hearing p clip P pay licensed β rank bank coef book pos stock reset e D r outside
    G.probHaar id measurable_id S gas small k ke (fun z=>(ks z).le) kp h eh L ln cash (fun z=>gp (J z))
  let t₀:=min 1 ((pathCash σ C Λ β D+passengerCash rank s' B coef D book)/2+(w/2)*Real.exp (-(p.supportExponent*(r:ℝ))/2))
  have after:=paid_regular_pair p e outside id measurable_id G.probHaar R reg width ke baree relevante
    (fun z=>(ks z).le) (fun z=>mul_pos (Real.exp_pos _) (gp (J z))) (fun z=>Real.exp_pos _) kp offset t₀ h eh L ln cash
  exact ⟨after.1,fun s hs=>before.2.1 s (after.2.1 hs),after.2.2⟩

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
