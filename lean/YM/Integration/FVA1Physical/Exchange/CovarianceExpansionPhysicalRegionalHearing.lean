import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRegionalGasChange
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPairDetectorPrice
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFullActionEnvelopes
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPhysicalMaskHearing

/-! The complete seven-row joint reading on a held bond under the original
masked numerical action and its independently filed unmasked Wilson action.
The only surviving exceptional pair is locally failed or has an active long
owner and a small mass on the same reachable component at BOTH fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Function MeasureTheory Lattice RG Wilson Precision WilsonStartup RoseCut
open Marked Marked.RemoteRoster YM.Integration.FVA1Physical.Replica
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{ι X:Type*}[MeasurableSpace X]
local notation "Fld" => Config G n

private theorem pull_env {f:Fld→ℝ}(h:Envelope f){u:X→Fld}(um:Measurable u):Envelope (fun x=>f (u x)):=
  ⟨h.meas.comp um,by obtain ⟨b,cap⟩:=h.cost;exact ⟨b,fun x=>cap _⟩⟩

private theorem positive_weighted_mass (μ:Measure X)[IsFiniteMeasure μ]{k a:X→ℝ}
    (ek:Envelope k)(ea:Envelope a)(kn:∀x,0 ≤ k x)(ap:∀x,0 < a x)(kp:0 < ∫x,k x ∂μ):
    0 < ∫x,k x*a x ∂μ:=by
  apply (integral_pos_iff_support_of_nonneg (fun x=>mul_nonneg (kn x) (ap x).le) ((ek.mul ea).integrable μ)).2
  have eq:Function.support (fun x=>k x*a x)=Function.support k:=by
    ext x;change k x*a x≠0 ↔ k x≠0
    exact ⟨left_ne_zero_of_mul,fun h=>mul_ne_zero h (ap x).ne'⟩
  rw [eq]
  exact (integral_pos_iff_support_of_nonneg kn (ek.integrable μ)).1 kp

/-- Same regulator, all readings and both physical normalizations. All
integrability and measurability follow from the original projector, filed
action stock, and its true KBound; only positivity of the actual gas and
nontriviality of the supplied sampling/transition kernel are used. -/
theorem original_wilson_regional_hearing (p:BudgetPoint)(c:Clip)(P:PathData G){σ C Λ σ' C':ℝ}
    (pay:P.Bounds c σ C Λ)(licensed:Decent c p)(β:ℝ)(rank:ι→ℕ)
    (A:(v:ι)→ℕ→Atom G (rank v))(coef:ι→ℝ)(L:List ι)(sp:0 < σ')
    (stock:∀v∈L,SumBudget (fun i=>(A v i).budget σ') C')(reset:∀v∈L,∀h:rank v=2,zeroContact (h ▸ A v))
    (e:Edge (Site n))(D r:ℕ)(outside:Fld)(μ:Measure X)[IsFiniteMeasure μ]
    (link:X→G.El)(lm:Measurable link)(S:Activities G n){w₀ δ:ℝ}(valid:S.Valid p δ w₀)(small:w₀ ≤ 1)
    (kernel:X→ℝ)(ke:Envelope kernel)(kn:∀x,0 ≤ kernel x)(kp:0 < ∫x,kernel x ∂μ)
    (h:Fin 3→X→ℂ)(env:∀i,Envelope (h i))(M:Fin 3→ℝ)(nn:∀i,0 ≤ M i)(bound:∀i x,‖h i x‖ ≤ M i):
    let U:=fun x=>update outside e (link x)
    let f:=fun x=>fullPhysical p c P β rank A coef L (U x)
    let w:=fun x=>fullIndependent c P β rank A coef L (U x);let gas:=fun x=>S.gas p (U x)
    let a:=fun x=>kernel x*(Real.exp (-f x)*gas x);let b:=fun x=>kernel x*Real.exp (-w x)
    let ℓ:=fun x=>Real.log (Real.exp (-f x)*gas x)-Real.log (Real.exp (-w x))
    let F:=physicalProperRows h;let T:=fun i=>FrozenRead.meanOn μ a (F i);let W:=fun i=>FrozenRead.meanOn μ b (F i)
    let z:=∫x,a x ∂μ;let q:=∫x,b x ∂μ
    let Y:=halo (max (D+p.B) (r*Push.GridApprox.Attach.leg p.B)) {e.1}
    let m:=4*Real.exp (-(p.supportExponent*(r:ℝ))/2)
    let tol:=min 1 ((pathCash σ C Λ β D+passengerCash rank σ' C' coef D L)/2+
      (w₀/2)*Real.exp (-(p.supportExponent*(r:ℝ))/2))
    let E:=pairExcess ℓ tol
    (∀x,0 < gas x) →
    MeasurableSet E ∧
      (∀s∈E,¬Healthy p.threshold Y (U s.1) ∨ ¬Healthy p.threshold Y (U s.2) ∨
        ((longFiled S p e r (U s.1) ∨ longFiled S p e r (U s.2)) ∧
          (let H:=jointTerritory S e (U s.1) (U s.2);
           max (abs (scalarParcel S p (U s.1) H ∅)) (abs (scalarParcel S p (U s.2) H ∅)) < m))) ∧
      ‖properThree T-properThree W‖ ≤ (26*M 0*M 1*M 2)*
      (tol+(∫s in E,(cost a b s+cost b a s) ∂μ.prod μ)/(2*z*q)):=by
  intro U f w gas a b ℓ F T W z q Y m tol E gp
  have um:Measurable U:=by
    apply measurable_pi_lambda;intro i
    by_cases eq:i=e
    · subst i;simpa only [U,update_self] using lm
    simpa only [U,update_of_ne eq] using (measurable_const (a:=outside i):Measurable (fun _:X=>outside i))
  obtain ⟨phys,ind⟩:=filed_action_envelopes (n:=n) p c P pay β rank A coef L sp stock
  have fe:Envelope f:=pull_env phys um
  have we:Envelope w:=pull_env ind um
  have ge:Envelope gas:=pull_env ⟨S.gas_measurable valid.forced,(Activities.gasSeries_of_KBound valid.boundK).bound⟩ um
  have ae:Envelope (fun x=>Real.exp (-f x)*gas x):=fe.neg.exp.mul ge
  have be:Envelope (fun x=>Real.exp (-w x)):=we.neg.exp
  have ap(x:X):0 < Real.exp (-f x)*gas x:=mul_pos (Real.exp_pos _) (gp x)
  have bp(x:X):0 < Real.exp (-w x):=Real.exp_pos _
  have lm':Measurable ℓ:=ae.meas.log.sub be.meas.log
  have vpos:0 < Real.exp (-(p.supportExponent*(r:ℝ))/2):=Real.exp_pos _
  have vsmall:Real.exp (-(p.supportExponent*(r:ℝ))/2) ≤ 1:=Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg p.exponent_pos.le (Nat.cast_nonneg _))) (by norm_num))
  let v:=Real.exp (-(p.supportExponent*(r:ℝ))/2)
  have vsq:Real.exp (-p.supportExponent*r)=v*v:=by dsimp only [v];rw [←Real.exp_add];congr 1;ring
  have δsmall:2*w₀*Real.exp (-p.supportExponent*r) ≤ m/2:=by
    rw [vsq];change 2*w₀*(v*v) ≤ (4*v)/2
    nlinarith only [mul_le_mul_of_nonneg_right small (mul_nonneg vpos.le vpos.le),mul_le_mul_of_nonneg_left vsmall vpos.le]
  have fee:(2*w₀*Real.exp (-p.supportExponent*r))/m=(w₀/2)*v:=by
    rw [vsq];change 2*w₀*(v*v)/(4*v)=(w₀/2)*v;field_simp [vpos.ne'];ring
  have wn:0 ≤ w₀:=by obtain ⟨_,_,site⟩:=valid.boundK;exact Push.AbsoluteSums.budget_nonneg (site e.1)
  have E0:0 ≤ pathCash σ C Λ β D+passengerCash rank σ' C' coef D L:=by
    have healthy:Healthy p.threshold (halo (D+p.B) {e.1}) (1:Fld):=
      mem_of_mem_nhds (OlderPrice.collar_geometry (G:=G) p (halo (D+p.B) {e.1})).1
    have clear:e.1∉flags p.threshold (1:Fld):=Finset.disjoint_left.mp healthy (halo_subset _ _ (Finset.mem_singleton_self _))
    have price:=complete_physical_mask_price p c P pay licensed β rank A coef L sp stock reset e D (1:Fld) (1:Fld)
      (fun _ _=>rfl) healthy clear
    simpa only [sub_self,abs_zero] using price
  have tn:0 ≤ tol:=le_min zero_le_one (add_nonneg (div_nonneg E0 (by norm_num)) (mul_nonneg (div_nonneg wn (by norm_num)) vpos.le))
  have off(x y:X)(b':Edge (Site n))(hb:b'≠e):U x b'=U y b':=by simp only [U,update_of_ne hb]
  have shrink(x:X)(hx:Healthy p.threshold Y (U x)){v':ℕ}(le:v' ≤ max (D+p.B) (r*Push.GridApprox.Attach.leg p.B)):
      Healthy p.threshold (halo v' {e.1}) (U x):=by
    apply Finset.disjoint_left.mpr;intro z hz hot;obtain ⟨u,hu,hz⟩:=halo_spec.mp hz
    exact Finset.disjoint_left.mp hx (halo_spec.mpr ⟨u,hu,hz.trans le⟩) hot
  refine ⟨pair_excess_borel lm' tol,?_,?_⟩
  · rintro ⟨x,y⟩ ex
    by_cases xc:Healthy p.threshold Y (U x)
    swap;· exact Or.inl xc
    by_cases yc:Healthy p.threshold Y (U y)
    swap;· exact Or.inr (Or.inl yc)
    right;right
    have safe:e.1∉flags p.threshold (U y):=Finset.disjoint_left.mp yc (halo_subset _ _ (Finset.mem_singleton_self _))
    let H:=jointTerritory S e (U x) (U y)
    have contra(hs:(longFiled S p e r (U x) ∨ longFiled S p e r (U y)) →
        m ≤ max |scalarParcel S p (U x) H ∅| |scalarParcel S p (U y) H ∅|):False:=by
      have d:=component_physical_gas_log S valid small e r _ _ (off x y) (shrink x xc (le_max_right ..)) safe
        (gp x) (gp y) (show 0 < m by dsimp only [m];positivity) δsmall hs
      have aprice:=complete_physical_mask_price p c P pay licensed β rank A coef L sp stock reset e D _ _ (off x y) (shrink x xc (le_max_left ..)) safe
      have tot:|ℓ x-ℓ y| ≤ (pathCash σ C Λ β D+passengerCash rank σ' C' coef D L)+2*((2*w₀*Real.exp (-p.supportExponent*r))/m):=by
        have eq:ℓ x-ℓ y= -((f x-w x)-(f y-w y))+(Real.log (gas x)-Real.log (gas y)):=by
          dsimp only [ℓ];rw [Real.log_mul (Real.exp_pos _).ne' (gp x).ne',Real.log_mul (Real.exp_pos _).ne' (gp y).ne'];simp only [Real.log_exp];ring
        rw [eq]
        exact (abs_add_le ..).trans (add_le_add (by rw [abs_neg];exact aprice) (d.trans_eq (by ring)))
      apply (not_lt_of_ge ?_) (show tol < cap (ℓ x-ℓ y) from ex)
      unfold cap
      apply min_le_min_left 1
      rw [fee] at tot
      linarith only [tot]
    by_contra! neg
    apply contra
    intro h
    exact le_of_not_gt (neg h)
  exact pair_excess_seven μ ke.meas ae.meas be.meas kn ap bp lm' 0 (fun _=>by simp only [add_zero];rfl)
    tol tn h env M nn bound ((ke.mul ae).integrable μ) ((ke.mul be).integrable μ)
    (positive_weighted_mass μ ke ae kn ap kp) (positive_weighted_mass μ ke be kn bp kp)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
