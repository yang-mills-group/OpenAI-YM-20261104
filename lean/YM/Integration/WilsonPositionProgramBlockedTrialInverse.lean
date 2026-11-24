import YM.Integration.WilsonPositionProgramBlockedTrialCone

/-! Finite measured inverse for a guarded trial on the original blocked
Wilson vacuum. The full response is sampled before choosing the prescribed
reporting vector. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonPositionProgramBlockedTrialInverse
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullPlacedGermMap Push.Local
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "B₀" => (C₀).localSection d
local notation "H₀" => (C₀).path
local notation "P₀" => (C₀).params

theorem original (simple:G.Simple) :
    ∃ onset:ℕ,∀ b≥onset, ∀ N p n,∀ live:b+n≤N,
      let rep:=(H₀).rep N p b
      let out:=WilsonPositionProgramOriginalBlockedTrial.carried R d live 0
      ∃ A:(C₀).label d ≃ₗ[ℂ] (C₀).label d,
        (∀ v q,Printed C₀ d N p b 0 q (out v) → A v=projection F₀ P₀ rep.p.threshold 0 q) ∧
        ∀ e:(C₀).label d,let w:=A.symm e
        (F₀).coeffSize w ≤ (2*WilsonPositionProgramBlockedTrialCone.cost R b n)*(F₀).coeffSize e ∧
        ∃ q:Coefficient F₀ ((C₀).side b p),q.Format 0 P₀ rep ∧
          q.remBound 0 rep (safety C₀ b) (2*stock C₀ b*(F₀).coeffSize e) ∧
          (F₀).coeffSize q.x≤2*(F₀).coeffSize e ∧ q.density 0 B₀ rep=out w ∧
          projection F₀ P₀ rep.p.threshold 0 q=e:=by
  obtain ⟨s,opens⟩:=eventually_atTop.mp (open_late C₀ simple d)
  refine ⟨max s (R.t d),?_⟩;intro b late N p n live rep out
  have now:b≤N:=by omega
  let home:Opened C₀ d b p:=opens b ((le_max_left ..).trans late) p
  let I:=WilsonPositionProgramBlockedTrialVoice.denomination F₀ H₀ N (b+n)
  obtain ⟨Z,heard,_,returned⟩:=WilsonPositionProgramBlockedTrialCone.original R d simple
    ((le_max_right ..).trans late) live (p:=p)
  let Q (x:(C₀).label d):=Z.plays (I.symm x)
  have fit (x:(C₀).label d):Printed C₀ d N p b 0 (Q x) (out x):=
    ⟨(heard.earns _).1,⟨_,(heard.earns _).2⟩,(returned x).1⟩
  obtain ⟨A,allForms⟩:=WilsonOriginalNullPlacedGermMap.linear C₀ d N p b 0 R.makes home now out
    (fun x=>⟨Q x,fit x⟩)
  have equals (x:(C₀).label d):A x=page (C:=C₀) d p b (Q x):=by
    have h:=allForms x (Q x) (fit x)
    have budget:rep.p=plank C₀ b:=(R.makes.wilson.represents N p b now).vac
    change A x=projection F₀ P₀ rep.p.threshold 0 (Q x) at h
    rw [budget] at h;exact h
  have cash (x:(C₀).label d):Z.charge (I.symm x) ≤ stock C₀ b * (F₀).coeffSize (Q x).x:=by
    rw [show (Q x).x=Z.index (I.symm x) from heard.currents _]
    exact (heard.cone _).trans (mul_le_mul_of_nonneg_left (Work.G08.size_core ..)
      (zero_le_one.trans ((H₀).levels.params b).columns_ge))
  have native (x:(C₀).label d):(F₀).coeffSize (Q x).x ≤ 2*(F₀).coeffSize (A x):=by
    let q:=Q x
    have acquired:reads (C:=C₀) d N p b q (stock C₀ b*(F₀).coeffSize q.x):=
      ⟨(heard.earns _).1,rem_mono (heard.earns _).2 (cash x)⟩
    have diff: (F₀).coeffSize (A x-q.x) ≤ (1/4:ℝ)*(F₀).coeffSize q.x:=by
      rw [equals x]
      exact (measured_diff d N p b R.makes home.post now acquired).trans (by
        rw [←mul_assoc];exact mul_le_mul_of_nonneg_right home.small.le (Work.G08.size_nonneg ..))
    have flip:(F₀).coeffSize (q.x-A x)=(F₀).coeffSize (A x-q.x):=by
      unfold Frame.coeffSize;apply Finset.sum_congr rfl;intro i _;exact norm_sub_rev ..
    have triangle:=Size.add F₀ (A x) (q.x-A x)
    rw [_root_.add_sub_cancel,flip] at triangle
    change (F₀).coeffSize q.x ≤ _;linarith [Work.G08.size_nonneg F₀ q.x]
  have inverse_fee (x:(C₀).label d):(F₀).coeffSize x ≤
      (2*WilsonPositionProgramBlockedTrialCone.cost R b n)*(F₀).coeffSize (A x):=by
    have top: (F₀).coeffSize x≤WilsonPositionProgramBlockedTrialCone.cost R b n*(F₀).coeffSize (Q x).x:=by
      rw [show (Q x).x=Z.index (I.symm x) from heard.currents _];exact (returned x).2
    exact (top.trans (mul_le_mul_of_nonneg_left (native x)
      (WilsonPositionProgramBlockedTrialCone.cost_nonneg R b n))).trans_eq (by ring)
  have inj:Injective A:=by
    apply LinearMap.ker_eq_bot.mp;apply LinearMap.ker_eq_bot'.mpr;intro v vanished
    have h:=inverse_fee v;rw [vanished] at h
    exact norm_le_zero_iff.mp ((norm_le_size ..).trans (by
      simpa only [Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero,mul_zero] using h))
  let M:=LinearEquiv.ofBijective A ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩
  refine ⟨M,allForms,?_⟩;intro e
  let w:=M.symm e
  have back:A w=e:=M.apply_symm_apply e
  have z:=native w;rw [back] at z
  have pay:=inverse_fee w;rw [back] at pay
  refine ⟨pay,Q w,(fit w).form,rem_mono (heard.earns (I.symm w)).2 ?_,z,(fit w).fields,?_⟩
  · exact (cash w).trans ((mul_le_mul_of_nonneg_left z
      (zero_le_one.trans ((H₀).levels.params b).columns_ge)).trans_eq (by ring))
  exact (allForms w _ (fit w)).symm.trans back

end YM.Integration.WilsonPositionProgramBlockedTrialInverse
end
