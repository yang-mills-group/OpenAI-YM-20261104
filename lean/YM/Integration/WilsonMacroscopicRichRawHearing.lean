import YM.Integration.WilsonMacroscopicRichMSProbeTransition

/-! A bounded signed comparison on the measured fixed-date probes gives a bounded raw
label for the complete submitted source, before the cutoff and the period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichRawHearing
open Filter Function Set Lattice Wilson RG Source Labels Analysis Next.Foundations Next.UVStress Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec FilteredWilsonProduct
open WilsonMacroscopicRichCapturedProbes WilsonMacroscopicRichCapturePropagation
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G)

theorem measured (h:ℕ):
    ∃P:Finset (Probe G h),∀u:ℕ,∀doors:∀p,Opened R.family h u p,∃L:ℝ,0≤L ∧
    ∀(N p b:ℕ)(_:Slices R.family.path.levels p)(ub:u≤b)(bN:b≤N)(uN:u<N)
      (Y:Cut R.family N p)(Z:Config G (R.family.side b p)→ℂ),
    Continuous Y → GaugeInvariant Y → Booked R.family N p h Y u uN.le →
    credit R.family N p h Y b bN=Z →
    ∀z:R.family.label h,
      ‖z-(label (C:=R.family) (D:=h) (w:=(N,p)) R.makes (doors p) uN.le Y:R.family.label h)‖≤
        L*WilsonMacroscopicRichIndependentHearing.debit R P (doors p) ub uN.le z Z:=by
  obtain ⟨P,K,kk,enough⟩:=probe_budget (R.family.labels.level h)
  refine ⟨P,?_⟩
  intro u doors
  obtain ⟨A,nn,buy⟩:=quota_stop R.family R.makes (doors 0).post
  refine ⟨A*2*K,mul_nonneg (mul_nonneg nn zero_le_two) (zero_le_one.trans kk),?_⟩
  intro N p b T ub bN uN Y Z ct gi booked cash z
  let f:=fitting h N p u R.makes (doors p) uN.le
  let Tm:=(R.family.factory h N p).terminal
  let M:=topReport R.family N p h R.makes u (doors p) uN.le Y
  let v:=Tm.symm z-M
  let c:=WilsonMacroscopicRichIndependentHearing.debit R P (doors p) ub uN.le z Z
  have cn:0≤c:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have good:=WilsonMacroscopicRichMeasuredProbe.measured R T uN h Y ct gi (doors p) booked
  have account:=WilsonMacroscopicRichCapturePropagation.original R T ub bN h Y Z cash
  have measured (t:Probe G h):runProbe (R.family.labels.level h) t (f M)=
      Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z):=
    (good t).trans (congrArg (Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0) account.symm)
  have price:(R.family.labels.level h).coeffSize (f v)≤K*c:=by
    apply enough _ _ cn
    intro t ht
    let π:R.family.label h→ₗ[ℂ]ℂ:=(runProbe (R.family.labels.level h) t).toLinearMap
    have one:π (f v)=π (f (Tm.symm z))-π (f M):=
      (congrArg π (f.map_sub (Tm.symm z) M)).trans (π.map_sub (f (Tm.symm z)) (f M))
    have eq:=one.trans (congrArg (fun a:ℂ=>π (f (Tm.symm z))-a) (measured t))
    apply (congrArg (fun a:ℂ=>‖a‖) eq).le.trans
    exact Finset.single_le_sum (f:=fun t=>‖runProbe (R.family.labels.level h) t (f (Tm.symm z))-
      Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z)‖)
      (fun _ _=>norm_nonneg _) ht
  have cost:quota R.family h u N p (Tm v)≤2*(R.family.labels.level h).coeffSize (f v):=by
    unfold quota
    change (R.family.labels.level h).coeffSize ((R.family.factory h N p).entries u (Tm.symm (Tm v))).x ≤ _
    rw [Tm.symm_apply_apply]
    exact (size_gap h N p u R.makes (doors p) uN.le v).2
  have id:Tm v=z-(label (C:=R.family) (D:=h) (w:=(N,p)) R.makes (doors p) uN.le Y:R.family.label h):=by
    change Tm (Tm.symm z-M)=z-Tm M
    rw [map_sub,Tm.apply_symm_apply]
  rw [←id]
  exact (buy N p (Tm v) uN.le).trans ((mul_le_mul_of_nonneg_left
    (cost.trans (mul_le_mul_of_nonneg_left price zero_le_two)) nn).trans_eq (by ring))

end YM.Integration.WilsonMacroscopicRichRawHearing
