import YM.Integration.WilsonMacroscopicRichMSProbe

/-! The fixed earlier probing map on the independently prescribed raw output has one
operator bound for all finer physical cutoffs and periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichOutputNorm
open Function Filter Lattice Wilson RG Cells Source Labels Spec PhysMS Analysis
open Next.UVStress Next.Foundations Push.Local Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open WilsonMacroscopicRichCapturedProbes
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}

theorem stock (H:C.Makes)(h u:ℕ)(start:C.ref h≤u):
    ∃K:ℝ,0≤K ∧ ∀N p (_uN:u≤N)(z:C.label h),quota C h u N p z≤K*‖z‖:=by
  induction u,start using Nat.le_induction with
  | base =>
    refine ⟨((C.labels.level h).extra+1:ℕ),Nat.cast_nonneg _,?_⟩
    intro N p live z
    unfold quota
    rw [C.normalized H live z]
    exact Push.Local.size_le_norm _ _
  | succ u uLive ih =>
    obtain ⟨K,nn,tariff⟩:=ih
    let c:=(C.path.levels.params (u+1)).columns
    have cn:0≤c:=zero_le_one.trans ((C.path.levels.params _).columns_ge)
    refine ⟨c*K,mul_nonneg cn nn,?_⟩
    intro N p live z
    have one:quota C h (u+1) N p z≤c*quota C h u N p z:=
      (H.calibrated h N p (uLive.trans ((Nat.le_succ u).trans live))).back u uLive live
        ((C.factory h N p).terminal.symm z)
    exact one.trans ((mul_le_mul_of_nonneg_left (tariff N p ((Nat.le_succ u).trans live) z) cn).trans_eq (mul_assoc _ _ _).symm)

theorem purchased (R:Run G)(h u:ℕ)(doors:∀p,Opened R.family h u p):
    ∃K:ℝ,0≤K ∧ ∀N p (uN:u≤N)(z:R.family.label h),
      ‖forecast R (doors p) uN z‖≤K*‖z‖:=by
  obtain ⟨K,nn,fee⟩:=stock R.makes h u (doors 0).post
  refine ⟨2*K,mul_nonneg zero_le_two nn,?_⟩
  intro N p live z
  have rank:=size_gap h N p u R.makes (doors p) live ((R.family.factory h N p).terminal.symm z)
  refine (Push.Local.norm_le_size (R.family.labels.level h) _).trans (?_:_≤_)
  change _≤(2*K)*‖z‖
  calc
    _ ≤ 2*quota R.family h u N p z:=rank.1
    _ ≤ 2*(K*‖z‖):=mul_le_mul_of_nonneg_left (fee N p live z) zero_le_two
    _ = _:= (mul_assoc _ _ _).symm

theorem read (R:Run G)(S:Table R.family.book)(h u:ℕ)(doors:∀p,Opened R.family h u p):
    ∃K:ℝ,0≤K ∧ ∀(J:ℝ→tower S)(r:ℝ)(N p:ℕ)(live:u≤N)(t:Probe G h)(y:(Climb.Bel R.family.book).Field h),
      ‖WilsonMacroscopicRichMSProbe.read R J r (doors p) live t y‖≤
        ‖runProbe (R.family.labels.level h) t‖*(K*(‖(S.representative h).toContinuousLinearMap‖*
        (‖(J r h).toLinearMap.toContinuousLinearMap‖*‖y‖))):=by
  obtain ⟨K,nn,fee⟩:=purchased R h u doors
  refine ⟨K,nn,?_⟩
  intro J r N p live t y
  let π:=(S.representative h).toContinuousLinearMap
  let F:=(J r h).toLinearMap.toContinuousLinearMap
  let L:=runProbe (R.family.labels.level h) t
  have label:‖π (F y)‖≤‖π‖*(‖F‖*‖y‖):=
    (π.le_opNorm _).trans (mul_le_mul_of_nonneg_left (F.le_opNorm _) π.opNorm_nonneg)
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    ((fee N p live (π (F y))).trans (mul_le_mul_of_nonneg_left label nn)) L.opNorm_nonneg)

end YM.Integration.WilsonMacroscopicRichOutputNorm
