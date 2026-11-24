import YM.Integration.WilsonReflectedMixedThermalArms
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedFundedSeat
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records MergeProof Push.Local Motion
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonMeasuredPublicEntranceGridDebit
open WilsonAddressedMixedEnrolledTrial WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]
local notation "C" => R.family
local notation "H" => (C).path.levels.clock.hatBeta


open WilsonReflectedMixedThermalArms
/-- The same fitted column and all its field placements with the true per-source bill.
The capital bound is available at unit normalization before any common dose.
-/
def Seat (d j target N p f K e:ℕ)(up:f≤K)(live:K≤N)(Y:(C).label d)(M ceiling:ℝ):Prop:=
  ∃(first:j≤f)(F:(C).label d ≃ₗ[ℂ] (C).label d),
    (∀x,Arrived R d j K N p target (first.trans up) live (1/32) F x) ∧
    let w:=F.symm (fitted R d j N p Y)
    ((C).labels.level d).coeffSize ((((C).S.a K:ℂ)^d)⁻¹ • w) ≤ ceiling ∧
    ∀(s:Signed)(b:Bool)(o:Site ((C).side f p)),∃A:Arm R d N p f K,
      A.Y=Y ∧ A.w=w ∧ A.b=b ∧ A.s=s ∧ A.o=o ∧
      Priced R A (rent R d M*((H f)^(e+1))⁻¹*((C).S.a f)^d)

theorem original (d j e:I→ℕ){target N p f K power reserve:ℕ}(up:f<K)(live:K≤N)
    (Y:(i:I)→(C).label (d i))(M:I→ℝ)(pos:∀i,0≤M i)(take:∀i,e i+1≤reserve)
    (limit:((C).path.levels.budget f).supportExponent≤100)
    (paid:Funded (R:=R) d j target N p f K power up live Y M (((H f)^reserve)⁻¹)):
    ∀i,Seat R (d i) (j i) target N p f K (e i) up.le live (Y i) (M i)
      (max 1 (4*∑i,M i)*(H K)^power):=by
  classical
  have base:1≤H f:=((C).path.levels.fits.delayed f).le
  have heat:0<H f:=zero_lt_one.trans_le base
  let reserveFee:=((H f)^reserve)⁻¹
  obtain ⟨before,F,issued,capital,physical⟩:=WilsonReflectedMixedThermalArms.original R d j up live Y M pos
      (inv_nonneg.mpr (pow_nonneg heat.le reserve)) limit paid
  intro i
  refine ⟨before i,F i,issued i,?_,?_⟩
  · simpa only [Complex.ofReal_one,inv_one,one_mul] using capital (fun _=>1) (fun _=>le_rfl) i
  · intro s b o
    obtain ⟨A,src,fit,bar,angle,site,room⟩:=physical i s b o
    refine ⟨A,src,fit,bar,angle,site,?_⟩
    have fee:rent R (d i) (M i)*reserveFee*((C).S.a f)^(d i) ≤
        rent R (d i) (M i)*((H f)^(e i+1))⁻¹*((C).S.a f)^(d i):=by
      have rr:0≤rent R (d i) (M i):=mul_nonneg (mul_nonneg (by norm_num) (pos i)) (zero_le_one.trans (le_max_left ..))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (inv_anti₀ (pow_pos heat _) (pow_le_pow_right₀ base (take i))) rr) (pow_nonneg ((C).S.a_pos f).le _)
    exact ⟨room.1.trans fee,rem_mono room.2.1 fee,room.2.2.1.trans fee,room.2.2.2.trans fee⟩

end YM.Integration.WilsonReflectedMixedFundedSeat
end
