import YM.Integration.WilsonAddressedMixedEnrolledTrial
import YM.Integration.WilsonReflectedPublicCommonRows
/-! Each resident mixed-radius inverse has its own ordinary Wilson ear on the
common reporter.  Retain the inverse used by the source's K trial. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedThermalArms
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records MergeProof Push.Local Motion
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonMeasuredPublicEntranceGridDebit
open WilsonAddressedMixedEnrolledTrial WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]
local notation "C" => R.family
local notation "H" => (C).path.levels.clock.hatBeta

def rent (d:ℕ)(bank:ℝ):ℝ:=8*bank*max 1 (WilsonAddressedPublicFiledFee.price R d)

theorem priced {d N p f K:ℕ}(A:Arm R d N p f K){bank credit:ℝ}(bp:0≤bank)(cp:0≤credit)
    (raw:let s:=WilsonAddressedPublicSignedFare.amplitude R d f 1
      let due:=8*bank*credit
      let total:=WilsonAddressedPublicFiledFee.price R d*due
      ‖s‖*A.cash ≤ due ∧ ‖s‖*((1+4*stock C f)*A.cash) ≤ total ∧
        ‖s‖*((invoice («C»:=C) d f p+4)*A.cash) ≤ total ∧ ‖s‖*(2*A.cash) ≤ total):
    Priced R A (rent R d bank*credit*((C).S.a f)^d):=by
  let a:=(C).S.a f
  let m:=max 1 (WilsonAddressedPublicFiledFee.price R d)
  let due:=8*bank*credit
  have da:0<a^d:=pow_pos ((C).S.a_pos f) _
  have cost:0≤due:=mul_nonneg (mul_nonneg (by norm_num) bp) cp
  have count:‖WilsonAddressedPublicSignedFare.amplitude R d f 1‖=(a^d)⁻¹:=by
    simp [WilsonAddressedPublicSignedFare.amplitude,a,norm_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos ((C).S.a_pos f)]
  have cmp{y:ℝ}{c:ℝ}(r:‖WilsonAddressedPublicSignedFare.amplitude R d f 1‖*y≤c*due)(h:c ≤ m):
      y ≤ rent R d bank*credit*a^d:=by
    have h0: y/a^d ≤ m*due:=by
      rw [div_eq_inv_mul];rw [count] at r;exact r.trans (mul_le_mul_of_nonneg_right h cost)
    have out: y ≤ m*due*a^d:=(div_le_iff₀ da).mp h0
    exact out.trans_eq (by dsimp [rent,due,m]; ring)
  exact ⟨cmp (raw.1.trans_eq (one_mul due).symm) (le_max_left ..),
    rem_mono A.filed.paid (cmp raw.2.1 (le_max_right ..)),
    A.filed.primary.trans (cmp raw.2.2.1 (le_max_right ..)),
    A.filed.measured.trans (cmp raw.2.2.2 (le_max_right ..))⟩

theorem original (d j:I→ℕ){target N p f K power:ℕ}(up:f<K)(live:K≤N)
    (Y:(i:I)→(C).label (d i))(M:I→ℝ){credit:ℝ}(mp:∀i,0≤M i)(cp:0≤credit)
    (limit:((C).path.levels.budget f).supportExponent≤100)
    (posted:Funded (R:=R) d j target N p f K power up live Y M credit):
    ∃(before:∀i,j i≤f)(F:(i:I)→(C).label (d i) ≃ₗ[ℂ] (C).label (d i)),
    (∀i e,Arrived R (d i) (j i) K N p target ((before i).trans up.le) live (1/32) (F i) e) ∧
    let w:=fun i=>(F i).symm (fitted R (d i) (j i) N p (Y i))
    (∀χ:I→ℝ,(∀i,1≤χ i) → ∀i,((C).labels.level (d i)).coeffSize
        ((((χ i:ℝ):ℂ)⁻¹*(((C).S.a K:ℂ)^(d i))⁻¹) • w i) ≤ max 1 (4*∑i,M i)*(H K)^power) ∧
    ∀i (s:Signed)(b:Bool)(o:Site ((C).side f p)),∃A:Arm R (d i) N p f K,
      A.Y=Y i ∧ A.w=w i ∧ A.b=b ∧ A.s=s ∧ A.o=o ∧
      Priced R A (rent R (d i) (M i)*credit*((C).S.a f)^(d i)):=by
  classical
  obtain ⟨before,F,arr,held,finance⟩:=posted
  refine ⟨before,F,arr,fun χ χp=>(finance χ χp).2,?_⟩
  intro i s b o
  obtain ⟨z,paper,_⟩:=held i 0
  let w:=(F i).symm (fitted R (d i) (j i) N p (Y i))
  let B:=bill R (d i) K f w
  let atDate (l:ℕ):Prop:=WilsonAddressedRestartedFiled.Filed R (d i) N p f 0
    (WilsonAddressedRestartedColumn.track R (d i) N p l
      (WilsonPositionProgramOriginalBlockedTrial.numerator R (d i) N p l 0 w) f-
      calValues («C»:=R.family) (d i) N p f ((R.family.factory (d i) N p).terminal.symm (Y i)))
    (bill R (d i) l f w) z
  have checked:atDate K:=(congrArg atDate (Nat.add_sub_of_le up.le)).mp paper
  let A:Arm R (d i) N p f K:=⟨Y i,w,b,s,o,B,z,checked⟩
  have receipts:=((finance (fun _=>1) (fun _=>le_rfl)).1 i)
  exact ⟨A,rfl,rfl,rfl,rfl,rfl,priced R A (mp i) cp ⟨receipts.1,receipts.2 limit⟩⟩
end YM.Integration.WilsonReflectedMixedThermalArms
end
