import YM.Integration.WilsonThermometerSameWalkBirthShift
import YM.Integration.WilsonMeasuredSingletonForce
import YM.Extra.SOURCE_HISTORIES.Beside

/-! The complete original positive-rank birth on the hard merger already
present in the elected bare presentation. -/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkBare
open Function Finset Lattice Wilson RG Source Marker QuadraticLocal Earn Sunrise
open Push Push.Corrected Push.AbsoluteSums Push.Local Animals MeasureTheory
open PhysicalNext.Repeat.Legato Extra.Trajectories Extra.Histories Labels Extra.Histories.Relay
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} {A:Hol G}
    (P:Rep G n) (S:SectionData F) (sound:S.Sound A) (o:Site n) (v:F.Coeff)
local notation "J" => Stock.census Unit
local notation "home" => (fun _:Unit=>o)
local notation "X" => S.footprint o
local notation "M" => WilsonThermometerSameWalkBirthShift.sheet P S sound o v

include sound in
theorem original {rad κ slack B:ℝ} (pos:0 < rad) (kp:0 < κ)
    (cap:0 ≤ B) (price:∀ U,‖supplement S P o v U‖ ≤ B)
    (win:rad*B*Real.exp ((P.p.supportExponent+1)*coverNumber P.p.B X) ≤ slack)
    {σ C Λ δ w:ℝ} (law:P.Lawful σ C Λ δ w) (existing:Hard.Install P.activities P.p κ slack):
    ∃ Z:Coefficient F n, Z.Format o A P ∧ Z.remBound o P (Real.sqrt κ) (rad⁻¹*Real.sqrt κ) ∧
      ∀ U,Z.density o S P U=(P.eval U:ℂ)*S.places (F.scaled P.p.threshold⁻¹ v) o U:=by
  classical
  obtain ⟨u,b,⟨H⟩,old⟩:=existing.room
  let K:=Kiosk.Second.canopy (Hard.rent (α:=Unit) (o:=home) (R:=J) old) (M) H
  have gate:(M).Budget (fun _=>rad) P.p.B (P.p.supportExponent+1) slack:=by
    obtain ⟨f,cn,h⟩:=WilsonThermometerSameWalkBirthShift.paid P S sound o v (a:=P.p.supportExponent+1) pos cap price
    refine ⟨f,cn,fun y=>?_⟩
    obtain ⟨nn,ss,hh⟩:=h y
    exact ⟨nn,ss,hh.trans win⟩
  have received:=Hard.Rent.instals (fun _:Unit=>pos) H old (M) P.p.exponent_pos.le gate
  let Q:=WilsonMeasuredSingletonForce.row (F:=F) K () ()
  have sq:0 < Real.sqrt κ:=Real.sqrt_pos.mpr kp
  have admitted:K.Paid (fun _=>rad) P.p.B P.p.supportExponent (Real.sqrt κ*Real.sqrt κ):=by
    rw [Real.mul_self_sqrt kp.le];exact received.1
  have soft:(primary o v).remBound o P (Real.sqrt κ) 0:=primary_rem _ sq
  have hard:Q.remBound o P (Real.sqrt κ) (rad⁻¹*Real.sqrt κ):=
    WilsonMeasuredSingletonForce.restored K () () (fun _=>rad) (fun _=>pos) sq sq.le admitted
  have hardShape:Q.Format o A P:=WilsonMeasuredSingletonForce.format K () () A
  have header:(primary o v).Format o A P:=primary_format _
  obtain ⟨fit,paid⟩:=presentation header soft hardShape hard
  refine ⟨beside (primary o v) Q,fit,by simpa only [zero_add] using paid,?_⟩
  intro U
  have quiet:((M).log () U).part (J).quiet=0:=by
    rw [WilsonThermometerSameWalkBirthShift.log,Poly.part_send,if_neg ((J).fire_hot ()).symm]
  have value:(WilsonCenteredAbsoluteHard.gas K () U).part ((J).fire ())=
      (P.activities.gas P.p U:ℂ)*supplement S P o v U:=by
    have sum:= (received.2 () U).tsum_eq
    change (∑' a,Fusion.Attached.packet P.activities P.p (K.hard ()) U a).part _=_
    rw [sum,Poly.part_smul,MergeProof.Accent.whisper J _ quiet (),WilsonThermometerSameWalkBirthShift.log,Poly.part_send,if_pos rfl]
  have debt:Q.density o S P U=(P.eval U:ℂ)*supplement S P o v U:=by
    rw [WilsonMeasuredSingletonForce.density K () () S U (received.2 () U).summable,value]
    simp only [Rep.eval,Complex.ofReal_mul,mul_assoc]
  rw [congrFun (plus law soft hard S) U,Pi.add_apply,primary_density,debt]
  unfold supplement;ring

end YM.Integration.WilsonThermometerSameWalkBare
end
