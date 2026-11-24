import YM.Integration.WilsonThermometerRegisteredCenteredStop
import YM.Integration.WilsonThermometerRegisteredCenteredPhysicalMeans

/-! The compact connected Wilson thermometer uses the same three physical scalar means
at every placement. Only the full roster, its three pairs and the signed singleton
remain in its compensated physical linear reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredSelfComponents
open Primitives.GCC.Anchor Comparison.RG02 WilsonFiniteOrdinaryInverse
open Finset Marker PhysicalNext.Repeat.Legato RG17 FullVolume Climb
open Lattice Wilson RG Source Extraction Table Spec
open WilsonThermometerFiniteConnectedCells WilsonThermometerCenteredScalar
open WilsonThermometerRegisteredSingletonCenter WilsonThermometerRegisteredCenteredInvoice
open WilsonThermometerCenteredAlgebra WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open scoped BigOperators Classical
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge}

theorem constant (R:Run G) (A:Group R.family 6) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (unit:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j) (z:ℕ×ℕ) (late:A.station.k<z.1)
    (refs:∀v:Fin 3,R.family.ref (index A (grade v))≤z.1) (x:Fin 3→Site (R.family.side z.1 z.2)) (v:Fin 3):
    read (measured R A z x) {v}=read (measured R A z (fun _=>0)) {v}:=by
  let col:=A.station.wheel.atCut z (index A (grade v)) (vector A univ v)
  have atSite(y:Fin 3→Site (R.family.side z.1 z.2)):
      read (measured R A z y) {v}=WilsonThermometerOriginalMeans.one R.family z col (y v):=by
    change R.family.omega z.1 z.2 (WilsonPositionThermometerJointFaces.submitted A z (placement R z y).origin {v})=_
    rw [WilsonThermometerRegisteredMeasuredStation.submitted_at R A checked unit z late refs (placement R z y) {v}]
    simp only [prod_singleton]
    rfl
  rw [atSite x,atSite (fun _=>0)]
  exact WilsonThermometerOriginalMeans.location R.family z col (x v) 0

theorem source (R:Run G) (A:Group R.family 6) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (unit:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j) (z:ℕ×ℕ) (late:A.station.k<z.1)
    (refs:∀v:Fin 3,R.family.ref (index A (grade v))≤z.1) (x:Fin 3→Site (R.family.side z.1 z.2)):
    properInvoice (measured R A z x) 1=properInvoice (measured R A z fun _=>0) 1:=by
  have common:shift (measured R A z x) 1=shift (measured R A z fun _=>0) 1:=by
    funext v;unfold shift;rw [constant R A checked unit z late refs x v]
  unfold properInvoice invoice;rw [common]

open private correction_top from YM.Integration.WilsonThermometerRegisteredCenteredInvoice

theorem self (F:Poly J):properInvoice F 1=correction (fun v=>read F {v}):=by
  have shifts:shift F 1=fun v=>read F {v}:=by
    funext v;unfold shift WilsonThermometerCenteredScalar.read
    rw [Poly.one_part,if_neg (show face {v}≠(J).quiet by fin_cases v <;> decide),sub_zero]
  unfold properInvoice invoice
  have qu:(1:Poly J).part (J).quiet=1:=by rw [Poly.one_part,if_pos rfl]
  have inv:inverseMass (1:Poly J)=1:=by simpa only [one_mul] using right_inverse qu
  rw [inv,one_mul,shifts,correction_top]
  rw [Poly.send_zero,sub_zero]

private theorem complete:∀s b:(J).Mode, (Poly.merges s b full)↔b=complement s:=by decide

theorem coefficient (F:Poly J) (s:(J).Mode):
    WilsonThermometerNominatedConnectedStop.coefficients (properInvoice F 1) s=
      (if complement s=(J).quiet then 1 else 0)-
      (if complement s=face {0} then read F {0} else 0)-
      (if complement s=face {1} then read F {1} else 0)-
      (if complement s=face {2} then read F {2} else 0)+
      (if complement s=face {1,2} then 2*read F {1}*read F {2} else 0):=by
  rw [self]
  unfold WilsonThermometerNominatedConnectedStop.coefficients
  simp only [complete,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  change (1:Poly J).part _-(Poly.send _ _).part _-(Poly.send _ _).part _-(Poly.send _ _).part _+(Poly.send _ _).part _=_
  simp only [Poly.one_part,Poly.part_send]

theorem total (F:Poly J) {S:ℝ} (means:∀v:Fin 3,‖read F {v}‖≤S):
    ∑s:(J).Mode,‖WilsonThermometerNominatedConnectedStop.coefficients (properInvoice F 1) s‖≤1+3*S+2*S^2:=by
  let B:=correction (fun v=>read F {v})
  have coord(s:(J).Mode):WilsonThermometerNominatedConnectedStop.coefficients (properInvoice F 1) s=B.part (complement s):=by
    unfold WilsonThermometerNominatedConnectedStop.coefficients
    rw [self];simp only [complete,Finset.sum_ite_eq',Finset.mem_univ,if_true];rfl
  have inv:∀s:(J).Mode,complement (complement s)=s:=by decide
  let E:(J).Mode≃(J).Mode:=⟨complement,complement,inv,inv⟩
  calc
    _=∑s:(J).Mode,‖B.part (E s)‖:=Finset.sum_congr rfl fun s _=>congrArg (fun c:ℂ=>‖c‖) (coord s)
    _=∑s:(J).Mode,‖B.part s‖:=Equiv.sum_comp E (fun s=>‖B.part s‖)
    _=Poly.price (fun _=>1) B:=by simp [Poly.price,Poly.toll]
    _≤1+3*S+2*S^2:=WilsonThermometerRegisteredCenteredWallet.correction_price (fun _=>1) (fun _=>zero_lt_one) _ S
      (fun v=>by simpa only [one_mul] using means v)

end YM.Integration.WilsonThermometerRegisteredCenteredSelfComponents
