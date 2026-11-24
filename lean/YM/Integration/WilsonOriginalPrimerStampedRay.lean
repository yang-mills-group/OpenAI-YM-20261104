import YM.Integration.WilsonOriginalPrimerCopiedRay
import YM.Integration.WilsonOlderFreshGraphCommission

/-! One counted primary enrolment, valid on all copied original tori and
on the pupil's actual stored portfolio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerStampedRay
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{Q d:ℕ}{σ:ℝ}(C:WilsonOlderFreshGraphSlate.Copy G d Q σ)
variable (Z:∀n:Side,Site n→PChart G n)

def Matched :Prop:=∀j≤Q,∀(n:Side)(x:Site n)(v:Link G n),
    MvPolynomial.eval v (coeff j (flash (Z n x)))=
      ∑u:Fin (Q+1),((C.roll u).folded u j).table n (mingle v (WilsonElectedPrimaryTensor.pin x))

variable (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)
variable {n:Side}(h:n.val∣(fine R i per).val){P P':Earn.Passport n Unit}
variable {H:Marker.Census Unit}(S:Earn.Binder P H)(E:Unit→Set ℂ)(t:Affinity.Wallet E)
variable {I:Type}(M:I→Earn.Row P' H G (Affinity.Wallet E))

theorem received (passport:P'=P)(names:I=C.Roster)(rows:HEq M (C.rows S E))
    (cap:∀t,‖value E t‖≤1)(σ0:0<σ)(layout:Layout G)(stock:Finset Age)
    (shell:∀n x,shellK d (Z n x))(pure:∀n x j,Pure (Z n x j))
    (filed:Matched C Z)(r:ℕ)(hr:r≤Q)(B:fieldDir G (coarse R i per) 1):
    WilsonOriginalEarnedUnaryPage.Ray R N i per hi F
      (copyColor h M (fun _=>d) (fun z=>(M z).paint t) layout stock) B (submitted S)
      (value E t) (located h S.center (Z (fine R i per))) r:=by
  subst P'
  subst I
  obtain rfl:=eq_of_heq rows
  exact WilsonOriginalPrimerCopiedRay.original R N i per hi F h S C.roll C.fare σ C.paid C.legal C.positive
    E cap t σ0 layout stock (Z (fine R i per)) r (shell _) (pure _)
    (fun l hl x A=>filed l (hl.trans hr) _ x A) B

end YM.Integration.WilsonOriginalPrimerStampedRay
end
