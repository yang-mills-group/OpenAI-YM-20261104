import YM.Integration.WilsonNeutralTwoPrintPathJet
import YM.Integration.WilsonOriginalPrimerDischarge

/-! Each funded lamp of the independently selected relative port, on the
original torus, with all colours and the actual scalar angular labelling. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathRoll
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
variable {G:Gauge}{n e j:ℕ}{k D:Fin n → ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
variable (R:Run G)(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor ≤ j)(enrolled:Paid R Y lo D k δ σ)
variable (N:ℕ) (c:Fin n)(X:Input Y lo S k D A)(included:J⊆S)(pin:c∈J)(positive:0 ≤ A)
variable (older:j<N)(deep:0 < mass k J)(sw:0 ≤ σ)(o:Cover)(t:Case D)(u:Frill J c)
local notation "M₀" => R.family.path.levels.clock.hatBeta j^δ*A^J.card

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
local notation "T" => WilsonOlderFreshConnectedBirth.issued R Y lo enrolled N c X included pin positive older deep sw o t u
local notation "P₀" => packetH J (output X J N) (mass k J) (e+1) c o u

open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series
open private curved from YM.Integration.WilsonOriginalPrimerReceipts
open scoped ContDiff

theorem complete {G₀:Gauge}{n':Side}(W:Poetry.Roll G₀ Unit)(a d h:ℕ)(d0:0<d){σ₀ C:ℝ}(hs:0<σ₀)
    (book:W.Faith {()} () (a+d+2) σ₀ C)(s:Site n')(B:Link G₀ n'):
    HasSum (fun u:W.Ty=>head (W.leg u) s a h B)
      ((W.folded a h).table n' (mingle B (WilsonElectedPrimaryTensor.pin s))):=by
  have rank (v:W.Ty):(W.leg v).r≤a+d+1:=by
    have hi:(W.leg v).r+(W.leg v).roots.length ≤ a+d+2 := (book.pinned v).tall
    have owned:0<(W.leg v).roots.length:=List.length_pos_of_mem (book.pinned v).owns
    omega
  have source:=WilsonOriginalPrimerRollJet.original W a d h d0 hs book s (fun _=>B) contDiffAt_const
  rw [weigh_const] at source
  exact source.congr_fun fun u=>(curved (W.leg u) s a d h (rank u) B).symm

abbrev Labels (a:Fin (e+1)):=Σ r:Fin (mass k J+a.val+1),Σ _z:RadP G r.val,Stationary.Ink G r.val

def locate (a:Fin (e+1)):Labels (G:=G) (k:=k) (J:=J) a ≃ ((T).roll a).Ty where
  toFun z:=⟨⟨z.1,(u,z.2.1),z.2.2⟩,rfl⟩
  invFun z:=⟨z.1.1,z.1.2.1.2,z.1.2.2⟩
  left_inv _:=rfl
  right_inv:=by
    rintro ⟨⟨r,⟨⟨u',z⟩,i⟩⟩,h⟩
    change u'=u at h
    subst u'
    rfl

local notation "pt" => locate R Y lo enrolled N c X included pin positive older deep sw o t u
local notation "ink" => WilsonOlderFreshConnectedAssembly.chart R Y lo enrolled N c X included pin positive older deep sw o t u

theorem colour {n':Side}(a:Fin (e+1))(r:Fin (mass k J+a.val+1))(z:RadP G r.val)
    (h:ℕ)(B:Link G n'):
    (∑b:Stationary.Ink G r.val,head (((T).roll a).leg (pt a ⟨r,z,b⟩)) (0:Site n') a.val h B)=
      diagonal (mass k J+h) (ink a r z h) B:=by
  let f (b:Stationary.Ink G r.val):Link G n'→ℝ:=
    Near.meter (((T).roll a).leg (pt a ⟨r,z,b⟩)).atom (0:Site n')
  have height (b:Stationary.Ink G r.val):(((T).roll a).leg (pt a ⟨r,z,b⟩)).r=r.val:=rfl
  by_cases active:a.val≤h
  · have cap:r.val+(h-a.val) ≤ mass k J+h:=by have bound:=r.isLt;omega
    change _=diagonal _ (if a.val≤h then sprig (fun A=>∑b,f b A) r.val (h-a.val) else 0) B
    rw [if_pos active,sprig_read _ _ _ _ cap]
    have smooth (b:Stationary.Ink G r.val):ContDiffAt ℝ ω (f b) 0:=
      (Helmet.frameGrade (((T).roll a).leg (pt a ⟨r,z,b⟩)).atom (0:Site n')).smooth
    simp only [head,if_pos active,height]
    change (∑b,Radial.jet (f b) (h-a.val+r.val) B)=_
    rw [Nat.add_comm r.val,Radial.jet,
      iteratedFDeriv_fun_sum_apply (fun b _=>(smooth b).of_le le_top)]
    simp only [_root_.sum_apply,Radial.jet,Finset.mul_sum]
  · change _=diagonal _ (if a.val≤h then _ else 0) B
    simp [head,active,diagonal]

theorem forRoll {n':Side}(width:0<σ)(a:Fin (e+1))(h:ℕ)(B:Link G n'):
    (((T).roll a).folded a.val h).table n' (mingle B (WilsonElectedPrimaryTensor.pin (0:Site n'))) =
      ∑r:Fin (mass k J+a.val+1),∑'z:RadP G r.val,diagonal (mass k J+h) (ink a r z h) B:=by
  let f (v:((T).roll a).Ty):=head (((T).roll a).leg v) (0:Site n') a.val h B
  have native:=complete ((T).roll a) a.val (mass k J) h deep (by positivity:0<2*σ) ((T).paid a) (0:Site n') B
  have ordered:=((pt a).hasSum_iff.mpr native)
  have sums:Summable (fun v=>f (pt a v)):=ordered.summable
  rw [←ordered.tsum_eq]
  change (∑'v:Labels (G:=G) (k:=k) (J:=J) a,f (pt a v))=_
  rw [sums.tsum_sigma,tsum_fintype]
  apply sum_congr rfl
  intro r _
  rw [(sums.sigma_factor r).tsum_sigma]
  apply tsum_congr
  intro z
  rw [tsum_fintype]
  exact colour R Y lo enrolled N c X included pin positive older deep sw o t u a r z h B

end YM.Integration.WilsonNeutralTwoPrintPathRoll
end
