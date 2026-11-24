import YM.Integration.WilsonNeutralTwoPrintPathRead
import YM.Integration.WilsonNeutralReportPlacedWord
import YM.Integration.WilsonOriginalPrimerStampedRay

/-! On every true copy of the posted group word the held chart is the
translated finite tensor of that same independently appointed relative port. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathCopies
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

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonNeutralTwoPrintPathRead PositionX.Jet PowerSeries
open private curved from YM.Integration.WilsonOriginalPrimerReceipts
open scoped ContDiff

private theorem move_group {n':Side}(x:Site n')(B:Link G n')(z:ℝ):
    Haiku.life (fun _=>B ∘ jog x) z=Lattice.translate x (Haiku.life (fun _=>B) z):=by
  have turn:(jog x:Woods G n'→Woods G n')=fun z=>(z.1+x,z.2):=by
    funext v
    exact Prod.ext (add_comm _ _) rfl
  rw [turn]
  rfl

private theorem move_head {n':Side}(p:Lantern G Unit)(x:Site n')(a d h:ℕ)(rank:p.r ≤ a+d+1)(B:Link G n'):
    head p x a h B = head p 0 a h (B ∘ jog x):=by
  refine (curved p x a d h rank B).symm.trans (Eq.trans ?_ (curved p 0 a d h rank (B ∘ jog x)))
  apply congrArg (fun f:ℝ→ℝ=>someJ f (h+d+1))
  funext z
  rw [move_group,WilsonNeutralReportPlacedWord.atom,zero_add]

private theorem move_roll {n':Side}(a:Fin (e+1))(width:0<σ)(h:ℕ)(x:Site n')(B:Link G n'):
    (((T).roll a).folded a.val h).table n' (mingle B (WilsonElectedPrimaryTensor.pin x)) =
    (((T).roll a).folded a.val h).table n' (mingle (B ∘ jog x) (WilsonElectedPrimaryTensor.pin (0:Site n'))):=by
  let W:=(T).roll a
  have rank (v:W.Ty):(W.leg v).r ≤ a.val+mass k J+1:=by
    have roof:(W.leg v).r+(W.leg v).roots.length ≤ a.val+mass k J+2:=(((T).paid a).pinned v).tall
    have one:0<(W.leg v).roots.length:=List.length_pos_of_mem (((T).paid a).pinned v).owns
    omega
  have left:=WilsonNeutralTwoPrintPathRoll.complete W a.val (mass k J) h deep (by positivity:0<2*σ) ((T).paid a) x B
  have right:=WilsonNeutralTwoPrintPathRoll.complete W a.val (mass k J) h deep (by positivity:0<2*σ) ((T).paid a) 0 (B ∘ jog x)
  exact HasSum.unique (left.congr_fun fun v=>(move_head (W.leg v) x a.val (mass k J) h (rank v) B).symm) right

private theorem shift_diag {n':Side}(F:Gen ℝ (Woods G n'))(cap:ℕ)(x:Site n')(B:Link G n'):
    diagonal cap (fun b z=>F b (jog (-x) ∘ z)) B=diagonal cap F (B ∘ jog x):=by
  simp only [diagonal,Blue.toll]
  apply sum_congr rfl
  intro b _
  let equiv:(Fin b→Woods G n')≃(Fin b→Woods G n'):=Equiv.piCongrRight fun _=>jog (-x)
  apply Fintype.sum_equiv equiv
  intro z
  congr 1
  apply prod_congr rfl
  intro i _
  change B (z i)=B (jog x (jog (-x) (z i)))
  congr 1
  apply Prod.ext
  · change (z i).1=x+(-x+(z i).1)
    abel
  · rfl

def chart (n':Side)(x:Site n'):PChart G n':=
  skewV (x-wrap n' o) ((tuftV (touch t J) (shifted (baton P₀ (e+1)) o)).1 n')

local notation "filed" => chart Y lo N c X o t u
local notation "tensor" => WilsonNeutralTwoPrintPathRead.relative Y lo N c X o t u

include enrolled included pin positive older in
theorem admitted (n':Side)(x:Site n'):
    shellK (mass k J) (filed n' x) ∧ ∀h,Pure (filed n' x h):=by
  have law:=(WilsonOlderFreshConnectedBinding.filed R Y lo enrolled N c X included pin positive older o u 0 (Nat.zero_le _)).1
  have realLaw:=law.tuft (touch t J)
  exact ⟨skew_shell _ (realLaw.span n') _,fun h=>skew_pure _ _ (realLaw.pale n' h)⟩

theorem coordinates (width:0<σ)(closed:Cloze D k Y Credit.leanC)
    (tickets:Insure n (mass k univ) Y Credit.leanC):
    WilsonOriginalPrimerStampedRay.Matched (T) (filed):=by
  intro h through n' x B
  have law:=(WilsonOlderFreshConnectedBinding.filed R Y lo enrolled N c X included pin positive older o u h through).2.2
  have slots (b:ℕ)(z:Fin b→Woods G n'):
      filed n' x h b z=(tensor h) b (jog (-x) ∘ z):=by
    change touch t J ((shifted (baton (P₀) (e+1)) o).1 n' h b (jog (-(x-wrap n' o)) ∘ z))=_
    rw [law n' b]
    congr 2
    funext i
    apply Prod.ext
    · change -(x-wrap n' o)+(z i).1=wrap n' o+(-x+(z i).1)
      abel
    · rfl
  have support:still (filed n' x h) (mass k J+h+1):=fun b tall=>
    (admitted R Y lo enrolled N c X included pin positive older o t u n' x).1 h b (by omega)
  have finite:MvPolynomial.eval B (coeff h (flash (filed n' x)))=diagonal (mass k J+h) (filed n' x h) B:=by
    rw [Blue.flash,coeff_mk,Blue.visible support,map_sum]
    rfl
  rw [finite,show filed n' x h = (fun b z=>(tensor h) b (jog (-x) ∘ z)) from funext fun b=>funext (slots b),
    shift_diag,←WilsonNeutralTwoPrintPathRead.register R Y lo enrolled N c X included pin positive older deep sw o t u width closed tickets h through]
  exact sum_congr rfl fun a _=>(move_roll R Y lo enrolled N c X included pin positive older deep sw o t u a width h x B).symm

end YM.Integration.WilsonNeutralTwoPrintPathCopies
end
