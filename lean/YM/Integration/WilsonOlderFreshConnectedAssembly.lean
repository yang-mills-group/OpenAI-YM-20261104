import YM.Integration.WilsonOlderFreshConnectedBinding
import YM.Integration.WilsonOlderFreshConnectedBirth
import YM.Integration.WilsonOlderFreshConnectedReceiver
import YM.Integration.WilsonOlderFreshUnaryCourse
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedAssembly
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

include included pin positive older in
theorem reserve (closed:Cloze D k Y Credit.leanC)(tickets:Insure n (mass k univ) Y Credit.leanC):
    ∃θ C:ℝ,0<θ ∧ Rains P₀ (e+1) θ C:=by
  let y:=toe J c o u
  have readyAt:=ready X included positive older closed y
  have card:J.card≤n:=by simpa using Finset.card_le_card (Finset.subset_univ J)
  have cap:mass k J ≤ mass k univ:=by
    unfold mass
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun v _ _=>Nat.zero_le _)
  have budget:0≤price Y k D A J j:=
    mul_nonneg (zero_le_one.trans (Credit.purchase _ (Y.depth j lo))) (pow_nonneg positive _)
  have h:=Rolls.posting (tickets.proof j lo) y (output X J N y) pin cap card _ budget
    readyAt.1 readyAt.2 (le_refl (e+1))
  exact ⟨_,_,(tickets.proof j lo).affordable,h.1⟩

def chart {n':Side}(a:Fin (e+1))(r:Fin (mass k J+a.val+1))(z:RadP G r.val)(h:ℕ):Gen ℝ (Woods G n') :=
  if a.val≤h then sprig
    (fun A=> ∑b, Near.meter (((T).roll a).leg ⟨⟨r,(u,z),b⟩,rfl⟩).atom (0:Site n') A)
    r.val (h-a.val) else 0
local notation "ink" => chart R Y lo enrolled N c X included pin positive older deep sw o t u
local notation "χ" => touch t J

theorem row {n':Side}(wage:∃θ C:ℝ,0<θ ∧ Rains P₀ (e+1) θ C)
    (a:Fin (e+1))(r:Fin (mass k J+a.val+1))(h b:ℕ)(x:Fin b→Woods G n'):
    HasSum (fun z=>ink a r z h b x) (χ ((bolus (P₀ a r) a.val).1 n' h b x)):=by
  obtain ⟨θ,C,wide,honest⟩:=wage
  have bill:=(((honest.2 a.val a.isLt).2 r).2)
  have raw:=elevated wide bill a.val n' h b x
  have scalar:=(touch t J).hasSum raw
  apply scalar.congr_fun
  intro z
  have hit:=WilsonOlderFreshConnectedBinding.angular R Y lo enrolled N c X included pin positive older
    deep sw o t u a.val (by omega) r z (n':=n')
  exact (congrFun (congrFun (congrFun hit h) b) x).symm

/-- Whole cofinal finite chart on the actual relative placement, with the connected vacuum and scalar. -/
theorem cofinal {n':Side}(wage:∃θ C:ℝ,0<θ ∧ Rains P₀ (e+1) θ C)
    (h:ℕ)(heard:h≤e)(b:ℕ)(x:Fin b→Woods G n'):
    χ (Carp.plume ((output X J N (toe J c o u)).2 h b) n' x) =
      ∑a:Fin (e+1),∑r:Fin (mass k J+a.val+1),
         ∑'z,ink a r z h b (jog (-wrap n' o) ∘ x):=by
  let v:=jog (-wrap n' o) ∘ x
  have page:=WilsonOlderFreshConnectedBinding.filed R Y lo enrolled N c X included pin positive older
    o u h heard
  rw [←page.2.2 n' b]
  change χ ((baton P₀ (e+1)).1 n' h b v)=_
  have split:
      χ ((baton P₀ (e+1)).1 n' h b v)=
        ∑a:Fin (e+1),∑r:Fin (mass k J+a.val+1),χ ((bolus (P₀ a r) a.val).1 n' h b v):=by
    simp only [baton,linesR,Prod.fst_sum,Finset.sum_apply,map_sum]
    exact (Fin.sum_univ_eq_sum_range (fun f:ℕ=>∑r:Fin (mass k J+f+1),
      χ ((bolus (P₀ f r) f).1 n' h b v)) (e+1)).symm
  rw [split]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  exact (row R Y lo enrolled N c X included pin positive older deep sw o t u wage a r h b v).tsum_eq.symm

theorem original {n':Side}(closed:Cloze D k Y Credit.leanC)(tickets:Insure n (mass k univ) Y Credit.leanC)
    (h:ℕ)(heard:h≤e)(b:ℕ)(x:Fin b→Woods G n'):
    χ (Carp.plume ((output X J N (toe J c o u)).2 h b) n' x) =
      ∑a:Fin (e+1),∑r:Fin (mass k J+a.val+1),
         ∑'z,ink a r z h b (jog (-wrap n' o) ∘ x):=
  cofinal R Y lo enrolled N c X included pin positive older deep sw o t u
    (reserve Y lo N c X included pin positive older o u closed tickets) h heard b x

end YM.Integration.WilsonOlderFreshConnectedAssembly
end
