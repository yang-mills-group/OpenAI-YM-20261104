import YM.Integration.WilsonMeasuredPublicEntranceTransferCofinalSurvey
import YM.Integration.WilsonOriginalPublicTrialPhaseGrant
/-! The original Gibbs price for the exact compensated finite optical words, evaluated on the same signed smoothly tested pins. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option quotPrecheck false
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferSubmittedPhase
open OPE Next.Rank Overlay Bid Push.GridApprox MergeProof Ribbons Accent ManyCopies
open PertExtension PertExtension.LatticePT
open OPE.Therm
open Trace.Physical.GermGraph
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Cells
open PhysicalNext.Repeat.Legato Spec
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units)
open WilsonMeasuredPublicEntranceTransferCampusSurvey (submittedWord reflection)
open WilsonMeasuredPublicEntranceBookedSurvey (Press model)
open WilsonMeasuredPublicEntranceTransferProfileMass (tested phase size)
open WilsonMeasuredPublicEntranceBookedRegulators (collect)
open WilsonOriginalPublicTrialPhaseGrant (Grant)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{D n f K N p u:ℕ}
local notation "C₀" => R.family
variable (d:Fin n→Fin (D+1))
local notation "grade" => fun i=>(d i).val

def fitted (file:Filed R (fun i=>(d i).val) K)(Y:∀i,(C₀).label (d i).val)(marked:Fin n→Bool):
    (i:Fin n)→(C₀).label (d i).val:=
  units R grade K (fun i=>Motion.patch ((C₀).labels.level (d i).val) (reflection (marked i))
    (doses R grade file.station (N:=N) (per:=p) (file.A N p) Y i))

def site (fk:f≤K)(o:Fin n→ Cover)(i:Fin n):Site ((C₀).side K p):=
  ((C₀).S.toDepth fk p).embed (wrap ((C₀).side f p) (o i))

theorem at_field (file:Filed R grade K)(fk:f≤K)(Y:∀i,(C₀).label (d i).val)(marked:Fin n→Bool)(o:Fin n→ Cover):
    submittedWord (N:=N) (p:=p) (R:=R) d file fk Y marked o=
      WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) grade (site (R:=R) (p:=p) fk o)
        (fitted (N:=N) (p:=p) d file Y marked):=by
  rfl

variable {m:ℕ}{E:Type}[Fintype E]{φ:Test n}{r:ℝ}{rp:0<r}{ref:E→E4}
theorem original (P:Press R φ r rp f m ref)(fk:f≤K)(live:K≤N)(uk:u≤K)
    (file:(Fin n→Bool)→Filed R grade K)(Y:∀_b:Fin n→Bool,∀i,(C₀).label (d i).val)
    (marked:Fin n→Bool)(fee:(Fin n→Bool)→ℝ)
    (paid:∀b (i:P.Entry)(a:(model P i).sample),Nonempty (Grant R (N:=N) grade
      (site (R:=R) (p:=p) fk (P.port i a)) (fitted (N:=N) (p:=p) d (file b) (Y b) marked) uk (fee b)))
    (α:(Fin n→Bool)→ℂ):
    let Q:=fun b (i:P.Entry) (a:(model P i).sample)=>submittedWord (N:=N) (p:=p) (R:=R) d (file b) fk (Y b) marked (P.port i a)
    let Gibbs:=fun b i a=>∫U,Q b i a U ∂scene (C₀).path N p K
    let Ear:=fun b i a=>actualTransport (C₀) (N:=N) (Q b i a) uk 1
    ‖phase P α Gibbs Ear‖≤∑b,‖α b‖*(size P*fee b):=by
  classical
  intro Q Gibbs Ear
  have point (b) (i:P.Entry)(a:(model P i).sample) : ‖Gibbs b i a-Ear b i a‖≤fee b:=by
    obtain ⟨grant⟩:=paid b i a
    exact WilsonOriginalPublicTrialPhaseGrant.original R grade _ _ uk live grant
  unfold WilsonMeasuredPublicEntranceTransferProfileMass.phase WilsonMeasuredPublicEntranceTransferProfileMass.tested
  calc
    _≤∑b,‖α b*collect P (fun i a=>Gibbs b i a-Ear b i a)‖:=norm_sum_le ..
    _≤_:=sum_le_sum fun b _=>by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have single:=WilsonMeasuredPublicEntranceTransferProfileMass.cell P (point b)
      simpa only [collect,smul_sub,Finset.sum_sub_distrib,mul_sub] using single

end YM.Integration.WilsonMeasuredPublicEntranceTransferSubmittedPhase
end
