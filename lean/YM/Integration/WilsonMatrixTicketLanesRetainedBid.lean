import YM.Integration.WilsonMatrixTicketLanesRetainedPlacement
import YM.Integration.WilsonMatrixTicketLanesRetainedAngular
import YM.Integration.WilsonMatrixTicketLanesRetainedMoments
import YM.Integration.WilsonMatrixTicketLanesDescentContractions

/-! The signed microscopic Wick coefficient of the actual deposited Wilson operators at all paid retained pins. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedBid
open Function Filter MeasureTheory Finset Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial PertExtension.GaussianScore
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Spool FVA2
open Next.Rank Next.Rank.Normal
open FVA2.CityHistory FVA2.Wick ThermalShortcuts.ThermalJets WilsonConditionalTaylorThermalCensus
open WilsonConditionalTaylorThermalBidScore WilsonMatrixTicketLanesDescentWords WilsonCoherentLampTicket
open WilsonMatrixTicketLanesReflectedInner WilsonMatrixTicketLanesRetainedAngular WilsonMatrixTicketLanesRetainedPlacement
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (T : Tree.Forest S.ratio)
local notation "layer" => Descent.push S T Descent.nil

def upstairs : Future G S T →ₗ[ℝ] Coordinates G layer where
  toFun:=WilsonMatrixTicketLanesRetainedPlacement.lift S T
  map_add' x y:=by funext e;cases e with | inl a=>rfl | inr a=>exact a.elim
  map_smul' t x:=by funext e;cases e with | inl a=>rfl | inr a=>exact a.elim

variable (R : Run G) {I : Type} [Fintype I] (k : I→ℕ) (i : ∀ s,(R.family.labels.level (k s)).Index)
    {N p : ℕ} {c : Side} (S : StepData c (R.family.side N p)) (T : Forest S.ratio) (x : I→Site (R.family.side N p))
local notation "d" => Descent.push S T Descent.nil
local notation "stencil" => entries R.family k i (fun j=>CoefficientBridge.run_valuation R (k j))
local notation "lampsAt" => lamps R k i

def freeLeg (v : ticket stencil) : Module.Dual ℝ (Future G S T) :=
  (leg G d (face stencil x v) (WilsonConditionalTaylorThermalCensus.color stencil v)).comp (upstairs S T)

/-- The physical signed coefficient on the original finite forest. Unpaired factors use its actual held-field skew. -/
def value (large : Bid.Larger (G:=G) S) (tag : S.Choices) (nil : (Descent.nil (top:=R.family.side N p)).Tags)
    (u : Directions G c) (part : Bool) : ℝ :=
  ∑m∈rows stencil,bill stencil part m * ∑ t∈(parties stencil m).powerset,
    (∏v∈(parties stencil m)\t,freeLeg R k i S T x v (changeField S T large tag nil u)) *
    (blend (FVA2.Wick.color (law S T large tag nil) (freeLeg R k i S T x)) 0 (glyphs id t)).re

/-- The genuine full complex roster includes location, orientation, wrapped colors, its true homogeneous
grade, and independently filed angular labels. Both real branches are evaluated on the same retained field. -/
theorem original {P : Parcel.Oven S.patch} (X : P.Form G) (offer : P.Offers X S.kernel) (Z : ChartRatio G) (hz : LocalRatio Z)
    (large : Bid.Larger (G:=G) S) (tag : S.Choices) (nil : (Descent.nil (top:=R.family.side N p)).Tags)
    (u : Directions G c) (pin : ∀e,‖u e‖≤X.Q) (part : Bool) :
    Spool.rankℝ lampsAt S T X Z u x part 0=value R k i S T x large tag nil u part := by
  let μ:=tangent G T.Free
  let Γ:=law S T large tag nil
  let M:=stencil
  let a:=changeField S T large tag nil u
  let e:=freeLeg R k i S T x
  have test:= (WilsonMatrixTicketLanesDescentWords.purchased R k i d x part).1
  rw [WilsonMatrixTicketLanesRetainedRoster.original lampsAt S T x part X offer Z hz large tag nil u pin]
  have filed (y : Future G S T) :
      Radial.jet (WilsonCoherentLampTicket.source lampsAt S T x part) (power lampsAt) (y+a,u)=
      ∑m∈rows M,bill M part m*Law.product e (parties M m) (y+a) := by
    rw [WilsonMatrixTicketLanesRetainedPlacement.jet lampsAt S T x part test]
    exact WilsonConditionalTaylorThermalBidScore.original R.family k i (fun s=>CoefficientBridge.run_valuation R (k s)) d x R.makes part (upstairs S T (y+a))
  change Γ.average μ (fun y=>Radial.jet (WilsonCoherentLampTicket.source lampsAt S T x part) (power lampsAt) (y+a,u))=_
  simp_rw [filed]
  simpa only [value,Function.comp_id,id_eq] using WilsonMatrixTicketLanesRetainedMoments.total Γ e μ id (rows M) (parties M) (bill M part) a

/-- No extra input to the actual regulator's signed coefficient, including at a nonzero retained site. -/
theorem series (large : Bid.Larger (G:=G) S) (tag : S.Choices) (nil : (Descent.nil (top:=R.family.side N p)).Tags)
    (u : Directions G c) :
    WilsonCoherentJointReturn.series lampsAt S T R.metals.O u x large tag nil 0=
      ⟨value R k i S T x large tag nil u false,value R k i S T x large tag nil u true⟩ := by
  obtain ⟨P⟩:=Parcel.Oven.builtafter (S).patch
  have positive : 0<‖u‖+1:=by positivity
  obtain ⟨X,width,offer⟩:=Parcel.Oven.fund (G:=G) (K:=S.kernel) P large.1 (‖u‖+1) positive
  have price (e) : ‖u e‖≤X.Q:=by rw [width];exact (norm_le_pi_norm u e).trans (by linarith)
  have got:=WilsonCoherentJointReturn.same lampsAt S T R.metals.O u x large tag nil X R.alloy.B.ratio offer price
  rw [←got]
  exact Complex.ext (original R k i S T x X offer R.metals.O R.alloy.B.ratio large tag nil u price false)
    (original R k i S T x X offer R.metals.O R.alloy.B.ratio large tag nil u price true)

end YM.Integration.WilsonMatrixTicketLanesRetainedBid
