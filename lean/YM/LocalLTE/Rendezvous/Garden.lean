import YM.LocalLTE.Newborn.Contract
import YM.LocalLTE.Rendezvous.Destined
/-! Rate conversion: for the chosen order, both inlet scales. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Filter Function Lattice Wilson Pressure RG RG.Supply Input Precision
open Push.PriceCompiler Push.SectorMeasure Push.AbsoluteSums ConnectedActivityE6 AnalyticBridge VerifiedReset
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
open LocalLTE.Inset Org
open ThroughLaunch WilsonStartup Extra.Histories Next.Scheduling Next.Foundations UVNext.CouplingReset
open Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.PriceCompiler ThroughLaunch Height Opera Roof Roost
open Progress.DirectedRecipe Time WilsonStartup Extra.Histories Next.Foundations
open ClockB Urns
open LocalLTE.Fan LocalLTE.Fan.Pastel Coat
variable {G:Gauge}(L:Side)(p M:ℕ)
-- x to 2*z band covers both adjacent. b≥ x/2>0. r = κ
local notation "f" x => betaF G x L
-- Converts.M.V strict all scales. Additional for real Raw amplitudes h tx.L also during 
-- calendar.Guarantees.F.Att.E.Raw powers fixed ppTag.Scale.
variable (ζ:ℝ) (hζ:(↑(p+1):ℝ)/2 < ζ)
variable {s:Sheet G}{D: Rolls s}{P:Protection D}
def MintZ (V:Delays P) (ζ:ℝ) (p:ℕ):Prop:=∀ j i,StepStages j i→∀ x≥V.betaEntry j,∀ β:ℝ,betaF G x (D.L j)/2 ≤ β→β ≤ 2*betaF G x (D.L j)→ (betaF G x (D.L j))^(-ζ) ≤ gStep β ^(p+1:ℕ)
include hζ
lemma pocketsZ (V:Delays P) : ∃ W:Delays P, DelayLe V W∧ ∀ Y:Delays P,DelayLe W Y→MintZ Y ζ p:=by
   have h (j i:ℕ)(_:StepStages j i):∀ᶠ x in atTop,∀ β:ℝ,betaF G x (D.L j)/2 ≤ β→β ≤2*betaF G x (D.L j)→(betaF G x (D.L j))^(-ζ) ≤ gStep β ^ (p+1):=by
       filter_upwards [Urns.actualG (D.L j) (↑(p+1)) _ _ (Rate.power (G:=G) (a:=-ζ)) (by linarith), Delay.shift_pos G (D.L j)] with x hx he β h ht
       have hz : 0 < β := (half_pos he).trans_le h; exact (hx _ h ht).trans_eq (Real.rpow_natCast ..)
   obtain ⟨x,-,hx,hP⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ _ (h j))
   exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun Y he i j hh x ht=> hP i x ((he.beta i).trans ht) j hh⟩
end YM.PhysicalNext.Repeat.Mallow
