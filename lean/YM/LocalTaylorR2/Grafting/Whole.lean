import YM.LocalTaylorR2.Grafting.Berth
/-! Family witness consumer for all polynomially-budgeted LOCAL INPUTS. Allows
   the actual continuum Growth/integration problems to charge later projections. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Song Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
open Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe Roost Opera
open Mallow Blush Lattice Daisy Lotus Daisy.Charity.RG12 UVNext.CouplingReset Extra.Histories Next.Foundations Planned.GuardedAtom
open CalendarStep Recoil
open Marker
open Guard

variable {G:Gauge}
open AnalyticBridge.VerifiedReset OPE _root_.YM.Marker MergeProof Accent Merge Menu Mallow.Many
variable {C: Family G}{g:G.Simple}{Δ:Daisy.Charity.RG12.Decal G}(U:Couture C g (Grafting.invite Δ)) (h:Grafting.Club U)
include h
open Grafting
-- readable same τ coupling. `Race.rich` exhibits far beyond for K analytic.Power.After inserting actual horizon. uniform for any requested exponent Strong: no analytic premise.
lemma circuit_order (p r K C₀:ℕ)(ε:ℝ)(hf:0<ε)(hu:ε≤1) : ∀ᶠ m:ℕ in atTop, let a:= U.cost.B.a; r ≤ (a.budget m).order∧ r ≤ (a.budget m).power∧
       ∀ N n:ℕ,(hm:m<N)→ let g':= Pert.Asymptotics.regulatorRun C N n (m+1); let v:=(Real.sqrt 2*g')^((p+1:ℝ)-ε); let Y:=U.uses; let z:=a.clock.hatBeta (m+1); let V₀ := Y.realBeat 0 N n (m+1); let y:= escalate K C₀ p; let d:= Reel.upfront z (troop y) ε; let ψ:=Reel.descend U.factor Y (troop y) N n (m+1)
         Reel.Affords V₀ a (m+1) ψ d ∧ ∀ (Z ι:Type)[DecidableEq Z][Fintype Z][Fintype ι](B:Marker.Census Z)(o:Z→Site (a.S.side (m+1) n))(s:ι→Menu.Hat B V₀), Fintype.card Z ≤ C₀ → Menu.Offer o s 1 (V₀.p.B) (V₀.p.supportExponent-4) (z^K) → Race U.factor Y hm o s K p C₀ ψ ε v (2*z^(21/10:ℝ)*d):=by
   filter_upwards [Orbit.boarding U h.menu.prelude p r K C₀ ε hf hu,h.aid (escalate K C₀ p) r ε hf hu,CalendarStep.lasts U.factor U.uses U.cellar (escalate K C₀ p) r ε hf] with m hm h' he
   refine ⟨hm.1,hm.2.1,fun N n hN=>?_⟩; intro g' v Y z V₀ y d ψ
   have hA:= h'.2.2.2.2 N n hN|>.2.2.2.1
   refine ⟨hA,fun Z ι _ _ _ B o s ht hx=>?_⟩
   exact accomplished U.factor Y hN o s K p C₀ ψ (Grafting.fortifies U) he.1 ht ε v hf (hm.2.2 N n hN Z ι B o s ht hx) (Reel.prize U n N (m+1) hN|>.2 p ε hu) hA

end YM.LocalTaylorR2.Orbit
