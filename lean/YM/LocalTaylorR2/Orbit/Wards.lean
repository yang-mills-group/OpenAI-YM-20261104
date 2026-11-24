import YM.LocalTaylorR2.Orbit.Chord
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
variable {C: Family G}{g:G.Simple}{Δ:Daisy.Charity.RG12.Decal G}(U:Couture C g (Orbit.modes Δ)) (h:Library U)
include h
-- after unweighting AND same witnesses call library
lemma boarding (p r K C₀:ℕ)(ε:ℝ)(hf:0<ε)(hu:ε ≤1) : ∀ᶠ m:ℕ in atTop, let a:=U.cost.B.a; r ≤ (a.budget m).order∧ r ≤ (a.budget m).power∧
       ∀ N n:ℕ,(hm:m<N)→ let g':= Pert.Asymptotics.regulatorRun C N n (m+1); let v:=(Real.sqrt 2*g')^((p+1:ℝ)-ε); let Y:=U.uses; let z:=a.clock.hatBeta (m+1); let V₀ := Y.realBeat 0 N n (m+1)
         ∀ (Z ι:Type)[DecidableEq Z][Fintype Z][Fintype ι](B:Marker.Census Z)(o:Z→Site (a.S.side (m+1) n))(s:ι→Menu.Hat B V₀), Fintype.card Z ≤ C₀ → Menu.Offer o s 1 (V₀.p.B) (V₀.p.supportExponent-4) (z^K) → Orbit.Rich U.factor Y hm o s K p C₀ ε v:=by
   let R:=U.factor; let S:= U.uses; let a:= U.cost.B.a; let L:= U.cellar
   let u₀:= escalate K C₀ p; have hA:Mallow.RG12.Earned (orbitD G) U.factor.shape U.cost.delay:= fun _ _ hv _ ht=> U.couture _ _ hv _ ht|>.2.2.2.2.1
   filter_upwards [h.window u₀ r ε hf hu,CalendarStep.lasts R S L u₀ C₀ ε hf
     ] with m hS hm
   refine ⟨hS.1,hS.2.1,fun N n hN=>?_⟩; intro g' v Y z V₀ Z ι _ _ _ B o s hp hv
   let Φ:=a.clock.op m n
   let X:=Cellar.yard (roseA Y) U.cellar; have hh : Pert.Asymptotics.regulatorRun X N n (m+1)=g':= congr_arg (fun F=> Pert.Asymptotics.regulatorRun F N n (m+1)) (show X=C from U.belongs.symm)
   have hR:= priceBoundActual (n:=n) R S L p hN ε hu; rw [hh] at hR
   apply Orbit.richer R S hN o s K p C₀ (h.tilt m) (h.tilt (m+1)) hA U.bandage.r hp hm.1 ?_ hv ε v hm.2.1 hf.le hR
   have hw : C₀≤ a.clock.J m:= hm.2.2.1
   intro i
   exact (Finset.card_filter_le ..).trans (le_trans (le_of_eq (Finset.card_univ)) (hp.trans (hw.trans ((a.fits.mono (Nat.le_succ m)).trans (Nat.le_add_right ..)))))
-- notation callback typo.
end YM.LocalTaylorR2.Orbit
