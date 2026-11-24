import YM.LocalTaylorR2.Orbit.Sustained
import YM.LocalTaylorR2.Capstone.AtHand
import YM.MergeProof.Wax
/-! Event witness on the actual Outfit. From Pulse.Op and Tickets; append
  Volume-independent unweighted mark budgets later (after Momentum geometrical fees). -/
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
-- Any extra demand δ. Horizons simultaneous as needed.
abbrev modes (δ:Daisy.Charity.RG12.Decal G):= Capstone.wrap ((orbitD G).paired δ)
variable {C: Family G}{g:G.Simple}{Δ:Daisy.Charity.RG12.Decal G}(U:Couture C g (modes Δ))
set_option quotPrecheck false
local notation "a"=>U.cost.B.a
local notation "t"=> U.cost.B.a.clock
local notation "G!"=> C -- remove
open _root_.YM.Marker
-- compatibility declaration keeps genuine consumer equations. no independently chosen model.
structure Library : Prop where
    horizon : Capstone.Manifest U
    tilt (m:ℕ) : (U.cost.B.a.budget m).supportExponent=100
    mint : Minty U.factor.shape (·+1) U.cost.delay
    window (p r:ℕ)(ε:ℝ)(hf:0<ε)(hu:ε ≤1): ∀ᶠ m:ℕ in atTop, r ≤ (((a).budget m).order)∧ r ≤ (((a).budget m).power) ∧ r ≤ (t).J m ∧
       ∀ N n:ℕ,(hm:m<N)→ let g:= Pert.Asymptotics.regulatorRun C N n (m+1); let v:=(Real.sqrt 2*g)^((p+1:ℝ)-ε); let Y:=U.uses; let H:= Marker.beam U.factor Y (n:=n) hm; let u:= Orchard.beam0
                              let V₀ := Y.realBeat 0 N n (m+1); let Q := Y.realBeat 0 N n m; let z:= (a).clock.hatBeta (m+1); let w:= Mallow.station z; let B:= (a).budget m;let Y₀:=(t).op m n;let D:= Mallow.sandboxK H u; let b:= B.supportExponent; let v' := Mallow.straw (U.factor.shape.μ ((t).J (m+1)) ((t).J m)) (U.roll.L ((t).J (m+1))) G ((t).hatBeta m)
                              Q=H.result u ∧ Volant Y₀ D ((t).J (m+1)+1) (V₀.p.supportExponent-4) w (b+1/2) (b+1) 1 v' ∧ Mallow.Tariff (U.factor.target ((t).J (m+1)) ((t).J m)) (U.roll.L ((t).J (m+1))) ((t).J (m+1)+1) (U.factor.shape.μ ((t).J (m+1)) ((t).J m)) ((t).hatBeta m) ∧
                               ∀ (Z ι:Type)[DecidableEq Z][Fintype Z][Fintype ι](K:Marker.Census Z)(F:ι→Menu.Hat K V₀)(p':Z→Site (a|>.S.side (m+1) n))(r:Z→ℝ), (∀ i,0<r i) → Extra.Multi.Occupancy (Y₀.ratio.parent ∘ p') ((t).J (m+1)+1) →Menu.Offer p' F r (V₀.p.B) (V₀.p.supportExponent-4) w → StrongR2 H u p K F p' r v

variable (hC:C.Makes)
include hC
lemma enveloped (f:Extraction.Order)(S:Table C.book)(T:Facilities C f S): Library U:=by
   let L₀:=U.cellar; let S₀:= U.uses; have he:C= Cellar.yard (roseA S₀) L₀:= U.belongs
   have hx:= Capstone.bought U hC
   have hA:Mallow.RG12.Earned (orbitD G) U.factor.shape U.cost.delay:= fun _ _ hv _ ht=> U.couture _ _ hv _ ht|>.2.2.2.2.1
   obtain ⟨_,_,_,hW⟩:=T.costlier
   have hz(i:ℕ): (((a).budget i).supportExponent)=(100:ℝ):=by
      have hv:= hW.support i; rw [hx.kernel.kernel.through.chronicles] at hv; exact hv
   have ht:= Mallow.minted_same U.factor.shape hA; refine ⟨hx,hz,ht,?_⟩
   intro p r ε hf hu; obtain ⟨k,hk,hℓ⟩:= hx.epoch p r r r ε hf hu
   filter_upwards [hℓ,lasts U.factor U.uses U.cellar p r ε hf] with m hX hM
   refine ⟨hX.1,hX.2.1,hX.2.2.1,fun N n hm=>?_⟩
   intro g' v Y H u V₀ Q z w B Y₀ D b v'
   have h := hX.2.2.2 N n hm; have hS:= U.bandage.r; have hp: V₀.p=(a).budget (m+1):= (H.knows (u:ℝ) u.property).1.point
   have hv : Mallow.Tariff _ _ _ _ _:= ht.word _ _ (U.cost.B.valid.pays m) _ (step_paid _ m)
   let J := (t).J (m+1); let L:= U.roll.L J; have hL : z=Pressure.betaF G ((t).hatBeta m) L:= beta_eq U.cost.B.valid m
   have hsY : 100 ≤ (H.result u|>.p.supportExponent):=(hz m).ge
   have hsQ : 100 ≤ V₀.p.supportExponent:= by rw [hp,hz]
   have hu₀: Mallow.station (Pressure.betaF G ((t).hatBeta m) L)=w:=congr_arg Mallow.station hL.symm
   have hZ:= h.2.2.2.2.2.2.2.1 -- slots1
   have hx': Tail.requested (p+1) (CalendarStep.loss J) ≤ Tail.requested (p+1) ε:=by unfold Tail.requested; linarith only [show CalendarStep.loss J ≤ε from hM.2.1]
   refine ⟨h.1, (Many.ripe g hm H u hsQ hsY hS ht.hold (slots1 S₀ N m n (rose0 S₀) hm) (show 0 ≤ w from hu₀ ▸ hv.nonneg) (hu₀ ▸ hv.shipping)),hv,?_⟩ -- g.Current shadow
   have h' := CalendarStep.priceBoundActual (n:=n) U.factor U.uses L₀ p hm ε hu
   rw [show Pert.Asymptotics.regulatorRun _ _ _ _=g' from congr_arg (fun F=> Pert.Asymptotics.regulatorRun F N n (m+1)) he.symm] at h'
   intro ι Z _ _ _ K F o r i ht h
   exact Many.sailR2 g hm H u hsQ hsY hS hA p _ _ _ _ i ht h hM.1 v ((Real.rpow_le_rpow_of_exponent_le ((a).fits.delayed _|>.le) hx').trans h')

omit hC
lemma eventual_library (g:G.Simple) (κ:ℝ)(hκ:0<κ)(δ:Daisy.Charity.RG12.Decal G)(F:Extraction.Order) :
    ∃ (C:Family G)(f:Extraction.Order)(T':Table C.book)(W:Spec.Final C (F.refine f) T') (L:EveryPhase.Almanac W) (A:Couture C g (modes δ)),
    C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=κ ∧ UVExtension.Oasis.Floral (hG:=g) C ∧ (Extraction.Order.mk Extraction.Sequence.full (F.refine f).per).Ordered C T' ∧ EveryPhase.Completed W L ∧ OPE.Facilities C (F.refine f) T' ∧ Library A :=by
  obtain ⟨C,f,T',W,L,A,h₁,h₂,h₃,h₄,h₅,h₆,h₇,H⟩:= Capstone.delivering g κ hκ ((orbitD G).paired δ) F; exact ⟨C,f,T',W,L,A,h₁,h₂,h₃,h₄,h₅,h₆,h₇,enveloped A h₁ (F.refine f) T' h₇⟩
end YM.LocalTaylorR2.Orbit
