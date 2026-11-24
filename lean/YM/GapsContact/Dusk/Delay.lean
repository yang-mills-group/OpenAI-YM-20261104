import YM.GapsContact.Dusk.Buy
import YM.MergeProof.Almandine
/-!
# Budget apparatus post-L purchase and retention
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe MergeProof  MergeProof.Menu Extra.Multi Merge
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {X : Targets s K} {D : Rolls s} {Θ : Protection D} {p : Expenses X} {u : Return.Wages} {l : ℕ→ℝ} {P : Teller G}
open GapsContact.Dusk
variable (R:Register D p u l) (Q:ℕ→ℕ)

def ConsumesD (Z:Delays Θ): Prop:= ∀ j x,Z.betaEntry j≤x→∀ i,StepStages j i → let μ:=R.μ j i; let L:=D.L j; let Y:=X j i; let v:= (p j i).earn
    (Bikes Y L μ x v ((Y.exp-v)/3) 0 0 0 ∧ 2*(pledgeA L Y μ x 0 0 0*(1-sailUp Y L x)⁻¹) ≤ precious x) ∧ Palette.shipPrice L Y x (Q j) (ipo (betaF G x L)) ∧ Ticks x (betaF G x L) (straw μ L G x) (Q j)
lemma boutique (U:Delays Θ) (hg:G.Simple)(he:∀ j i,(X j i).rate=rBase): ∃ V:Delays Θ, DelayLe U V ∧ ∀ W:Delays Θ, DelayLe V W→ ConsumesD R Q W:=by
   let P(j i x):= let μ:=R.μ j i; let L:=D.L j; let Y:=X j i; let v:= (p j i).earn
                  (Bikes Y L μ x v ((Y.exp-v)/3) 0 0 0 ∧ 2*(pledgeA L Y μ x 0 0 0*(1-sailUp Y L x)⁻¹) ≤ precious x) ∧ Palette.shipPrice L Y x (Q j) (ipo (betaF G x L)) ∧ Ticks x (betaF G x L) (straw μ L G x) (Q j)
   have hP j i (h:StepStages j i) : ∀ᶠ x in atTop,P j i x:=by
      have hm:0 < R.μ j i:= (R.consumes j i h).2.1
      exact (sails_near (X j i) (D.L j) (p j i) hg hm (he j i)).and ((ipo_ship _ _ _ hg (he j i)).and (shore_finance _ _ hg hm))
   obtain ⟨x,-,hx,H⟩:= collect_upper U.betaEntry _ fun j=> eventually_transitions j _ _ (fun i hi=> hP j i hi)
   exact ⟨{U with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun W hy j x hx i h=> H j x ((hy.beta j).trans hx) i h⟩
end YM.PhysicalNext.Repeat.Mallow

namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus GapsContact.Dusk MergeProof Accent Menu
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG:G.Simple)
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
set_option quotPrecheck false
local notation "H"=> Issue.trail Y
local notation "L"=> A.B.a

private lemma retrace {n j m:ℕ}{R:RG.Rep G (A.B.a.S.side m j)}{E:RG.Rep G (A.B.a.S.side (m+1) j)}{D:GaugeDoor E R}{a c d k t u:ℝ}{K:ℕ}
    (he:(Issue.trail Y).rep n j (m+1)=E) (h:(Issue.trail Y).rep n j m=R) (hp: Volant ((L).clock.op m j) D K a c d k t u): Volant ((L).clock.op m j) (duet (Issue.trail Y) n j m h he D) K a c d k t u:= by subst E R; exact hp
include b hG
lemma traffic (Q:ℕ→ℕ)(h : Nest X Y)(hq:Mallow.Minty X.shape Q A.delay)(hC:ConsumesD X.shape Q A.delay)
    (hE:∀ i:ℕ,100 ≤ (A.B.a.budget i).supportExponent)
    (D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail Y).rep N p (m+1)) ((Issue.trail Y).rep N p m)) (hd:∀ N p m(hm:m<N), Climbs X Y N m p (D N p m hm)) : Shipper H (mutt L Q) D:=by
  refine ⟨hE,fun n j m hm=>?_⟩
  let J:= (L).clock.J (m+1); let Jp:= (L).clock.J m; let y:=(L).clock.hatBeta m
  have hp:=hC J y (A.B.valid.pays m) Jp (step_paid _ m)
  have hv: (L).clock.hatBeta (m+1)=Pressure.betaF G y (P.L J):= (Extra.Iteration.block_beta m).trans (congr_arg (Pressure.betaF _ _) (Extra.Iteration.block_eq A.B.valid m))
  obtain ⟨l,v,Q',U,x,he,hx,hT⟩:= hd n j m hm
  have hK:(Q' x.val).p= (L).budget (m+1):= (U.knows _ x.property).1.point
  have hE': (U.result x|>.p)= (L).budget m:=rfl
  dsimp only; change ∃ a:ℝ, Volant ((L).clock.op m j) (D n j m hm) (Q J) ((L|>.budget (m+1)).supportExponent-4) (ipo ((L).clock.hatBeta (m+1))) ((L|>.budget m).supportExponent+1/2) ((L|>.budget m).supportExponent+1) (precious y) a ∧ Ticks y ((L).clock.hatBeta (m+1)) a (Q J) -- `_` m fix
  rw [hv,hT]
  have ht :0 ≤ ipo (Pressure.betaF G y (P.L J)):=by rw [←hv]; exact (ipo_pos ((L).fits.delayed _)).le
  have ha:= Many.dawn hG hm U x (hK.symm ▸ hE (m+1)) (hE'.symm ▸ hE m) b.r hq.hold (hx ▸ h.samples hG n (m+1) j hm) ht hp.2.1 hp.1.1 hp.1.2
  rw [hK] at ha; exact ⟨_, retrace Y hx he ha,hp.2.2⟩
end YM.PhysicalNext.Repeat.Legato.Bandage
