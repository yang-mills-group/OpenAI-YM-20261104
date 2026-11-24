import YM.GapsR2RG.StakePages
import YM.RG17.Witness
/-! # Bind stencil reserve on the same campaign. Does not assume or replace the slate transfer choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
open Matric
open Guard
-- anchor at Q reference state. annotations only; analytic transport via Fortune.
variable {Y}
namespace Boutique
variable {meshT:ℕ→∀ p,RG.Shoot.Trail A.B.a p}{N p m d:ℕ}
local notation "H!"=> A.B.bake.make meshT
local notation "μ"=> (0:ℝ)
variable (U: Boutique X meshT N p m)(choice: (A.B.bake.make meshT).Selected)(hd:d+3 ≤ A.B.a.clock.J m)
local notation "ris"=> (H!).rep N p (m+1)
local notation "R'"=> (H!).rep N p m
local notation "fa"=> (Labels.frames G).level d
local notation "J"=> A.B.a.clock.J (m+1)
local notation "t"=> A.B.a.clock.J m
open Motion
include hG Y
lemma capStencil (hz:Nest X Y): Reserves H! N p m (hol G) (U.castT b choice hd|>.plate) (C (A.B.a.clock.J (m+1))) (Doors.rate ((H!).S.block m)):=
  ledgerHereStencil U.hx b.songs b.PStage b.wait (Graces.feet hd b.clock) hz b.r U.stock center U.taught rfl hG b.tunes b.furthering b.corners b.shape b.clock b.stamp choice U.down U.up (okC b U choice hd) hd
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse
open Matric

lemma Campaign.storedStencil {R:Run G} {T:Campaign R} (W:Pillars R T) (h:G.Simple) :
    ∀ d N p m, R.family.ref d ≤ m → m < N → Bandage.Strengthened R.T (R.stories d N p) (R.t d) :=by
   intro d N p _ _ _ m hm hn v; let hd:= hm.trans hn.le
   let hz:=R.tuning.receipts
   let V := R.stories d N p
   let U := W.yields N p
   have he : ∀ w:R.t d ≤ N, Branch.Piano R.b U (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) V w := fun hx=> W.ports d N p hx
   obtain ⟨S,hS⟩:= he hd
   let hi:=R.accepts d |>.trans (R.alloy.B.a.fits.mono hm)
   let D := U.steps m (Nat.zero_le _) hn
   let P := D.castT R.b U.choice hi
   obtain ⟨Y,X,hX,hY⟩:= Boutique.capTriangle h R.b D U.choice hi hz
   -- The OP branch Heading needn't be the one defined by `.chamber.choose`.
   -- But casting the marks, including their forced partners, is unchanged,
   -- so we estimate another property of the actual output coordinates.
   have hp := Boutique.capStencil h R.b D U.choice hi hz
   let hw := U.notices (fun i=> Boutique.brochure R.T i p hz) ((Nat.zero_le m).trans m.le_succ) hn
   let hh:= hS.2.2.1.earned _ (hm.trans m.le_succ) hn
   let Q' := measure hh P.up hw; rw [show (R.stories d N p).entries=(S.draft _).inits from hS.2.1]
   have eq (v: R.family.label d) : (S.draft _).inits m v = Q'.point P ((S.tone (m+1)).index v):= (hS.2.2.2 m hm hn).2.2 hh v
   dsimp only; rw [eq]
   exact Gram.pointBlown P hX hp hw Q' R.b.clock.room R.b.clock.bank _

lemma Campaign.citizenTie {R:Run G} (hPack:OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors) {T:Campaign R} (W:Pillars R T) (h:G.Simple)
   (hv:∀i, (R.family.path.levels.budget i).supportExponent=100) (h' : OPE.Therm.Poetry R.family.path.levels)
   (hL:Filter.Tendsto R.Q Filter.atTop Filter.atTop) (hf:Subsidize R.family.path.levels): Citizen R.family R.w (mutt R.family.path.levels R.Q) R.doors :=by
   obtain ⟨hT,hq,hVel,hfr,-,-,-,-⟩:=R.bought _ R.tuning.receipts _ R.accepts R.stories R.doors R.makes R.carries R.books
   have hr:=Filter.Tendsto.comp hL (R.alloy.B.a.fits.deep.comp (tendsto_add_atTop_nat 1)); refine ⟨⟨hPack, (fun m N p d=> further h R.b _ R.T _ R.stories R.doors hT hf m N p d), hv, hr⟩,fun d N p m hm he=> Campaign.storedStencil W h d N p m hm he m hm he,h'⟩

end YM.PhysicalNext.Repeat.Legato

