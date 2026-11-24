import YM.IntegrationR2.Columns
import YM.RG17.Columns

/-!
# No choosing a second column family

Retains the actual Portal and its field-by-field Desk. In particular this gives
Strobe's `torches` budget on FullVolume/Feather (also the strictly stronger UV
`Jewel` construction) for every cutoff and every finite demand in the Cult.Rank
admission. The further gates of `Citizen` will be paid separately, at
construction time.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent Matric.R2
open Muse Matric
namespace Bandage.Boutique
open Mallow Lotus
variable (hG : G.Simple){M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K)
    {Y:Bolt A}{meshT:ℕ→∀ p,RG.Shoot.Trail A.B.a p}{N p m d:ℕ}
    (U: Boutique X meshT N p m)(choice: (A.B.bake.make meshT).Selected)(hd:d+3 ≤ A.B.a.clock.J m)
local notation "H!"=> A.B.bake.make meshT
set_option quotPrecheck false
include hG
lemma castReserve (hz:Nest X Y) : ReservePlate (localSection G d) H! N p m (hol G) ((H!).rep N p (m+1)) ((H!).S.block m) (U.castT b choice hd).plate (C (A.B.a.clock.J (m+1))) (Doors.rate ((H!).S.block m)) U.gate:=
    plateReserve U.hx b.songs b.PStage b.wait (Graces.feet hd b.clock) hz b.r U.stock center U.taught rfl hG b.tunes b.furthering b.corners b.shape b.clock b.stamp choice U.down U.up (okC b U choice hd) hd
end Bandage.Boutique
open Mallow Lotus
namespace Campaign
variable {R:Run G} {T:Campaign R} (W:Pillars R T) (h:G.Simple)
variable (d m N p:ℕ) (hm:R.t d ≤ m)(hn:m < N)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "H"=> R.family.path
local notation "F"=> (Labels.frames G).level d
local notation "D!"=> (W.yields N p).steps m (Nat.zero_le _) hn
local notation "Z!"=> (D!).castT R.b (W.yields N p).choice ((R.accepts d).trans (R.alloy.B.a.fits.mono hm))

/-- Name the actual tool and seat parameters; stated after the Run is chosen. -/
abbrev r2tool := (D!).castT R.b (W.yields N p).choice ((R.accepts d).trans (R.alloy.B.a.fits.mono hm))
include W hn in
lemma r2desk : Well ((H).rep N p (m+1)) (Boutique.attire R.T (m+1) p) (Real.sqrt ((H).levels.clock.forcedAllowance (m+1))):= (W.yields N p).notices (fun i=> Boutique.brochure R.T i p R.tuning.receipts) (show 0 ≤ m+1 from Nat.zero_le _) hn -- W may not included
include h
set_option maxHeartbeats 700000 in
lemma actualColumns :
    let U:Tool ((Labels.frames G).level d) (R.family.path) N p m:= r2tool W d m N p hm hn
    -- Tug and its BudgetPoint on the very same doors
    let z:= R.y (R.alloy.B.a.clock.J (m+1)); let y:= Doors.rate ((H).S.block m)
    ReservePlate (localSection G d) (H) N p m (hol G) ((H).rep N p (m+1)) ((H).S.block m) U.plate z y (R.doors N p m hn) ∧
    (∃ Y X, Tool.Cap U (localSection G d) (hol G) R.w (R.doors N p m hn) Y z y (waybill R.alloy.B.a m) X ∧ ∃ c, Push.Local.Leading Y.map.toLinearMap c) ∧
    Afford U.plate (hol G) ((H).rep N p (m+1)) ((H).rep N p m) ∧
    -- receipts attached to actual H of this Run
    Well ((H).rep N p (m+1)) (Boutique.attire R.T (m+1) p) (Real.sqrt ((H).levels.clock.forcedAllowance (m+1))) ∧
    ∃ Q:Gram F (hol G) (Boutique.attire R.T (m+1) p) ((H).levels.params (m+1)).columns,
      (∀ v, Q.point U (((C).factory d N p).entries (m+1) v|>.x)=((C).factory d N p).entries m v) :=by
   intro U z y; let f:= W.yields N p; let hz:=R.tuning.receipts
   let V := R.stories d N p
   have he : ∀ w:R.t d ≤ N, Branch.Piano R.b f (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) V w := fun hx=> W.ports d N p hx
   obtain ⟨S,hS⟩:= he (hm.trans hn.le)
   let hi:=R.accepts d |>.trans (R.alloy.B.a.fits.mono hm)
   let D := f.steps m (Nat.zero_le _) hn
   have hf:= Boutique.capTriangle h R.b D f.choice hi hz
   have hR:= Boutique.castReserve h R.b D f.choice hi hz
   have h' : R.doors N p m hn = D.gate := by rw [W.earnings]
   let Φ:= f.reading R.b (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) (m+1) (le_trans hm m.le_succ) hn hS
   rw [h']; refine ⟨hR,hf,(Boutique.tickets h _ D f.choice hi hz).swing,r2desk W m N p hn,Φ,fun v =>?_⟩
   have hx:= f.sungAt R.b (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _) (R.accepts d) (m+1) (hm.trans m.le_succ) hn hS
   change (Φ.point U ((V.entries (m+1) v).x))= V.entries m v
   rw [hS.2.1]
   change Φ.point U ((S.tone (m+1)).plays v).x=(S.tone m).plays v
   rw [hx.currents v]
   exact ((hS.2.2.2 m hm hn).2.2 hx v).symm

include W hm hn
lemma torchR2 : let P := ((C).factory d N p); ∀ v, Blown (P.entries m v) 0 ((C).path.rep N p m) (((H).levels.params m).columns * (F).coeffSize ((F).core (P.entries m v).x)) := by
  obtain ⟨he,⟨Y,X,hx,-⟩,-,hw,Q,hQ⟩:= actualColumns W h d m N p hm hn
  intro P v
  let x:= (P.entries (m+1) v).x; let U:=r2tool W d m N p hm hn
  have hh:= columnsBudget U hx hw he Q R.b.clock.room R.b.clock.bank x
  have ht : Q.point U x=P.entries m v:= hQ v
  rw [ht] at hh; exact hh
end Campaign
end YM.PhysicalNext.Repeat.Legato
