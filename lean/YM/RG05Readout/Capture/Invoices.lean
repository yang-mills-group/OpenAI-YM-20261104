import YM.RG05Readout.Capture.Pepper
import YM.RG05Readout.Capture.Plum
import YM.MergeProof.North.Bonus
/-!
# Shared schedule at the last punch/supply

Buy at post-block and export ripping estimates with pepper cash unchanged
per acquired trial. One schedule binding, not new launches after phase/horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {S: Family G}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open YM.MergeProof.Ribbons
open Mallow YM.RG05Readout
set_option quotPrecheck false
structure Cater (C:Family G) (D:Address.Rail C) :Prop where
    tiers : ∀ m N p:ℕ,∀ h:m<N,∃ a t:ℝ, RG05Readout.Many.Coursework C.path (RG05Readout.Many.apron C.path.levels) (D N p m h) (renal C.path.levels m) a t ∧ let z:= MergeProof.Ribbons.scurry C.path.levels (RG05Readout.Many.apron C.path.levels) (fun _=>t) (renal C.path.levels m) m; let X:=(C.path.levels.budget m).B; (((X+X+1:ℕ):ℝ)^4*z ≤ 1/2)∧ Real.exp z-1 ≤ 1
    throve : ∀ d m N p:ℕ,∀ h:m<N,d+3≤ C.path.levels.clock.J m→Address.Plated (C.labels.level d) C.path (C.localSection d) C.params m N p (D N p m h) (bling C.path.levels m)

variable (hG:G.Simple) {M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{K:ℕ→ℝ}{W:Bid.Worth}(b:Bandage X K W)(Y:Bolt A) (Q:ℕ→ℕ)
variable (t:ℕ→ℕ)(Z:∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p)(D:∀ N p m:ℕ,m<N→GaugeDoor ((Issue.trail Y).rep N p (m+1)) ((Issue.trail Y).rep N p m))
local notation "C"=> Family.mk (Issue.trail Y) (hol G) (Labels.frames G) (localSection G) t Z
local notation "H"=> Issue.trail Y
local notation "a"=> A.B.a
local notation "U"=> A.B.a.budget
local notation "J"=> A.B.a.clock.J
local notation "x"=> A.B.a.clock.hatBeta
local notation "r"=> RG05Readout.Many.apron A.B.a
local notation "p"=> fun i:ℕ=> (i+2)*(P.L i).val^4
variable (hN:Chateau b Q Y t Z D)(ht:∀ m:ℕ,100 ≤ (A.B.a.budget m).supportExponent)
open Lotus
section
variable {m j n:ℕ}
private lemma duetRG05 {E:Rep G (A.B.a.S.side m j)} {Z:Rep G (A.B.a.S.side (m+1) j)}(D:GaugeDoor Z E)(hk:(Issue.trail Y).rep n j m=E)(h:(Issue.trail Y).rep n j (m+1)=Z)(d:ℕ)(u:ℝ) (hp:∀ (o:Site (A.B.a.S.side (m+1) j)) (q:Set Wing)(M:Lotus.Leaf Z), (A.B.a.clock.op m j).ratio.parent o=0 → M.turn∈q → o∈ M.crest→ MergeProof.Along (localSection G d) (Issue.trail Y) n j m (hol G) o q (duet _ _ _ _ hk h D) (Complex.ofReal ∘ M.cicada) (MergeProof.prose M) (entry M) 0 0 (u*load M) (u*load M) (2*load M)) : Address.Plated ((Labels.frames G).level d) (Issue.trail Y) (localSection G d) (hol G) m n j (duet _ _ _ _ hk h D) u:=by subst E Z; exact ⟨hp⟩
end
include ht hN hG
lemma uv_RG05_cater (hP:Mallow.Minty X.shape (p) A.delay)(hv:Mallow.AccordV X.shape (p) A.delay) : Cater (C) D:=by
    let w m:= straw (X.shape.μ (J (m+1)) (J m)) (P.L (J (m+1))) G (x m)
    let u m:= station (x (m+1)); have h(i): x (i+1)=Pressure.betaF G (x i) (P.L (J (i+1))):= by rw [Extra.Iteration.block_beta,Extra.Iteration.block_eq A.B.valid]
    have hm(i j:ℕ)(hi:j ≤ J i) := hv _ _ (A.B.valid.pays i) _ (step_paid _ _) j hi
    have hμ:r= mutt A.B.a p:=funext fun i => by unfold mutt RG05Readout.Many.apron; rw [Extra.Iteration.block_eq A.B.valid]
    constructor
    · intro m N j he; change ∃ v t, RG05Readout.Many.Coursework _ r _ _ _ t∧ _
      obtain ⟨hF,hD⟩:= paneer hG b Y he (p) hN.nest (hN.motion N m j he) hP.hold (hP.word _ _ (A.B.valid.pays m) _ (step_paid _ _)) (ht _) (ht m)
      have hs : RG05Readout.Many.Coursework (H) r (D N j m he) (renal A.B.a m) (u m) (w m) := (by rw [hμ];exact ⟨hD,hF⟩); refine ⟨u m,w m,hs,?_⟩
      let I:= M.p.profile (J m); have hz: (U m).supportExponent= I.supportExponent:=congr_arg Stage.supportExponent (params_eq A.B.valid _)
      let f:=fun _ : ℕ=> w m; change (((U m).B+(U m).B+1:ℕ):ℝ)^4*scurry A.B.a (r) f (renal A.B.a m) m ≤1/2 ∧ Real.exp (scurry A.B.a (r) f (renal A.B.a m) m)-1 ≤1; unfold scurry renal; rw [hz,h m,hμ]; exact ⟨(hm m 0 (Nat.zero_le _)).1,(hm m 0 (Nat.zero_le _)).2.1⟩
    intro d m N j he hd; obtain ⟨l,v,Q',T,xv,hq,hZ,hO⟩:= hN.motion N m j he
    change Address.Plated ((Labels.frames G).level d) H (localSection G d) (hol G) m N j (D N j m he) (bling A.B.a m); rw [hO]; apply duetRG05 Y; intro o q M ho hp hu
    have H':= (Nat.le_add_right d 3).trans (show _ ≤ J m from hd); apply Graces.RG05_respects hG he hN.nest b.r T xv hq hZ b.clock b.stamp H' o ho M (bling A.B.a m) _ q hp hu
    unfold bling; rw [h m]; exact (hm m d H').2.2.2.2
end YM.PhysicalNext.Repeat.Legato
