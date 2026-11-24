import YM.LocalLTE.Vinca.Key
import YM.LocalLTE.Vinca.Buy
import YM.LocalLTE.Georges.MarcoT
import YM.LocalLTE.Vinca.Song
/-! Gateway procurement. Entire trajectory, not just α scopes. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
-- choose structs Peers earlier. Motion alignment.
variable (l:ℕ)(hE:Elevates A.B.a C K l)
variable (N m n:ℕ) (S:Turf X N m n)
variable (hO:(Issue.trail Y).rep N n m=S.output) (hI:(Issue.trail Y).rep N n (m+1)=S.inPort)
    (hP:HasSlots (S.inPort|>.p) (S.inPort|>.activities))(hA:HasSlots ((Issue.trail Y).rep N n m).p ((Issue.trail Y).rep N n m).activities)
-- extension aspect h_rank. use standby otherwise.T.Value.
open YM.LocalLTE.Vinca
local notation "u" => A.B.a.clock.J m
local notation "j"=> A.B.a.clock.J (m+1)
local notation "X'"=> (Issue.trail Y).rep N n (m+1)
local notation "X₀"=> (Issue.trail Y).rep N n m
local notation "Ko"=> Guard.Keeper.sufficient («R»:=S.output) -- no name? unused
variable (P₀:Guard.Keeper (S.output|>.p) (S.output|>.activities))(P':Guard.Keeper ((Issue.trail Y).rep N n (m+1)).p ((Issue.trail Y).rep N n (m+1)).activities)
local notation "D"=> duet H N n m hO hI S.door
local notation "v" => 2*(Real.exp (X').p.supportExponent* Cub.title G (M.p.profile j))
variable (hm:m<N)(d:ℕ)
-- Ω.E.Global.System.
include b
lemma aperture (hd:d+3 ≤ A.B.a.clock.J m) : Push.Local.Readable (hol G) (localSection G d) (S.inPort|>.p) (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1)))):=by
     rw [(S.senses).1.point]; rw [show title G (M.p.profile j) = authors A.B.a (m+1) from ?_]; exact lively b.clock (((Nat.le_add_right d 3).trans hd).trans (step_paid A.B.a m).1)
     unfold title authors; rw [params_eq A.B.valid (m+1)]
-- actual deterministic policy. avoids dependence on forecasting.Price for r0 etc later
noncomputable def purser : Gateway ((Labels.frames G).level d) (hol G) ((Issue.trail Y).rep N n (m+1)) ((Issue.trail Y).S.side m n):=if h:d+3≤ A.B.a.clock.J m then
       YM.LocalLTE.Vinca.sway H N n m (hol G) S.inPort hI (Cub.lightPlant S (Bandage.aperture b N m n S d h) hP l P₀) else {
           core:= fun _=>Extra.Histories.primary 0 0
           reader:= fun _ _ _ _ _=>Extra.Histories.primary 0 0
           flag:= fun _ _ _ _ _ =>Extra.Histories.primary 0 0 }
-- motion
include hE hG hm hA
lemma procurement (hd:d+3≤ A.B.a.clock.J m): YM.LocalLTE.Vinca.Depot (localSection G d) H N n (hol G) K m D (waybill A.B.a m) (purser b Y l N m n S hI hP P₀ d) P':=by
    have hω:v= waybill A.B.a m:=by unfold waybill; rw [params_eq A.B.valid]; have he:(X').p=A.B.a.budget (m+1):= Y.choice.represents N n (m+1) hm|>.vac; rw [he]
    rw [← hω]; refine ⟨?_, sound_duet H N n m hO hI S.door _ (S.opensV hG hm b.r),mul_nonneg zero_le_two (mul_nonneg (Real.exp_nonneg _) (zero_le_one.trans (Cub.title_one ..))), (glyphBound A.B.a (m+1)).2⟩
    let n':= (H).S.side (m+1) n; let x₀ := (0:Site n'); let a (i:{i:Support n'//x₀∈i}):Wing := .logKey (Blush.found x₀ i.val i.property)
    let e (i:StockTag n'): Wing:= .gasKey (cart P' i)
    let V:= Set.range a∪ Set.range e
    obtain ⟨T0,hc⟩:= Cub.chordsP hm b.songs b.PStage b.wait (Graces.feet hd b.clock) hA b.r S hO hI hG b.tunes b.furthering b.corners b.shape b.clock b.stamp (aperture b N m n S d hd) hP l P₀ hd V (fun i hi=> Or.inl ⟨⟨i,hi⟩,rfl⟩) -- syntax.
    let s:=Bandage.purser b Y l N m n S hI hP P₀ d
    have hv:= hE.tilt H m rfl d ((Nat.le_add_right d 3).trans hd)
    dsimp only at hv; rw [params_eq A.B.valid,Push.PriceCompiler.block_eq A.B.valid] at hv
    rw [purser,dif_pos hd]; exact ⟨V,T0,_,_,(Set.finite_range a).union (Set.finite_range e), fun i=> Or.inr ⟨i,rfl⟩,hc,hv⟩
end YM.PhysicalNext.Repeat.Legato.Bandage
