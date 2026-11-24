import YM.Frontier6.Trajectory.Duets
import YM.MergeProof.Marco
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Lattice Wilson Source RG Extra.Histories
variable {G:Gauge} {d:ℕ}
def StepsLeading {N p:ℕ} {F:Labels.Frame G d} (W:Bid.Worth) (D:SectionData F) (H:History G) (A:Hol G) (h:ℕ) (T:TransferData F H N p):Prop :=
   ∃ Z: Music F H N p, T.entries=(Z.draft H).inits∧ Sung D H N p A W h Z ∧
    ∀ m:ℕ, h ≤ m→ m<N → ∃ T:Heading F, (∃ cap:ℝ, Push.Local.Leading T.map.toLinearMap cap) ∧
       CoeffStep H p W m (Z.tone (m+1)) (Z.tone m) T
def ColumnSteps (C:Family G)(W:Bid.Worth):Prop:= ∀ d N p:ℕ, C.ref d≤N→ StepsLeading W (C.localSection d) C.path C.params (C.ref d) (C.factory d N p)
end YM.MergeProof

namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Guard Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
-- interface terminalHistory selected. grants Tube. keep Grade d and potential.Cauchy.
variable (h:Nest X Y)
local notation "ℓ" => fun N p=> Keeper.sufficient (h.born N p) -- binder K Name
-- Book.T anchors
variable {Xf :∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p}{t:ℕ → ℕ}
include b hG h
lemma squadLeading (t:ℕ→ℕ) (hp:∀ d,d+3≤ (Issue.trail Y).levels.clock.J (t d)): ∃ (D:∀ N p m,m<N→GaugeDoor ((H).rep N p (m+1)) ((H).rep N p m)) (Xf : ∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p),
   let F:= Family.mk H (hol G) (Labels.frames G) (localSection G) t Xf
   F.Makes ∧ Spec.Calibrated F ∧ (∀ N m p (hm:m<N), Climbs X Y N m p (D N p m hm)) ∧ ColumnSteps F K ∧∀ d N p : ℕ, t d ≤ N→ Freight Y h N p d (Xf d N p) (t d) K (D N p):=by
   choose D hA hD using chorusLeading hG b Y h
   -- D N p m
   let U(d):= (Labels.frames G).level d
   have he(d m) (hq : t d ≤ m):d+3 ≤ A.B.a.clock.J m:= (hp d).trans (A.B.a.fits.mono hq)
   let B(d):= localSection G d
   have hg(d N p): ∃ T: TransferData (U d) H N p, t d≤N → T.Based (hol G) (B d) (t d) ∧ StepsLeading K (B d) H (hol G) (t d) T ∧ Freight Y h N p d T (t d) K (D N p):=by
      by_cases hx:t d≤N
      swap; · exact ⟨⟨fun _ v => Extra.Histories.primary 0 v,LinearEquiv.refl _ _⟩,fun he => False.elim (hx he)⟩
      let F:= U d; let V:= Guard.summit F (B d) H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) d; let W:= K; let S:= (B d)
      have he' := (Nat.le_add_right d 3).trans (he _ _ hx)
      have ho : OnTop S H N p (hol G) V := summon F S H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) Y.choice d (sound ..) (Doors.cameras_ge G d) (fun i=> Doors.cameras_holds G d _ i 0) ((b.clock.sequences N d he').receipts p 0)
      obtain ⟨Z,hZ,hS,hQ⟩:= MergeProof.composeLeading S H N p (hol G) W Y.choice (sound G d) b.clock.room b.clock.bank (t d) hx V ho (voice S H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) d Y.choice (sound G d) ho) (fun m hm hm'=> hD N p m hm' d (he _ _ hm))
      obtain ⟨T,hT,H'⟩:= Work.G08.answer W H b.clock.room b.clock.bank N p d (t d) _ (Z.draft H) (localSection G d) _ (Sung.clocks S H N p (hol G) K _ _ hS)
      exact ⟨T,fun _=> ⟨H',⟨Z,hT,hS,fun m a b=>(hQ m a b).1⟩,Z,hZ,hT,hS,fun m a b=>(hQ m a b).2⟩⟩
   choose T hT using hg; have ha := Issue.refer H K C t b.clock hp
   refine ⟨D,T,⟨Y.choice,ha.gets,ha.order,ha.fits,?_,fun d N p hi=>(hT d N p hi).1⟩,⟨M.p,P,A.θ,A.delay,A.bar,A.asks,M.O,M.K,A.post,A.B,Y.history,Y.sticks,rfl,Y.moves⟩,fun N m p hm=>hA N p m hm,fun d N p hi=>(hT d N p hi).2.1,fun d N p hi=>(hT d N p hi).2.2⟩
   exact fun d N p hi o v=> ha.loaded d N hi _ rfl rfl _ o v
end YM.PhysicalNext.Repeat.Legato.Bandage
