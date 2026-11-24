import YM.LocalLTE.Vinca.Career
import YM.LocalLTE.Georges.Mile
import YM.LocalLTE.Georges.EscarpT
/-! Adaptation of YM/MergeProof/Marco; same budget on Career. -/
set_option autoImplicit false
noncomputable section
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
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) {Y:Bolt A}
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
-- interface terminalHistory selected. grants Tube. keep Grade d and potential.Cauchy.
variable (h:Dynamo X Y)
local notation "ℓ" => fun N p=> Keeper.sufficient (h.born N p) -- binder K Name
-- Book.T anchors
variable {Xf :∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p}{t:ℕ → ℕ}
open LocalLTE.Vinca
structure Harmonics (X:Factor A) (C:ℕ→ℝ) (Wt:Bid.Worth)(P:Bolt A)(l:ℕ) where
   tag : Bandage X C Wt
   elevated : Elevates A.B.a C Wt l
   port (N m n:ℕ)(_hm:m<N): Turf X N m n
   charged (N m n:ℕ)(hm:m<N) : (Issue.trail P).rep N n (m+1)= (port N m n hm).inPort
   baptism (N m n:ℕ)(hm:m<N) : (Issue.trail P).rep N n m=(port N m n hm).output
   samples (N m n:ℕ)(_hm:m≤N): HasSlots (P.history N n m).p (P.history N n m).activities
namespace Harmonics
variable {l N m n d:ℕ} (g:Harmonics X C K Y l)
include g
lemma mission : Dynamo X Y:=⟨fun _ _=> g.samples _ _ _ le_rfl,fun _ _ _ hm=> g.samples _ _ _ hm, fun N m n hm=> ⟨_,g.baptism N m n hm,g.charged N m n hm⟩⟩
local notation "P'"=> Issue.trail Y

variable (hm:m<N)
theorem ore : HasSlots ((g.port N m n hm).inPort|>.p) ((g.port N m n hm).inPort|>.activities):=by
   rw [← g.charged N m n hm]; exact g.samples _ _ _ hm
theorem oreo : HasSlots ((g.port N m n hm).output|>.p) ((g.port N m n hm).output|>.activities):=by
   rw [← g.baptism N m n hm]; exact g.samples _ _ _ hm.le
noncomputable def kube (N m n:ℕ)(hm:m≤N): Guard.Keeper ((Issue.trail Y).rep N n m).p ((Issue.trail Y).rep N n m).activities:= Guard.Keeper.sufficient (g.samples _ _ _ hm) -- type deduct.
noncomputable def space (N m n:ℕ)(hm:m<N): Guard.Keeper ((g.port N m n hm).output|>.p) ((g.port N m n hm).output|>.activities):=Guard.Keeper.sufficient (g.oreo hm)
noncomputable def deed (N n m:ℕ)(hm:m<N):= duet (Issue.trail Y) N n m (g.baptism N m n hm) (g.charged N m n hm) (g.port N m n hm).door
noncomputable def lays (d N n m:ℕ)(hm:m<N):=Bandage.purser g.tag Y l N m n (g.port N m n hm) (g.charged N m n hm) (g.ore hm) (g.space N m n hm) d
include hG
lemma purses (hd : d+3≤ A.B.a.clock.J m): Depot (localSection G d) (Issue.trail Y) N n (hol G) K m (g.deed N n m hm) (waybill A.B.a m) (g.lays d N n m hm) (g.kube N (m+1) n hm):= by
   exact Bandage.procurement hG g.tag Y l g.elevated N m n (g.port N m n hm) (g.baptism N m n hm) (g.charged N m n hm) (g.ore hm) (g.samples _ _ _ hm.le) (g.space N m n hm) (g.kube N (m+1) n hm) hm d hd
omit hG
lemma posts (N n m:ℕ)(hm:m<N): ClimbsT X Y N m n (g.deed N n m hm):= ⟨_,_,_, rfl⟩ -- potentially infer. Use literals.
end Harmonics
variable {l:ℕ}(g:Harmonics X C K Y l)
-- validator. FULL factory entries and physical calibration.
structure Stately (d N p :ℕ) (Xf:TransferData ((Labels.frames G).level d) (Issue.trail Y) N p) (t:ℕ):Prop where
   permits : ∃ Z:Extra.Histories.Music ((Labels.frames G).level d) H N p,Z.tone N=summit ((Labels.frames G).level d) (localSection G d) H N p (Keeper.sufficient ((Harmonics.mission g).born N p)) (Keeper.blank ((Harmonics.mission g).born N p)) d ∧ Xf.entries=(Z.draft H).inits∧ Sung (localSection G d) H N p (hol G) K t Z∧ ∀ m:ℕ,t ≤ m → ∀ hm:m<N,Carol (localSection G d) H N p m (g.deed N p m hm) (Z.tone (m+1)) (Z.tone m) (waybill A.B.a m)∧ Arranged H N p (hol G) m (Z.tone (m+1)) (Z.tone m) (g.lays d N p m hm) (g.kube N (m+1) p hm)∧ Chorus H N p m (Z.tone m)
lemma Stately.freight {d N p t:ℕ} {P':TransferData ((Labels.frames G).level d) (Issue.trail Y) N p} (hv:Stately g d N p P' t): FreightT Y g.mission N p d P' t K (g.deed N p):=by
    obtain ⟨Z,h,hz,hV,hm⟩:=hv.permits; exact ⟨Z,h,hz,hV,fun m p hm'=> ⟨(hm _ p hm').1,(hm _ p hm').2.2⟩⟩
include hG
lemma stipples (t:ℕ→ℕ)(hp:∀ d,d+3≤ (Issue.trail Y).levels.clock.J (t d)) : ∃ (Xf : ∀ d N p,TransferData ((Labels.frames G).level d) (Issue.trail Y) N p),
   let F:= Family.mk H (hol G) (Labels.frames G) (localSection G) t Xf
   F.Makes ∧ Spec.Calibrated F ∧∀ d N p:ℕ,t d≤N→Stately g d N p (Xf d N p) (t d):=by
   let b:= g.tag; let h:= g.mission
   let U(d):= (Labels.frames G).level d
   have he(d m) (hq : t d ≤ m):d+3 ≤ A.B.a.clock.J m:= (hp d).trans (A.B.a.fits.mono hq)
   let B(d):= localSection G d
   have hg(d N p): ∃ T: TransferData (U d) H N p, t d≤N → T.Based (hol G) (B d) (t d) ∧ Stately g d N p T (t d):=by
      by_cases hx:t d≤N
      swap; · exact ⟨⟨fun _ v => Extra.Histories.primary 0 v,LinearEquiv.refl _ _⟩,fun he => False.elim (hx he)⟩
      let F:= U d; let V:= Guard.summit F (B d) H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) d; let W:= K; let S:= (B d)
      have he' := (Nat.le_add_right d 3).trans (he _ _ hx)
      have ho : OnTop S H N p (hol G) V := summon F S H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) Y.choice d (sound ..) (Doors.cameras_ge G d) (fun i=> Doors.cameras_holds G d _ i 0) ((b.clock.sequences N d he').receipts p 0)
      obtain ⟨Z,hZ,hS,hQ⟩:= LocalLTE.Vinca.sing S H N p (hol G) W Y.choice (sound G d) b.clock.room b.clock.bank (t d) hx V ho (voice S H N p (Keeper.sufficient (h.born N p)) (Keeper.blank (h.born N p)) d Y.choice (sound G d) ho) (g.lays d N p) (fun i hm=> g.kube N (i+1) p hm) (fun m hm hm'=> g.purses hG hm' (he _ _ hm))
      obtain ⟨T,hT,H'⟩:= Work.G08.answer W H b.clock.room b.clock.bank N p d (t d) _ (Z.draft H) (localSection G d) _ (Sung.clocks S H N p (hol G) K _ _ hS)
      exact ⟨T,fun _=> ⟨H',⟨Z,hZ,hT,hS,hQ⟩⟩⟩ -- nested
   choose T hT using hg; have ha := Issue.refer H K C t b.clock hp
   refine ⟨T,⟨Y.choice,ha.gets,ha.order,ha.fits,?_,fun d N p hi=>(hT d N p hi).1⟩,⟨M.p,P,A.θ,A.delay,A.bar,A.asks,M.O,M.K,A.post,A.B,Y.history,Y.sticks,rfl,Y.moves⟩,fun d N p hi=>(hT d N p hi).2⟩
   exact fun d N p hi o v=> ha.loaded d N hi _ rfl rfl _ o v
end YM.PhysicalNext.Repeat.Legato.Bandage
