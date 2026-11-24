import YM.LocalLTE.Sail.Spinning
import YM.LocalLTE.Ticket.Tent
import YM.LocalLTE.Ticket.Tissue
import YM.LocalLTE.Ticket.Stalk
import YM.LocalLTE.Ballot.Boat
import YM.LocalLTE.Ticket.Oracle
import YM.LocalLTE.Ticket.Parade
import YM.LocalLTE.Ticket.Pump
import YM.LocalLTE.Ballot.Pane
/-! Reworking `Ticket/Prom` for schedules with explicit, controlled guide functions.

 Dues bought and ports ON ACTUAL Stage. Epoch grade supplied in companion schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Bandage Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
section
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
local notation "H"=> Issue.trail P
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ} (U:Harmonics R C W P l)
-- window opportunities using after-L supports. 
variable {N n m:ℕ} (hm:m<N)
local notation "T"=> U.port N m n hm
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.hatBeta m
set_option quotPrecheck false
open Pressure ConnectedActivityE6 Push.AbsoluteSums
variable (hG:G.Simple)
-- recall after.App durations
open Spiral
variable {M p0 r q TT :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hp:East.stagnate q 500<l)(hR:∀ i j,(R.target i j).halo=500)
-- Stately archive.One physical offered history.E for any reference.
variable (d:ℕ)
set_option quotPrecheck false
local notation "F0"=> ((Labels.frames G).level d)
local notation "V'"=> A.B.a.S.side m n
local notation "B'"=> (localSection G d)
local notation "s"=> U.kube N (m+1) n hm
variable (P₀:Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
local notation "o1"=> P₀.tone (m+1)
local notation "o0"=> P₀.tone m
variable (hΓ: A.B.a.params m=A.B.a.params m)
local notation "u"=> N - (m+1)
local notation "c" i=> (Issue.trail P).rep N n i
local notation "κ1" i=> (Real.sqrt (A.B.a.clock.forcedAllowance i))
local notation "x1" i=> (A.B.a.clock.hatBeta i)
local notation "t"=> Spiral.grantZ p0 TT (N-(m+1))
local notation "Qi"=> AX.demand J I u
local notation "U0"=> (D.L J).val* Pressure.radiusB Y
local notation "pT"=> AX.outfit J I u
local notation "Xκ"=> (x1 (m+1))^t
-- exhibition validity across scheduled canonical legs. ANY accepted basis at each aperture.No Lens deferred.We expose Sequence of estimators.Requests fixed independently per m. Inlets bought prior to rescale.Runtime.
set_option quotPrecheck false
variable (Z:∀ i:ℕ, ((Labels.frames G).level d).Coeff → Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side i n))
variable (X0:∀ i:ℕ,FrameBox.Grove (0:Site (A.B.a.S.side i n)))
local notation "π"=> torso hr.provision hp hR m n
-- continuity tick.Marks
include hr hp hR d U X0 P₀
noncomputable def EncoreC (m:ℕ) (hm:m<N)(Z0: ((Labels.frames G).level d).Coeff → Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side (m+1) n))
    (Z1: ((Labels.frames G).level d).Coeff → Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side m n)) : Prop:=∃ (hd:d+3≤ A.B.a.clock.J m)(V:Employ (Issue.trail P) N n (hol G) m (P₀.tone (m+1)) (U.kube N (m+1) n hm)), let e0:= U.lays d N n m hm;
       (P₀.tone m).plays = Vinca.marksP (Issue.trail P) N n (hol G) m (P₀.tone (m+1)) (U.kube N (m+1) n hm) e0 V ∧
          ∃ Y₀: ∀ i,Ticket.Inlet («H»:=H) (N:=N) (m:=m) (p:=n) (localSection G d) (hol G) κ (AX.demand (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (N-(m+1))) ((D.L (A.B.a.clock.J (m+1))).val* Pressure.radiusB (A.B.a.clock.hatBeta m)) (Z0 ((P₀.tone (m+1)).index.symm (Size.axis F0 i))) (A.B.a.clock.hatBeta (m+1)),
          Z1= Ticket.galleryC B' (hol G) (U.lays d N n m hm) (U.lantern hm d hd q (AX.atlas (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (N-(m+1))) (AX.outfit (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (N-(m+1))) (torso hr.provision hp hR m n) (X0 m)) (P₀.tone (m+1)) (U.kube N (m+1) n hm) V Y₀ -- X0 not variable hr hp in type.Port h for def fails use include.
local notation "B0"=> (fun v:(F0).Coeff=> Extra.Histories.primary (0:Site (A.B.a.S.side N n)) v)
variable (ρ:ℕ) (he:ρ≤ m)(hq:ρ ≤ N)(hd:d+3≤ A.B.a.clock.J ρ)
-- Need kit.E.Arbitrary range.
open Planned.GuardedAtom Guard
local notation "SC"=> (Keeper.sufficient ((Harmonics.mission U).born N n))
local notation "SB"=> (Keeper.blank ((Harmonics.mission U).born N n))
include hr hd
omit hp hR X0
lemma committedC (hN:P₀.tone N=summit F0 B' H N n SC SB d) (ht:Sung (localSection G d) (Issue.trail P) N n (hol G) W ρ P₀) : Harmonics.ShellDate (AX:=AX) (l:=l) (p0:=p0) (TT:=TT) (κ:=κ) d P₀ N (B0):=by
   constructor; swap; · intro h; omega
   have hx:= ht.head.heard; rw [hN] at hx; rw [Nat.sub_self,hN]; let CT:= A.B.a.clock
   let Rf:=A.B.a
   have he: d≤ CT.J N:=(Nat.le_add_right d 3).trans (hd.trans (A.B.a.fits.mono ht.ahead))
   obtain ⟨hs₁,he',hA,hR,Hv⟩:=hr.provision.limits _ _ (step_paid A.B.a N) _ (A.B.valid.pays N)|>.2 d he
   have hz : 1 ≤ CT.hatBeta N:= Hv.warm; let g0:= Spiral.grantZ p0 TT 0; let x:= CT.hatBeta N; let Q:=x^g0
   have hp': Extra.Histories.fee F0 (Rf.budget N) ((localSection G d).footprint (0:Site (Rf.S.side N n))) (Doors.cameras G d) (Rf.clock.forcedAllowance N) ≤ Real.sqrt (Rf.clock.forcedAllowance N)*Q:= Hv.receipt Rf N n rfl (by rw [show Rf.params N = _ from params_eq A.B.valid N])
   intro v T' -- rank.ori
   let v':= Ticket.premiere B' (hol G) (SC) (SB) d P.choice (sound G d) (Doors.cameras_ge G d) (fun i=> Doors.cameras_holds G d _ i 0) hp' (Real.rpow_nonneg (zero_le_one.trans hz) g0) hx («u»:=l*(A.B.a.budget N).B) (d0:=rankLC A AX N N) (μ:=κ) v
   exact v'.pledge (mul_le_mul_of_nonneg_right hz (Work.G08.size_nonneg ..)) le_rfl
-- orbit semantics.Mark.
-- Port.At any range exactly.T requests
structure GalaC (m:ℕ):Prop where
    deeds : ∀ i,m≤ i→ i≤N→ ShellDate (AX:=AX) (l:=l) (p0:=p0) (TT:=TT) (κ:=κ) d P₀ i (Z i)
    pre : Z N=fun v:((Labels.frames G).level d).Coeff=> Extra.Histories.primary (0:Site (A.B.a.S.side N n)) v
    stance i: m≤ i→∀ hi:i<N, EncoreC U hr hp hR d P₀ X0 i hi (Z (i+1)) (Z i)
include hκ hG hp hR U X0
lemma fundsC (h:N-m≤TT+1)(he:m≤N)(hx:ρ ≤ m) (hN:P₀.tone N=summit F0 B' H N n SC SB d) (ht:Sung (localSection G d) (Issue.trail P) N n (hol G) W ρ P₀) (hy:∀ i,ρ ≤ i→∀ h:i<N,Vinca.Arranged H N n (hol G) i (P₀.tone (i+1)) (P₀.tone i) (U.lays d N n i h) (U.kube N (i+1) n h)):∃ Z,GalaC U hr hp hR d P₀ Z X0 m:=by
   let r:= ht.ahead
   induction he using Nat.decreasingInduction with
   | self=>
      let Z : ∀ i,(F0).Coeff → Coefficient (F0) ((Issue.trail P).S.side i n) := fun i v=> Extra.Histories.primary (0:Site (A.B.a.S.side i n)) v
      refine ⟨Z,⟨fun i hi hv=> ?_,rfl,fun i hi hu=>by omega⟩⟩; have he:i=N:=le_antisymm hv hi; rw [he]; exact U.committedC hr d P₀ ρ hd hN ht
   | of_succ i hi ih=>
      obtain ⟨Z',hZ⟩:= ih (by omega) (by omega); have hd':d+3≤ A.B.a.clock.J i:= hd.trans (A.B.a.fits.mono hx)
      have hf:= hZ.deeds (i+1) le_rfl hi
      let s0:= U.kube N (i+1) n hi
      let g₁:=P₀.tone (i+1); obtain ⟨ℓ,hℓ⟩:= hy i hx hi
      have hψ:= invitationC (A:=A) hi hr d P₀ hf; let Y₀:= hψ.some
      have hs:= U.extendsHC hi hG hr hκ hp hR d P₀ hf hd' (X0 i) (by omega) (ht.earned _ (by omega) hi) (ht.earned _ hx hi.le) (ht.step _ hx hi) ℓ hℓ Y₀ -- Type by elaboration maybe fails
      let I':=A.B.a.clock.J i; let J':=A.B.a.clock.J (i+1); let v:=N-(i+1)
      let Zt:= U.lantern hi d hd' q (AX.atlas J' I' v) (AX.outfit J' I' v) (torso hr.provision hp hR i n) (X0 i)
      let Z0:=Ticket.galleryC B' (hol G) (U.lays d N n i hi) Zt (P₀.tone (i+1)) (U.kube N (i+1) n hi) ℓ Y₀
      let Xy:= Function.update Z' i Z0; have hk:Xy i= Z0:= Function.update_self ..; have he(j)(h:i<j):Xy j=Z' j:=Function.update_of_ne (Ne.symm h.ne) ..
      refine ⟨Xy, fun j hj hy=> ?_,(he _ hi).trans hZ.pre,fun j hj ht'=>?_⟩
      · obtain h|h:= lt_or_eq_of_le hj; rw [he _ h]; exact hZ.deeds j h hy
        subst j; rw [hk]; exact hs
      obtain h|h:=lt_or_eq_of_le hj; rw [he _ h,he _ (by omega)];exact hZ.stance j h ht'
      subst j; rw [he _ (by omega),hk]; exact ⟨hd',ℓ,hℓ,Y₀,rfl⟩
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
