import YM.LocalLTE.Quay.Harp
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
open Spool
-- center.Burn at origin no rotations for new capsules. ℓ availability
open Mallow ConnectedActivityE6 Push.AbsoluteSums Push Local Planned.GuardedAtom.Guard Blush
open Pressure VoucherB LocalLTE.Vault LocalLTE.Concourse
set_option quotPrecheck false
variable (hd:3≤ A.B.a.clock.J m)(hG:G.Simple)
local notation "Ut"=> U.tag
local notation "Xg"=> (X.p.profile I)
local notation "W₀"=> (U.lays 0 N n m hm)
local notation "Z"=> U.kube N (m+1) n hm
local notation "t₀"=> (U.port N m n hm)
local notation "Ωu"=> (Issue.trail P).rep N n (m+1)
local notation "Ω"=> (Issue.trail P).rep N n m
local notation "R₁"=> (t₀).output
local notation "Z₁"=> (t₀).inPort
local notation "D₀"=> (localSection G 0)
-- potential solid carriers.
variable {M p0 r q TT c d ι₀ p :ℕ}{κ ζ ε:ℝ}{Hx:Heights}{K:ℕ}(hr: Spool.Terms R.shape κ p0 r l q M K ε A.delay Hx)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hp:East.stagnate q 500<l)(hR:∀ i j,(R.target i j).halo=500)
variable (hX:1 ≤ q)(hT:Package R.shape κ p r l K d c ι₀ ε A.delay)
-- certificate for use at all τ.Vehicle pitch. invoice
local notation "B0"=> (localSection G 0)
local notation "F0"=> ((Labels.frames G).level 0)
structure Staff (R:Coefficient ((Labels.frames G).level 0) ((Issue.trail P).S.side m n)) (E:ℕ→ Coefficient ((Labels.frames G).level 0) ((Issue.trail P).S.side m n))(x:(F0).Coeff)(f:ℕ→ℕ)(l K c p:ℕ)(κ:ℝ):Prop where
    format : R.Format 0 (hol G) ((Issue.trail P).rep N n m)
    credit : R.remBound 0 ((Issue.trail P).rep N n m) (Real.sqrt (A.B.a.clock.forcedAllowance m)) (limitT m N c A.B.a)
    receipt : ((Labels.frames G).level 0).coeffSize (R.x-x) ≤ oath p (A.B.a.clock.hatBeta m)
    holdings : LocalLTE.Concourse.Center (localSection G 0) (hol G) ((Issue.trail P).rep N n m) R E f K (l*(A.B.a.budget m).B) κ (Real.sqrt (A.B.a.clock.forcedAllowance m)) (fun _=> A.B.a.clock.hatBeta m) (weightC (A.B.a.clock.hatBeta m)) (weightC (A.B.a.clock.hatBeta m))
variable (R' : Coefficient ((Labels.frames G).level 0) ((Issue.trail P).S.side (m+1) n)) (E:ℕ→ Coefficient ((Labels.frames G).level 0) ((Issue.trail P).S.side (m+1) n))
    (Yp: ((Labels.frames G).level 0).Coeff)
    (Ψ:FrameBox.Grove (0:Site (A.B.a.S.side m n)))
open LocalLTE.Drift
structure Fellows where
   y : Syllabus (Issue.trail P) N n m (hol G) (rack (U.kube N (m+1) n hm) (memo ((Labels.frames G).level 0).e0 R')) (limitT (m+1) N c A.B.a)
   p : Paper («H»:=Issue.trail P) (m:=m) (N:=N) (p:=n) (localSection G 0) (hol G) E K (Hx.angle 0) ((D.L (A.B.a.clock.J (m+1))).val*Pressure.radiusB (A.B.a.clock.hatBeta m)) (U.port N m n hm|>.ranch.allocation.κ) (fun _=> A.B.a.clock.hatBeta (m+1)) (weightC (A.B.a.clock.hatBeta (m+1)))
-- checkpoint nonempty independent stencil, price precision
variable (T_x:Fellows (K:=K) (Hx:=Hx) (c:=c) U hm R' E)
local notation "fp"=> rescueX U hm hr hp hR 0 hd Ψ
local notation "Xa"=> Concourse.outgoing B0 (hol G) W₀ fp Z R' E T_x.y T_x.p
local notation "Ta"=> Concourse.honour (hol G) W₀ Z R' T_x.y
local notation "Ya"=> Concourse.reserve B0 (hol G) W₀ fp Z R' E T_x.y T_x.p
variable (ht: Staff («P»:=P) («m»:=m+1) («n»:=n) («N»:=N) R' E Yp (Hx.angle 0) l K c p κ)
-- enable.No presum.
include ht hr hκ
lemma descend : Nonempty (Fellows (K:=K) (Hx:=Hx) (c:=c) U hm R' E):=by
   let X:= LocalLTE.Concourse.memo ((F0).e0) R'
   obtain ⟨Vo⟩:= Vinca.proposed (Issue.trail P) N n m (hol G) (MergeProof.rack_format Z X (memo_format _ ht.format)) (MergeProof.keeps Z X (memo_cost _ ht.credit)) -- argument P x implicit.Expected X
   refine ⟨Vo, Classical.choice (LocalLTE.Concourse.Center.licenses B0 (hol G) R' E (U.mountY hm hr hκ R' E ht.holdings))⟩ -- order
-- actual payment for ANY offerings within
include hG hp hR hd hT hX hκ
lemma tollgate : Staff («P»:=P) («m»:=m) («n»:=n) («N»:=N) Ta Xa (Ya Yp) (Hx.angle 0) l K c p κ ∧ (Ta).density 0 B0 Ω=(A.B.a.clock.op m n).push ((Ωu).beta) (R'.density 0 B0 Ωu) ∧ ((Labels.frames G).level 0).coeffSize ((Ta).x-R'.x) ≤ limitT m N c A.B.a:=by
   have hx:= U.tide hm hd hG hT R' T_x.y ht.credit ht.format -- order check
   obtain ⟨hC,hb⟩:=U.stampsY hm hd hG hr hκ hp hR hX hT R' E Yp Ψ T_x.y T_x.p ht.holdings ht.receipt
   refine ⟨⟨hx.1,hx.2.2.1,hb,hC⟩,hx.2.1,?_⟩
   rw [show (Ta).x-R'.x=_ from (show _= (Concourse.ticketP (hol G) W₀ Z R' T_x.y).x-(F0).e0 from add_sub_cancel_right ..)]; exact hx.2.2.2
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
