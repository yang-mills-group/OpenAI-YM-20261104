import YM.LocalLTE.Orbit.Harvest
import YM.LocalLTE.Drift.Values
import YM.LocalLTE.Ballot.Boat
import YM.LocalLTE.Orbit.Sky
import YM.LocalLTE.Keels.Wishes
import YM.LocalLTE.Ticket.Tissue
import YM.LocalLTE.Drift.Story
import YM.LocalLTE.Ticket.Oracle
import YM.LocalLTE.Ticket.Parade
import YM.LocalLTE.Ticket.Pump
import YM.LocalLTE.Ballot.Pane
/-! Dues bought and ports ON ACTUAL Stage. Epoch grade supplied in companion schedule. -/
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
open Spiral Push Fan Legato.Spool
variable {M p0 r q TT :ℕ}{κ ζ ε:ℝ}{Hx:Heights}{K:ℕ}(hr: Spool.Terms R.shape κ p0 r l q M K ε A.delay Hx)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hp:East.stagnate q 500<l)(hR:∀ i j,(R.target i j).halo=500)

-- stage reading and exposure
variable (hX:1≤q)
local notation "π"=> torsoZ hr hp hR m n
variable (d:ℕ)(hd:d+3≤ A.B.a.clock.J m)
local notation "g"=> Hx.angle d
local notation "t"=> Hx.uplink d
local notation "w"=> Hx.grade d
open Drift
local notation "A0"=> (T|>.inPort)
local notation "Za"=> (R.target J I)
local notation "c"=> ((Hx.angle d) 0)
local notation "L"=> D.L J
local notation "f"=> (localSection G d)
local notation "F0"=> ((Labels.frames G).level d)
local notation "κ'"=> (T).ranch.allocation.κ
variable (X0:FrameBox.Grove (0:Site (A.B.a.S.side m n)))
local notation "bY"=> Bandage.aperture U.tag N m n T d hd
local notation "β"=> betaF G Y L

local notation "ℓ"=> (l*Pressure.radiusB Y)
-- entropy actor.Authorization actual. article provenance per census Booth.H.
local notation "UT"=> (begun hr d hd)
local notation "x'"=> (X.p.profile I)
local notation "y'"=> (X.p.profile J)
local notation "B1"=> Legato.Spool.outlay (X.p.profile I) (X.p.profile J) l d r L ε (R.target J I) (R.shape.μ J I) Y ((T).inPort.beta) UT
local notation "Yv"=> Harmonics.shipform U hm hr hp hR d hd X0
local notation "Ppp"=> U.port N m n hm
local notation "δ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
open Mallow

local notation "h1" => U.charged N m n hm
local notation "hz" => U.baptism N m n hm
local notation "hP"=> (U.lays d N n m hm)
local notation "P0" => rescueX U hm hr hp hR d hd X0
local notation "Y₀"=> (A.B.a.clock.hatBeta m)
local notation "Bz"=> (B1)
variable (P₀:Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
local notation "o1"=> P₀.tone (m+1)
local notation "o0"=> P₀.tone m

-- local trajectory receipts using the actual prior column spectra.NEOS.
local notation "Θ"=> (H).rep N n m
local notation "P₁"=> (H).rep N n (m+1)
local notation "R1"=> H
local notation "Y1"=> (A.B.a.clock.hatBeta (m+1))
local notation "Qκ"=> (T|>.ranch.allocation.κ)

-- ceremony exposure. One family across all epochs, at declared pre cutoff. Inputs opaque actual ports.Ppt
variable (X' :∀ i:ℕ,FrameBox.Grove (0:Site (A.B.a.S.side i n)))
variable (fX:∀ i:ℕ, ((Labels.frames G).level d).Coeff→ ℕ→ Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side i n))

-- normalized orientation producer. Consumers can predict *reset step and inverse* including relative projected lead/principal, normalized orientation outputs (input indexed by THAT inverse), including regular and complete K. Using true coordinates from W at each step; not a formal recurrence translating frames across constructions.
variable (ρ P0':ℕ)(hx:Sung (localSection G d) (Issue.trail P) N n (hol G) W ρ P₀)
variable (hρ:d+3≤(Issue.trail P).levels.clock.J ρ)(hs: Spool.Scope K P0' A.delay)(hb:TourX U hr hp hR d P₀ X' fX ρ)
local notation "K0" => ((H).rep N n m) -- macro needs H..
local notation "S0"=> weightC Y K
local notation "uQ"=> ((F0).coeffSize)
local notation "Uv"=> (o0|>.index)
local notation "Xp"=> (o1|>.index)
local notation "V0"=> Keels.rotor F0 (o1) (o0)
local notation "b"=> ((S0))
include hb hm
-- angular order after normalization readback in frame.X.Full lead.
lemma ranked (hI:ρ ≤ m) (j:ℕ)(hj:j≤ K): Ledger F0 (A.B.a.S.side m n) (fun v=> fX m v j):=by
   obtain ⟨hd,v,Υ,h,hx⟩:= hb.prep _ hI hm
   let S:= Υ; have hPV:= Drift.previewP f (hol G) (U.lays d N n m hm) (U.rescueX hm hr hp hR d hd (X' m)) _ _ v Υ j hj -- Γ missing.Car
   -- rewriting fX m v requires defeq.
   rw [hx]; exact hPV
local notation "wT"=> (fun v=> fX m v K)
local notation "qG"=> Coat.gStep ((Issue.trail P).rep N n (m+1)).beta
-- Ticket.Back.Read. This proof stored internally to use anytime.
structure Kinematics (sz:ℝ) (Z:((Labels.frames G).level d).Coeff→ Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side m n)) (p1 h rk:ℕ)(κ:ℝ) : Prop where
    story: ∃ (hPz: Ledger ((Labels.frames G).level d) ((Issue.trail P).S.side m n) Z) (Lx : (F0).Coeff≃ₗ[ℂ] (F0).Coeff), Lx.toLinearMap= Keels.nextK F0 (o1) Z hPz ∧
       (∀ i v, Motion.patch F0 i (Lx v) = Lx (Motion.patch F0 i v)) ∧
       ∀ i, let a:= (Uv).symm i; let r:= (Z ((Xp).symm (Lx.symm i))); let s:= (qG^((p1:ℝ)+1))* ((Labels.frames G).level d).coeffSize i
         (F0).coeffSize (Lx i - V0 i) ≤ s ∧ (F0).coeffSize (Lx.symm i - (V0).symm i) ≤ s ∧ r.x=i∧ Exhibition (localSection G d) κ h rk (hol G) ((Issue.trail P).rep N n m) (P₀.tone m|>.plays a) r (Real.sqrt ((Issue.trail P).levels.clock.forcedAllowance m)) (sz*(F0).coeffSize i) s -- precedence fix names clash.
include hx hρ hs
set_option maxHeartbeats 500000 in
lemma curator (hi:ρ ≤ m): Harmonics.Kinematics d P₀ (2*Y) (wT) P0' (l*Pressure.radiusB Y) (Hx.angle d K) κ :=by
    have hd : d+3 ≤ A.B.a.clock.J m:= hρ.trans (A.B.a.fits.mono hi)
    have he:= hb.income m hi hm.le; let bank:= wT; let X₁:= uQ
    obtain ⟨he0,vR,Υ,hv,hT⟩:= hb.prep _ hi hm
    let a:= (Ppp); let β₁:= (Issue.trail P).rep N n (m+1)|>.beta
    have hΨ: Ledger F0 (A.B.a.S.side m n) bank:=by unfold bank; rw [hT]; exact Drift.previewP f (hol G) (hP) (U.rescueX hm hr hp hR d he0 (X' m)) _ _ vR Υ K (Nat.le_refl _)
    have hℓ:∀ v:F0|>.Coeff, Exhibition f κ (l*Pressure.radiusB Y) (Hx.angle d K) (hol G) Θ ((o0).plays v) (bank v) δ (Y *X₁ (Uv v)) (weightC Y K * X₁ (Uv v)):= (fun v=> (show Drift.Book _ _ _ _ _ _ _ _ _ _ _ _ _ from he).annual v K (Nat.le_refl _))
    let eC:= (P₁).beta
    let w':= (Spool.powerR P0' eC); have hp0 := (Ppp).senses.2
    have hy: β = Y1:= Push.PriceCompiler.beta_eq A.B.valid _|>.symm
    have hy': β₁=a.inPort.beta:= congr_arg (fun z=> z.beta) (U.charged N m n hm)
    have h := hs.estimate _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) _ ((Nat.le_add_right d 3).trans hd)|>.limits β₁ (hy ▸ (hy'.symm ▸ hp0.1)) (hy ▸ (hy'.symm ▸ hp0.2)) -- order
    obtain ⟨hE,hPz,hpm,hQ,hS,h'⟩:= h
    let T0':=(P₀.tone (m+1))
    have hX0:= hx.earned (m+1) (by omega) hm; have hY0:= hx.earned _ hi hm.le; let G':= Keels.nextK F0 (P₀.tone (m+1)) bank hΨ
    obtain ⟨L',hL,Hm⟩:= Keels.tender F0 f (hol G) T0' (o0) W bank hΨ hX0 hY0 hℓ (zero_le_one.trans ((hr.pay _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)).1)) hE hPz (hx.step _ hi hm) U.tag.clock.room U.tag.clock.bank
    refine ⟨hΨ,L',hL,?_,?_⟩
    · intro i v; have he:∀ v,(L' v)=G' v:= fun v=> LinearMap.congr_fun hL v
      rw [he, he]; change Motion.patch F0 i (bank ((Xp).symm v)|>.x)=(bank ((Xp).symm (Motion.patch F0 i v))).x; unfold bank; rw [hT]; exact Drift.commutes _ _ (hP) (U.rescueX hm hr hp hR d he0 (X' m)) _ _ vR Υ K le_rfl i v
    intro i hdP Vc μ
    have hy': 2*(1+(H|>.levels.params m).columns)*weightC Y K ≤ w':=by change 2*(1+(A.B.a.params m).columns)*_ ≤ _; rw [params_eq A.B.valid]; exact hS
    obtain ⟨hh,hv,he,hX'⟩:= Hm i; let u:=X₁ i; have ht : 0 ≤ u:= Work.G08.size_nonneg ..
    have hf':(H).S.block m=D.L J:= Push.PriceCompiler.block_eq A.B.valid m
    refine ⟨?_,?_,he, (hX'.pledge ?_ ?_)⟩
    · rw [Work.G08.size_sub_rev]; apply hh.trans; apply mul_le_mul_of_nonneg_right _ ht; change weightC Y K *((A.B.a.params (m+1)).columns*((H).S.block m|>.val:ℝ)^d) ≤_; rw [hf', show A.B.a.params (m+1)= y' from params_eq A.B.valid _]; exact hpm
    · rw [Work.G08.size_sub_rev]; apply hv.trans
      change (A.B.a.params (m+1)).columns*weightC Y K*(2*u)≤_; rw [show A.B.a.params (m+1)= y' from params_eq A.B.valid _]; refine le_trans (le_of_eq (by ring : _ = 2*(y'|>.columns)*(weightC Y K)*u)) (mul_le_mul_of_nonneg_right hQ ht)
    · change Y*(2*u)≤2*Y*u; exact le_of_eq (by ring)
    change (1+(A.B.a.params m).columns)*weightC Y K*(2*u)≤ w'*u; refine le_trans (le_of_eq (by ring : _=2*(1+(A.B.a.params m).columns)*(weightC Y K)*u)) (mul_le_mul_of_nonneg_right hy' ht)
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
