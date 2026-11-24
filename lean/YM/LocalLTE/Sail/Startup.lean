import YM.LocalLTE.Sail.Village
/-! Summit precision and ancestry from common Family. Explicit registration policy. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
open Legato.Spool LocalLTE.Sail MergeProof Menu Accent Spiral Planned.GuardedAtom Guard
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n m i :ℕ}(V:∀ d,Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
    (r0:ℕ→ℕ)(hV:∀ d,d+3 ≤ (Issue.trail P).levels.clock.J (r0 d))
open Spiral Pressure ConnectedActivityE6
variable {M p0 r q TT K P0 p' :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)(hp: Market M K P0 p0 TT l G ζ A.delay) (hD: Patronage K P0 p' p0 TT ζ A.delay)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hG:G.Simple)(hL:∀ i j,(R.target i j).halo=500)(hl:East.stagnate q 500<l) (he:0<ζ)
variable {I:Type} [DecidableEq I][Fintype I]
    (B:Marker.Census I)(Y:Batch (Issue.trail P) N n I)(v₀:I)
    (h:Y.Roles V m W r0 K)
variable (hR:∀ d, r0 d ≤ N → Registers U V d (r0 d))
variable {z: GuideF}{Tt:ℕ→Mallow.ConcertZ R.target M ζ}(hU: Mobility AX R.shape A.delay z Tt K l TT κ)
-- Bill normalized paint estimate.Cone. Weight.Lambda and support currencies preserved.
variable (π:∀ i:ℕ,i≤N→Y.steering i)
variable (Xθ:∀ i:ℕ, FrameBox.Grove (0:Site (A.B.a.S.side i n)))
  (Xf:∀ (j:I) (i:ℕ), ((Labels.frames G).level (Y.demand j)).Coeff → Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side i n))
  (hh:∀ j, GalaC U hr hl hL (Y.demand j) (V (Y.demand j)) (Xf j) Xθ m)
variable (hm:m<N)
-- Pack units including all shared. 
noncomputable abbrev topQ(j:I):= stampField H N n (Y.motion j) (fun i=> Y.origin i j) (π N le_rfl j) (Xf j N (Y.voice j))
set_option quotPrecheck false
local notation "v'"=> (Coat.gStep ((Issue.trail P).rep N n N).beta)
set_option quotPrecheck false
local notation "b"=> (v'^((P0:ℝ)+1))
local notation "ξ"=> Real.sqrt (A.B.a.clock.forcedAllowance N)
local notation "K'"=> (fun i=>(Y.named V (π N le_rfl) i).forced)
local notation "E"=> U.commence B Y v₀
local notation "Q"=> (Issue.trail P).rep N n N
structure AtBirth (N₀:ℕ) :Prop where
     enjoys : Appendix.Prepared B Q E (Y.origin N) (Y.requested V N) K' (Y.raw B)
     pay : Appendix.Budget B Q E (fun _=>1) 0 0 (v'^((N₀:ℝ)+1)) 0 ξ
     seals (j:I): FrameReport Q (Y.origin N j) (Y.named V (π N le_rfl) j) (topQ Y π Xf j) (hol G) ξ (v'^((N₀:ℝ)+1))
include hp hR hr hm h hV hh hD
lemma billet : AtBirth U V B Y v₀ π Xf P0:=by
    have hpN : ∃ i,N=i+1:= ⟨N-1,by omega⟩; obtain ⟨i,rfl⟩:=hpN
    let X' := A.B.a.S; let R':=U.port (i+1) i n (show i<(i+1) from by omega); let z:= allocationK (A.B.a.clock.hatBeta (i+1)) ζ
    have hx i hz:=U.charged (i+1) i n hz
    obtain ⟨hx',hz,hk⟩:= U.born_precision V r0 hV hr hp B Y v₀ h hR (π (i+1) le_rfl) (rfl : i+1=i+1) (show m≤ i from by omega) (fun _=>1) (fun _=>zero_lt_one) (fun _=>le_rfl)
    have hj:(Issue.trail P).rep (i+1) n (i+1) = R'.inPort:= hx i (Nat.lt_add_one _)
    let Y₁:= A.B.a.clock.hatBeta (i+1); let x:= A.B.a.clock.hatBeta i; let v0:= (Coat.gStep ((Issue.trail P).rep (i+1) n (i+1)).beta)^((P0:ℝ)+1); let J:= A.B.a.clock.J (i+1); let j:= A.B.a.clock.J i; let J':=A.B.a.clock.J (i+1)
    have hβ: Y₁/2 ≤ ((Issue.trail P).rep (i+1) n (i+1)).beta ∧ ((Issue.trail P).rep (i+1) n (i+1)).beta ≤ 2*Y₁:=by -- Q (i+1)=R'.inPort requires dependent type not defeq n between (i+1) & i+1. revise above with subst early.
       rw [hj]; exact R'.senses.2
    have hW (p:I):r0 (Y.demand p) ≤ i:=(h.phase.registered p).trans (show m≤ i from ?_)
    swap
    · omega
    have ht(p:I):Y.demand p ≤ A.B.a.clock.J i:= (Nat.le_add_right (Y.demand p) 3).trans ((hV _).trans (A.B.a.fits.mono (hW p)))
    have he:=step_paid A.B.a i; have ht0:Y₁=betaF G x (D.L J'):= beta_eq A.B.valid i
    have hf (p:I): LocalLTE.River.rotationP ((Labels.frames G).level (Y.demand p)) (X.p.profile J').order (X.p.profile J').power *Y₁^(grantZ p0 TT 0) ≤ v0 ∧ z ≤ v0:=by
        have h:=hD.frames _ _ he x (A.B.valid.pays i) _ (ht p) 0 (Nat.zero_le _)|>.stamp; rw [←ht0] at h; have hh:=h (((Issue.trail P).rep (i+1) n (i+1)).beta) hβ.1 hβ.2; exact ⟨hh.2.1,hh.2.2.1⟩
    have h0: z*Real.sqrt (A.B.a.clock.forcedAllowance (i+1)) ≤ v0*Real.sqrt (A.B.a.clock.forcedAllowance (i+1)):= mul_le_mul_of_nonneg_right (hf v₀).2 (Real.sqrt_nonneg _)
    refine ⟨hx',⟨Port.budgetUp _ _ hz.trueB le_rfl le_rfl h0,hz.cope,Port.budgetUp _ _ hz.rented le_rfl le_rfl h0⟩,fun p=>?_ ⟩
    let A':= A.B.a; have he':=(hh p).deeds _ hm.le (le_refl _); have hv:= he'.l (Y.voice p); let κ:= z -- edit shadow
    let d:=Y.demand p; let F:=Y.voice p; have hz0:=hR _ ((hW p).trans (by omega)); let t:=(V d).tone (i+1)
    have hX:LocalLTE.River.rotationP ((Labels.frames G).level d) ((Issue.trail P).rep (i+1) n (i+1)).p.order ((Issue.trail P).rep (i+1) n (i+1)).p.power=LocalLTE.River.rotationP ((Labels.frames G).level d) (X.p.profile J').order (X.p.profile J').power:=by rw [show ((Issue.trail P).rep (i+1) n (i+1)).p=A.B.a.budget (i+1) from (P.choice.represents _ _ _ le_rfl).vac,Rain.jersey (A:=A) (m:=i+1)|>.1,Rain.jersey (A:=A) (m:=i+1)|>.2.1]
    have hO:t.index F=F:=by rw [← hz0.contract.head.heard.currents F]; exact hz0.contract.head.out _
    simp_rw [Nat.sub_self] at hv
    apply auditor (localSection G d) (Y.motion p) _ _ hv (sound G d) ((by decide:2 ≤ 4).trans (actual_side_ge (Issue.trail P|>.S) (i+1) n)) _
    -- audit after shifts.Normalization ζ at (i+1)=1 precisely.
    rw [sample_top, norm_one, one_mul,hX]; change LocalLTE.River.rotationP _ _ _ * (Y₁^(grantZ p0 TT 0) *_ ) ≤ _; apply le_trans _ (hf p|>.1)
    let P':=(Labels.frames G).level d; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (River.rotation_one ..)); apply mul_le_of_le_one_right (Real.rpow_nonneg (zero_le_one.trans ((A.B.a.fits.delayed _).le)) _); change P'.coeffSize (t.index F) ≤ 1; rw [hO]; exact h.phase.marks p
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
