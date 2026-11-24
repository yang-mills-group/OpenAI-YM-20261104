import YM.LocalLTE.Quay.Core
import YM.LocalLTE.Orbit.Sky
import YM.LocalLTE.Keels.Spark
import YM.LocalLTE.Quay.Guide
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
local notation "Θ"=> (H).rep N n m
local notation "B"=> A.B.a
-- center readout at calibrated components. Exact.EP export.
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {M p0 r q :ℕ}{κ ε:ℝ}{Hx:Heights}{K:ℕ}(hr: Spool.Terms R.shape κ p0 r l q M K ε A.delay Hx)
variable (hp:East.stagnate q 500<l)(hR:∀ i j,(R.target i j).halo=500)
variable (d:ℕ) (v:((Labels.frames G).level d).Coeff)(hv:((Labels.frames G).level d).coeffSize v≤1)
    (Yt: Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n) {ρ:ℕ}
    (he: Sung (localSection G d) (Issue.trail P) N n (hol G) W ρ Yt)
variable (Ψ:∀ i:ℕ, FrameBox.Grove (0:Site (A.B.a.S.side i n)))
variable (fX:∀ i:ℕ, ((Labels.frames G).level d).Coeff → ℕ→ Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side i n))
local notation "z" i:max=> Sail.sampleNorm H N d i
local notation "f"=> ((Labels.frames G).level d)
include he U hv
lemma pinnacleT : ∀ i:ℕ,ρ ≤ i→ i ≤ N→ let x:= (Yt.tone i).index v; ‖z i‖ * (f).coeffSize ((f).core x) ≤ (1/2:ℝ)^(N-i) ∧ ‖z i‖ * (f).coeffSize x ≤ 2-(1/2:ℝ)^(N-i) :=by
    intro i hi hx
    induction hx using Nat.decreasingInduction with
    | self=>
       have hQ: (Yt.tone N).index v=v:=(he.head.heard.currents v).symm.trans (he.head.out v)
       rw [hQ,Sail.sample_top]; simpa using! (show (f).coeffSize ((f).core v) ≤ 1 ∧ (f).coeffSize v ≤ 2-(1:ℝ) from ⟨(Work.G08.size_core ..).trans hv,hv.trans_eq (by norm_num)⟩) -- eq
    | of_succ m hm ih=>
        intro x'; obtain ⟨hR0,hP'⟩:= ih (hi.trans m.le_succ); let t:= (Yt.tone m); obtain ⟨hx,hA⟩:= Concourse.forwardT (Issue.trail P) W (Yt.tone (m+1)) t (localSection G d) (he.earned _ (hi.trans (m.le_succ)) hm) (he.earned _ hi hm.le) (he.step _ hi hm) U.tag.clock.bank v -- order
        let q:= ‖z (m+1)‖ *(f).coeffSize ((f).core ((Yt.tone (m+1)).index v))
        have hF: (1/2:ℝ) *q ≤ 1/2*(1/2:ℝ)^(N-(m+1)):=mul_le_mul_of_nonneg_left hR0 (by norm_num)
        rw [show N-m=N-(m+1)+1 from (by omega),pow_succ,mul_comm (_^_) ((1:ℝ)/2)]; refine ⟨hx.trans hF,hA.trans ((add_le_add hP' hF).trans ?_)⟩; exact le_of_eq (by ring)
variable (hs:TourX U hr hp hR d Yt Ψ fX ρ)(h₀:d+3 ≤ (Issue.trail P).levels.clock.J ρ)
local notation "Γ"=> (T).senses
local notation "βt"=> weightC Y K
local notation "P1"=> Extra.Histories.stretch (z m) ((Yt.tone m).plays v)
local notation "P0"=> Extra.Histories.stretch (z m) (fX m v K)
open Keels Drift Sail -- Spiral maybe
variable (ht:Spool.Scope K p0 A.delay)(hP:ρ ≤ m)
-- `center_core` ensures cap independent STAGES even BEFORE rotating.Ve.
include hv he ht hP hs h₀ hm
lemma orderX : Exhibition (localSection G d) κ (l*Pressure.radiusB Y) (Hx.angle d K) (hol G) ((Issue.trail P).rep N n m) P1 P0 (Real.sqrt (A.B.a.clock.forcedAllowance m)) (2*(A.B.a.clock.hatBeta m)) (Spool.powerR p0 ((Issue.trail P).rep N n (m+1)|>.beta))∧ (P1).Format 0 (hol G) ((Issue.trail P).rep N n m):=by
    have hz:= hs.income m hP hm.le; have hb:= (T).senses.2
    let k:=P1; let t:= (T); let s:= (P0); have hc : d+3≤A.B.a.clock.J m:=h₀.trans (A.B.a.fits.mono hP)
    have he':0 ≤ (Y):=zero_le_one.trans ((A.B.a.fits.delayed _).le); let d':= (f).coeffSize ((Yt.tone m).index v); have hxC:‖z m‖ * d' ≤ 2:= (Harmonics.pinnacleT U (N:=N) (n:=n) d v hv Yt he m hP hm.le|>.2).trans (sub_le_self 2 (by positivity))
    have hR1:= (show Drift.Book _ _ _ _ _ _ _ _ _ _ _ _ _ from hz).annual v K (le_refl K)
    let y:= betaF G (Y) (D.L J); let β:= ((Issue.trail P).rep N n (m+1)|>.beta); have heδ: betaF G (Y) (D.L J)=A.B.a.clock.hatBeta (m+1):= Push.PriceCompiler.beta_eq A.B.valid m|>.symm
    have hxB: β = t.inPort.beta:= congr_arg (fun R:Rep G (A.B.a.S.side (m+1) n)=> R.beta) (U.charged N m n hm)
    have heκ:=ht.estimate _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) d ((Nat.le_add_right d 3).trans hc)|>.limits β (heδ.symm ▸ (hxB.symm ▸ hb.1)) (heδ.symm ▸ (hxB.symm ▸ hb.2)) -- compare
    obtain ⟨hQ,hq,hxL,hB,hX₀,hd⟩:=heκ
    refine ⟨(Exhibition.buckets (z m) hR1).pledge ?_ ?_, stretch_format _ (he.earned _ hP hm.le|>.earns v).1⟩
    · change ‖z m‖*((Y)* d') ≤ 2*_; exact le_trans (le_of_eq (by ring : _= (‖z m‖*d')*Y)) (mul_le_mul_of_nonneg_right hxC he')
    change ‖z m‖* (weightC (A.B.a.clock.hatBeta m) K * d') ≤ _; refine le_trans (le_of_eq (by ring : ‖z m‖* (βt*d')= (‖z m‖*d')*βt)) ((mul_le_mul_of_nonneg_right hxC hQ).trans (le_trans ?_ hB)); apply mul_le_mul_of_nonneg_right _ hQ; nlinarith only [(X.p.profile (A.B.a.clock.J (m+1))).columns_ge]
-- top comparison. top unit wallet need weight in *INPUT* of TOP-1.A.
omit hP
lemma summitP (hM : N=m+1)(hδ:ρ  ≤ m) : let P':=(Yt.tone N).plays v
    Exhibition (localSection G d) κ (l*Pressure.radiusB (A.B.a.clock.hatBeta N)) (Hx.angle d K) (hol G) ((Issue.trail P).rep N n N) P' (fX N v K) (Real.sqrt (A.B.a.clock.forcedAllowance N)) (A.B.a.clock.hatBeta N) (Spool.powerR p0 ((Issue.trail P).rep N n N|>.beta)):=by
    intro P'; let y:= A.B.a.clock.hatBeta N
    have hQ : (Yt.tone N).index v=v:= (he.head.heard.currents v).symm.trans (he.head.out v)
    have hc:= hs.income N he.ahead (le_refl N)
    have hz := (show Drift.Book _ _ _ _ _ _ _ _ _ _ _ _ _ from hc).annual v K (le_refl K); rw [hQ] at hz -- function stage proof
    refine hz.pledge (mul_le_of_le_one_right (zero_le_one.trans ((A.B.a.fits.delayed _).le)) hv) ((mul_le_of_le_one_right (show 0≤weightC y K from Real.rpow_nonneg (zero_le_one.trans ((A.B.a.fits.delayed _).le)) _) hv).trans ?_)
    have he'δ : d ≤ I:=(Nat.le_add_right d 3).trans (h₀.trans (A.B.a.fits.mono hδ)); have hu:= (T).senses.2; let t:= (T); let β:= t.inPort.beta
    have hb': β= ((Issue.trail P).rep N n N|>.beta):=by unfold β; rw [show t.inPort=_ from (U.charged N m n hm).symm]; rw [show (m+1)=N from hM.symm] -- rw motive.
    have hy: A.B.a.clock.hatBeta (m+1)= Pressure.betaF G (A.B.a.clock.hatBeta m) (D.L J):= Push.PriceCompiler.beta_eq A.B.valid m; have hf:= ht.estimate _ _ (step_paid A.B.a m) _ (A.B.valid.pays m) d he'δ|>.limits β (hy ▸ hu.1) (hy ▸ hu.2)
    rw [← hb']; refine le_trans ?_ hf.2.2.2.2.2; apply Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le ((A.B.a.fits.delayed _).le)) _ (bitN _)
    unfold y; have heY:N=m+1:=hM; rw [heY,hy]; exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
