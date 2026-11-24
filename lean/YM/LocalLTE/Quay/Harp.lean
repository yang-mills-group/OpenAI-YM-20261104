import YM.LocalLTE.Quay.Moor
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
variable (V':Coefficient ((Labels.frames G).level 0) ((Issue.trail P).S.side (m+1) n))
    (E:ℕ→ Coefficient ((Labels.frames G).level 0) ((Issue.trail P).S.side (m+1) n))
noncomputable abbrev rateSpan (s k:ℕ):ℝ:= (1/2:ℝ)^(k-(s+1)) -- s < k
noncomputable def limitT (s:ℕ)(H0: ℕ)(c:ℕ) (A:Levels G):ℝ:= if s=H0 then culture (A.params s) c else rateSpan s H0
-- note H macro collision
local notation "U'" i:max=> limitT i N c A.B.a
local notation "f'"=> Hx.angle 0
open LocalLTE.Drift
variable (y: ((Labels.frames G).level 0).Coeff)
variable (Ψ:FrameBox.Grove (0:Site (A.B.a.S.side m n)))
local notation "S₀"=> (U.port N m n hm)
local notation "x₀"=> A.B.a.clock.hatBeta m
local notation "z'"=> A.B.a.clock.hatBeta (m+1)
local notation "η'"=> (weightC (z'))
local notation "ε'"=> (weightC x₀)
local notation "δ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
local notation "B0"=> (localSection G 0)
local notation "F0"=> ((Labels.frames G).level 0)
local notation "T0"=> rescueX U hm hr hp hR 0 hd Ψ
local notation "LL"=> D.L J -- rename
local notation "xg"=> (LL).val*Pressure.radiusB x₀
variable (Yx:Syllabus (Issue.trail P) N n m (hol G) (rack (U.kube N (m+1) n hm) (memo ((Labels.frames G).level 0).e0 V')) (limitT (m+1) N c A.B.a))
    (RB: Paper («H»:=Issue.trail P) (m:=m) (N:=N) (p:=n) (localSection G 0) (hol G) E K (Hx.angle 0) ((D.L (A.B.a.clock.J (m+1))).val*Pressure.radiusB (A.B.a.clock.hatBeta m)) (U.port N m n hm|>.ranch.allocation.κ) (fun _=> A.B.a.clock.hatBeta (m+1)) (weightC (A.B.a.clock.hatBeta (m+1))))
local notation "G'"=> (X.p.profile I)
local notation "Vx"=> (X.p.profile J)
local notation "Xp"=> (Concourse.outgoing B0 (hol G) W₀ T0 Z V' E Yx RB)
local notation "Zp"=> (Concourse.ticketP (hol G) W₀ Z V' Yx)
local notation "Xq"=> (Concourse.honour (hol G) W₀ Z V' Yx)
local notation "Yp"=> (Concourse.reserve B0 (hol G) W₀ T0 Z V' E Yx RB)
local notation "Cp"=> (culture Vx c)
local notation "tp"=> ((S₀).ranch.allocation.κ)
variable (hV: LocalLTE.Concourse.Center (localSection G 0) (hol G) ((Issue.trail P).rep N n (m+1)) V' E (Hx.angle 0) K (l*(A.B.a.budget (m+1)).B) κ (Real.sqrt (A.B.a.clock.forcedAllowance (m+1))) (fun _=> A.B.a.clock.hatBeta (m+1)) (weightC (A.B.a.clock.hatBeta (m+1))) (weightC (A.B.a.clock.hatBeta (m+1)))) (hP:((Labels.frames G).level 0).coeffSize (V'.x-y)≤ oath p (A.B.a.clock.hatBeta (m+1)))
    (hE:V'.remBound 0 ((Issue.trail P).rep N n (m+1)) (Real.sqrt (A.B.a.clock.forcedAllowance (m+1))) (limitT (m+1) N c A.B.a))
local notation "μ"=> (outlay (X.p.profile I) (X.p.profile J) l 0 r LL ε (R.target J I) (R.shape.μ J I) x₀ ((T).inPort.beta) (begun hr 0 hd))
include hκ hr hV
lemma mountY : LocalLTE.Concourse.Center B0 (hol G) Ωu V' E (f') K xg tp (Real.sqrt (A.B.a.clock.forcedAllowance (m+1))) (fun _=> z') (weightC (z')) (weightC (z')):=by
    rw [(hκ N m n hm).2]; have he:=hr.pay _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)|>.2.1
    rw [← beta_eq A.B.valid] at he; exact LocalLTE.Concourse.Center.trim B0 (hol G) hV _ he -- args order
omit hκ hr hV in
private lemma fee_above (x₁ v t:ℝ)(h:x₁*v≤t)(ht:1≤x₁)(hz:0≤t) : v≤t:= by by_cases H0: v ≤ 0; exact H0.trans hz; exact (le_mul_of_one_le_left (not_le.mp H0|>.le) ht).trans h
include hG hP hp hR hd hT hX
lemma stampsY : LocalLTE.Concourse.Center B0 (hol G) Ω (Xq) (Xp) (f') K (l*Pressure.radiusB x₀) κ δ (fun _=> x₀) ε' ε' ∧ ((Labels.frames G).level 0).coeffSize ((Xq).x- Yp y) ≤ oath p x₀:=by
     have hV':= hT.bought _ _ (step_paid A.B.a m)|>.2 x₀ (A.B.valid.pays m); have hf: z'= betaF G x₀ LL:= beta_eq A.B.valid m
     have hz1:1≤ x₀:= (A.B.a.fits.delayed m).le; have hφ: limitT (m+1) N c A.B.a ≤ Cp:=by unfold limitT; rw [params_eq A.B.valid (m+1)]; split; exact le_rfl; exact (pow_le_one₀ (by norm_num) (by norm_num)).trans (culture_pos ..)
     have hv: 1 ≤ hoist G' Vx 0 G:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (rotation_one ..) (Motion.orbitCost_one_le _)) (Vx).columns_ge
     have he(i): 0 ≤ weightC x₀ i:= Real.rpow_nonneg (zero_le_one.trans hz1) _
     let B1:=μ; let u' := Real.sqrt (A.B.a.clock.forcedAllowance (m+1)); let a':= (S₀).inPort.beta; have ht:= (S₀).senses.2
     have hx:= hV'.2.1.expenses a' u' (hf ▸ ht.1) (hf ▸ ht.2) (glyphBound A.B.a (m+1)|>.2)
     let q:=H ; have hq:= U.certK hm hG hr hκ hp hR hX 0 hd Ψ
     have hΛ:∀ i,i≤K→ B1.peak (Cp) (fun _=> z') (η') (η') i ≤ x₀:=by
        intro i hi; rw [hf]; apply fee_above _ _ _ ((mul_comm _ _|>.trans_le (hx.1 i hi|>.1))) hv (zero_le_one.trans hz1) -- shadow lemma includes too much
     have hΖ:∀ i,i≤K→ B1.delta (Cp) (fun _=> z') (η') (η') (fun i=>u'*(weightC z' i+weightC z' i)) i ≤ (ε') i:=by
        intro i hi; -- rewrite won't change u'
        rw [hf]; exact fee_above _ _ _ (hx.1 i hi|>.2) hv (he i)
     have hxF:= U.mountY hm hr hκ V' E hV
     have hY(i)(hi:i<K): B1.slip (Cp) (fun _=> z') η' η' (i+1) +B1.slip (Cp) (fun _=> z') η' η' i ≤ (weightC x₀ i):=by
         rw [hf]; exact fee_above _ _ _ (hx.2 i hi) hv (he i)
     obtain ⟨hQ,hv⟩:=Concourse.center B0 (hol G) W₀ Z V' E Yx RB (μ) hq.1 hq.2 hxF _ hφ y hP (fun _=> x₀) ε' ε' hΛ hΖ hY (fun i _=> hr.born.pour 0 i) -- Order
     refine ⟨?_,hv.trans ?_⟩
     · let qX := Xp; change Center _ _ _ _ qX _ _ _ _ _ _ _ _; rw [← (hκ N m n hm).2]; exact hQ
     rw [hf]; exact hV'.2.2.1
include hE
omit hV hκ hr hp hR hd hX hP
-- smaller payments.
variable (hR':V'.Format 0 (hol G) ((Issue.trail P).rep N n (m+1)))
include hd hR'
lemma tide : (Xq).Format 0 (hol G) Ω ∧ (Xq).density 0 B0 Ω=(A.B.a.clock.op m n).push ((Ωu).beta) (V'.density 0 B0 Ωu) ∧ (Xq).remBound 0 Ω δ (limitT m N c A.B.a) ∧ ((Labels.frames G).level 0).coeffSize ((Zp).x- ((Labels.frames G).level 0).e0) ≤ limitT m N c A.B.a:=by
    have hv:=U.epochB hm hd hG V' hR' hE Yx
    let t':= scaler G' l LL; have hX:t'*Cp≤1/2:=(hT.bought _ _ (step_paid A.B.a m)).1; have hq:t'≤1/2:= (le_mul_of_one_le_right (scaler_pos ..) (culture_pos ..)).trans hX
    suffices he:t'*(U' (m+1)) ≤ limitT m N c A.B.a from ⟨hv.1,hv.2.1,rem_mono hv.2.2.1 he,hv.2.2.2.trans he⟩
    unfold limitT; rw [if_neg (show ¬m=N from hm.ne)]; split
    next h'=> rw [show A.B.a.params (m+1)=Vx from params_eq A.B.valid _,rateSpan,← h',Nat.sub_self,pow_zero]; exact hX.trans (by norm_num)
    next h'=> apply le_trans (mul_le_mul_of_nonneg_right hq (show 0 ≤ rateSpan (m+1) N from pow_nonneg (by norm_num) _)); rw [mul_comm,←pow_succ]; unfold rateSpan; rw [show N-(m+1+1)+1=N-(m+1) from (by omega)] -- pow_succ defeq reorder
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
