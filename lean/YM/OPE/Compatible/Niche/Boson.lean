import YM.OPE.Compatible.Niche.Railway
import YM.OPE.Compatible.Niche.Roller
import YM.OPE.Compatible.Niche.Acme
/-! # Actual frame posteriors.Leg.C.Trust at one arbitrary period sufficiently tall.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl
open Function Filter Set MeasureTheory Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input RG.Shoot
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest Stroke.MatchZ
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ ThroughLaunch Zeph
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι :Type} {G :Gauge} {P: MapPrices}
variable {P':Patch}{n N i j m p l:ℕ}{H:Sponsor G}{T:Seasons H}{s:Sheet G}{t:ℕ→ℕ}
section Story
open Next.Foundations
local notation "M"=> ThroughLaunch.currency s P t
variable {S:Supply.Rolls (ThroughLaunch.raise s t)}{A:Alloy (ThroughLaunch.currency s P t) S}(C:Bolt A)(F:Factor A)
local notation "E"=>A.B.a.clock
local notation "J"=>A.B.a.clock.J
local notation "jν"=> J (m+1)
local notation "ξ"=>A.B.a.S
set_option quotPrecheck false
local notation "ζP"=> Reach (A:=A) m
local notation "ν"=>A.B.kin.alpha
variable (h: Torrent (s:=s) H.X P H.l A.post A.B.a A.B.M A.B.kin)(hs:Lend s T)(g:G.Simple)(hy:m+1<N)(hn:Nest F C)
local notation "zV"=> (s.profile (J m)).clip
local notation "zW"=> (s.profile (J (m+1))).clip
local notation "Dx"=> Mug ζP zW zV T (J m) (chart G) (PadQ H ζP)
local notation "Z!"=> ruler h hs hy
local notation "η"=> ηSz A m p
local notation "S!"=> A.B.a.clock.op m p
local notation "BK"=> PadQ H ζP
-- choose canonical Can/Rep. syntax use superP
variable (he:Lac A m p)
include g he hy hs h
local notation "Φ"=>berthQ C h hs g hy he
local notation "ZQ"=> F.books
variable {Y:ℕ→ℝ}{L0:Bid.Worth}(Yq:Bandage F Y L0)
omit he h hs
include hn Yq
local notation "ρ"=> J m
local notation "P'!"=> J (m+1)
lemma Austen : Coffer (F.books) ζP P'! ρ:=by
       have he:= enact F g (Reach (A:=A) m) F.books C hn rfl (p:=0) Yq depR rfl rfl hy; exact ⟨rfl,⟨A.B.a.fits.mono (Nat.le_succ m),A.B.a.fits.stepSlow m⟩,he.1⟩
local notation "v!"=> Austen C F g hy hn Yq
open YM.AnalyticBridge.VerifiedReset Time
local notation "T'"=> (ThroughLaunch.currency s P t).p.profile (J m)
local notation "Tf"=> (ThroughLaunch.currency s P t).p.profile P'!
local notation "t0"=> A.B.a.clock.hatBeta m
local notation "z"=> ν N m
omit Yq
lemma tallyE : θj t0 ^2 * |(C.history N p m).beta - (C.history N p (m+1)).beta-z| ≤ credit G (s.profile ρ) * ℰb t0:= by
        have he:= πreset F (p:=p) g C hn (Nat.lt_trans (Nat.lt_succ_self _) hy); unfold forecastE at he; rw[params_eq A.B.valid m] at he; exact he
variable (ht:credit G (s.profile (A.B.a.clock.J m))* ℰb (A.B.a.clock.hatBeta m) ≤ θj (A.B.a.clock.hatBeta m) ^ 2)
include ht
lemma feesF : |z|≤ rangeV ζP G (s.profile P'!) :=by
       let x:=(C.history N 0 (m+1)).beta; let y:=(C.history N 0 m).beta; let L:= rangeV ζP G (s.profile P'!)
       have hc: |y-x-z| ≤ 1:= le_of_mul_le_mul_left ((tallyE C F g hy hn (p:=0) |>.trans ht).trans (by rw [mul_one])) (pow_pos (A.B.a.budget m).threshold_pos _)
       have hx:= (C.choice.steps N 0 m (Nat.lt_trans (Nat.lt_succ_self m) hy)).2; change |x-y-G.slopeConstant*Real.log (A.B.a.S.block m).val| ≤ (A.B.a.params (m+1)).drift at hx; rw [depQ,params_eq A.B.valid] at hx; let v:= Δfare G (Reach (A:=A) m).L; change |x-y-v| ≤ (s.profile (J (m+1))).drift at hx; change _≤ (s.profile (J (m+1))).drift+|v|+1; rw[abs_le] at hc hx ⊢; constructor <;> linarith only [hc.1,hc.2,hx.1,hx.2,le_abs_self v,neg_le_abs v]
omit g hy hn ht in
lemma peekR (hx:m ≤ N): Tag (s.profile (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) (C.history N p m).p (C.history N p m).beta:=by
         have hv:= (C.sticks N p).prices m (Nat.zero_le _) hx; rw[hv.1.point]; change Tag ((ThroughLaunch.currency s P t).p.profile _) _ _ _; rw [←params_eq A.B.valid]; exact ⟨rfl,rfl,rfl,rfl,rfl, (C.choice.represents N p m hx).band⟩
include h hs he Yq
local notation "Q0"=> BootU A.θ F.books (Austen C F g hy hn Yq)
lemma Realty :∃ t1:Pillar (Q0) Φ (A.B.a.clock.hatBeta m), Aud (Q0) Φ ((ThroughLaunch.currency s P t).p.profile (J (m+1))) ((ThroughLaunch.currency s P t).p.profile (J m)) t0 t1:=by
        -- Pillar readiness transport by Matrol
        let U:= Φ; obtain ⟨S,hS⟩:=posture C F hn hy (h:=g) Yq _ (show U.hostS.Z=S! from canyon hs); obtain ⟨V,ha,hb⟩:=boast A.θ F.books (Austen C F g hy hn Yq) U S hS
        refine ⟨V,ha,hb,?_,⟨?_,?_⟩,feesF C F g hy hn ht, tallyE C F g hy hn, ?_⟩
        · rw [← PassF]; exact ⟨peekR C hy.le,peekR C ((Nat.le_succ m).trans hy.le)⟩
        · rw [←PassF]; exact SoftRise h hs hy
        · exact SoftRise h hs (Nat.lt_trans (Nat.lt_succ_self m) hy)
        have h0:= (C.choice.steps N p m (Nat.lt_trans (Nat.lt_succ_self m) hy)).1; change _=(SlotF (K:=H) (ηSz A m p)).push _ _; rw [canyon hs]; exact h0
end Story
end YM.OPE.Owl
