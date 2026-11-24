import YM.LocalLTE.Quay.Mint
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

-- aspect ~ forecast ledger power read on supported Coefficient.The analysis reading at OUT after ports.
variable (i:ℕ) (hP:m ≤ i)(hM:i≤N)
local notation "Λt"=> Hx.angle 0
local notation "F0"=> ((Labels.frames G).level 0)
local notation "B0"=> localSection G 0
local notation "Ω'"=> ((Issue.trail P).rep N n i)
local notation "Xℓ"=> A.B.a.clock.hatBeta i
variable (F: SlipRole G (Issue.trail P) i n)
    {φ: Config G ((Issue.trail P).S.side N n)→ℂ} (hZ:VoucherC (P:=P) (n:=n) c p i N F (Hx.angle 0) l K κ φ)
variable (hT':Package R.shape κ p r l K d c ι₀ ε A.delay)
local notation "E"=> (F.paints K)
noncomputable abbrev proposal (F: SlipRole G (Issue.trail P) i n)(K:ℕ):= memo F.τ (F.paints K)
local notation "Xp"=> proposal (P:=P) i F K -- P not inferred
local notation "Zb"=> (if i=N then ((Issue.trail P).rep N n N).beta else ((Issue.trail P).rep N n (i+1)).beta)
local notation "δ"=> Real.sqrt (A.B.a.clock.forcedAllowance i)
local notation "s"=> powerR p Zb
include hm hM U hZ hT'
set_option maxHeartbeats 400000 in
lemma crystalV : F.X.Format 0 (hol G) Ω'∧ Exhibition B0 κ (l*Pressure.radiusB Xℓ) (Hx.angle 0 K) (hol G) Ω' F.X (proposal (P:=P) i F K) (Real.sqrt (A.B.a.clock.forcedAllowance i)) ((A.B.a.clock.hatBeta i)+4) (powerR p (if i=N then ((Issue.trail P).rep N n N).beta else ((Issue.trail P).rep N n (i+1)).beta))∧ ‖(F.X.x) 0‖≤3:=by
    obtain ⟨he,hV,hq,hE⟩:= hZ
    obtain ⟨hP',ht,hx,hν⟩:= hV
    have hΓ:0 ≤ Xℓ:= zero_le_one.trans ((A.B.a.fits.delayed _).le)
    have hxV : weightC Xℓ K ≤ s ∧ oath p Xℓ ≤ s:=by
        obtain rfl|hM:= eq_or_lt_of_le hM
        · rw [if_pos rfl]; have hI : ∃ u:ℕ,i=u+1:=by exact ⟨i-1,by omega⟩ -- name i substituted N? 
          obtain ⟨u,rfl⟩:= hI; let Z':=(U.port (u+1) u n (by omega)); have hvβ := Z'.senses.2
          have hv:=hT'.bought _ _ (step_paid A.B.a u)|>.2 _ (A.B.valid.pays u);
          let y:=betaF G (A.B.a.clock.hatBeta u) (D.L (A.B.a.clock.J (u+1))); let t:=A.B.a.clock.hatBeta (u+1); let z:= A.B.a.clock.hatBeta u
          have hp : ((Issue.trail P).rep (u+1) n (u+1)).beta=Z'.inPort.beta:=congr_arg (fun a=>Rep.beta a) (U.charged (u+1) u n (by omega))
          have hx:t=y:=beta_eq A.B.valid u; have h0 :1≤ z:= (A.B.a.fits.delayed _).le; have he: z ≤ t:=hx.symm ▸ le_add_of_nonneg_right (Work.E04.shift_nonneg ..); let X:= weightC z K
          have h₀:0 ≤ weightC z K:=Real.rpow_nonneg (zero_le_one.trans h0) _; have h₁:0 ≤ oath p y:= pow_nonneg (inv_nonneg.mpr (zero_le_one.trans (h0.trans (he.trans hx.le)))) _
          have ht:t/2 ≤ Z'.inPort.beta ∧ Z'.inPort.beta≤2*t:= hvβ
          have he: oath p z≤ powerR p Z'.inPort.beta:= hv.2.2.2 _ (show y/2≤Z'.inPort.beta from hx ▸ ht.1) (show _≤2*y from hx ▸ ht.2)
          have hy: z ≤ t:=hx.symm ▸ le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
          rw [hp]; refine ⟨( (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le h0) hy (bitN K))).trans ((le_add_of_nonneg_right h₁).trans (le_trans hv.2.2.1 he)),?_⟩
          change oath p t ≤ _; rw [hx]; exact (le_add_of_nonneg_left h₀).trans (le_trans hv.2.2.1 he)
        rw [if_neg hM.ne]; have hB:= (U.port N i n hM).senses.2; let z:= A.B.a.clock.hatBeta i; let y:=betaF G z (D.L (A.B.a.clock.J (i+1))); have hx: A.B.a.clock.hatBeta (i+1)=betaF G z (D.L (A.B.a.clock.J (i+1))):= beta_eq A.B.valid i
        have hv:=hT'.bought _ _ (step_paid A.B.a i)|>.2 _ (A.B.valid.pays i); have hm:y≥z:=le_add_of_nonneg_right (Work.E04.shift_nonneg ..); have hV':0 ≤ oath p y:=pow_nonneg (inv_nonneg.mpr (hΓ.trans hm)) _
        rw [show ((Issue.trail P).rep N n (i+1))= _ from U.charged N i n hM]; have ht:= hv.2.2.2 (U.port N i n hM|>.inPort.beta) (hx ▸ hB.1) (hx ▸ hB.2); exact ⟨(le_add_of_nonneg_right hV').trans (hv.2.2.1.trans ht),ht⟩
    -- projection. actual ancestors.Y including Canon ν receipts.
    have hvP : (F0).coeffSize F.X.x≤ 3:=hq.trans (sub_le_self _ (by positivity)); have hh: (F0).coeffSize F.τ ≤ 4:=by
        apply (Work.G08.size_triangle (F0) F.τ F.X.x).trans; rw [Work.G08.size_sub_rev];
        have hV: oath p Xℓ≤1:=pow_le_one₀ (inv_nonneg.mpr hΓ) (inv_le_one_of_one_le₀ ((A.B.a.fits.delayed _).le)); linarith only [hvP,hx,hV]
    have hf:= (hν.slip K le_rfl).pledge (le_refl _) hxV.1; have hE:(decrement F.X (memo F.τ (F.paints K))).regular=(decrement (memo (0:(F0).Coeff) F.X) (F.paints K)).regular:=rfl
    let k:= Xp; let x:=F.X
    have h :decrement x k = memo (F.X.x-F.τ) (decrement (memo 0 x) E):=rfl
    refine ⟨hP',⟨?_,memo_format F.τ hf.format,hf.layout,?_,?_,hx.trans hxV.2⟩,?_⟩
    · exact ⟨hh.trans (le_add_of_nonneg_left hΓ), (hf.stock.raise (by linarith only [show (0:ℝ)≤4 from by norm_num] : Xℓ≤ Xℓ+4) (le_refl _) (le_refl _)).regular,hf.stock.forced⟩ -- Kcalc
    · exact h.symm ▸ memo_format (F.X.x-F.τ) hf.trade
    · exact h.symm ▸ memo_force (F.X.x-F.τ) hf.fee
    rwa [← Concourse.center_size]
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
