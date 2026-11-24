import YM.LocalLTE.Quay.Diamond
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
variable {V:Type}[DecidableEq V][Fintype V]
    (B:Marker.Census V) (Wz:V→ℕ)(v:∀ i:V, ((Labels.frames G).level (Wz i)).Coeff)
local notation "vV"=> vista («P»:=P) (N:=N) (n:=n) B Wz v
local notation "Φ"=> (H).rep N n N
variable (X' : ∀ i:ℕ, FrameBox.Grove (0:Site (A.B.a.S.side i n)))
variable (i:ℕ)(hΨ:m ≤ i)(he:i ≤ N)
local notation "Z'"=> (Issue.trail P).rep N n i
local notation "g"=> A.B.a.clock.hatBeta i
local notation "φ"=> (if i=N then (Φ).beta else ((Issue.trail P).rep N n (i+1)).beta)
local notation "εs"=> (powerR p0 φ)
local notation "u₀"=> Real.sqrt (A.B.a.clock.forcedAllowance i)
local notation "S"=> (A.B.a.S)
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
structure Booklet (κ:ℝ)(p p0:ℕ)(A0:ℝ)(α:B.Mode)(d:ℕ) (Z Q':Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side i n))(ξ τ:ℕ) : Prop where
     full : Z.Format 0 (hol G) ((Issue.trail P).rep N n i)
     ball : Exhibition (localSection G d) κ ξ τ (hol G) ((Issue.trail P).rep N n i) Z Q' (Real.sqrt (A.B.a.clock.forcedAllowance i)) A0 (Spool.powerR p0 φ)
     story x: (vV i he x).part α = Z.density 0 (localSection G d) ((Issue.trail P).rep N n i) x
     reads x : flags ((Issue.trail P).rep N n i).p.threshold x=∅→ let u:= ((Issue.trail P).rep N n i).eval x; let y:= u⁻¹ • vista («P»:=P) (N:=N) (n:=n) B Wz v i he x; u>0 ∧ y.part α=Z.exponentialEntry 0 (localSection G d) ((Issue.trail P).rep N n i) x ∧ ‖y.part α-Q'.exponentialEntry 0 (localSection G d) ((Issue.trail P).rep N n i) x‖≤ Spool.powerR p φ -- scalar complex? real smul
variable (r0:ℕ→ℕ)(Y':∀ d N n :ℕ, TransferData ((Labels.frames G).level d) (Issue.trail P) N n)
    (H₁:(Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r0 Y').Makes)
local notation "y'" k=> (A.B.a.params k).columns
variable (hS : LaneQ A.delay p p0)
include hS hm U he
local notation "a"=> (X.p.profile (A.B.a.clock.J i)).columns
private lemma fees : (3+a)* εs ≤powerR p (if i=N then (Φ).beta else ((Issue.trail P).rep N n (i+1)).beta):=by
    rcases eq_or_lt_of_le he with hh|ht
    · subst i; obtain ⟨u,hu⟩:∃ x:ℕ,N=x+1:=⟨N-1,by omega⟩; subst N; rw [if_pos rfl]
      let h:= (U.port (u+1) u n (by omega)); have hv := hS.frame _ _ (step_paid A.B.a u) _ (A.B.valid.pays u); let β:= h.inPort.beta; let y:= A.B.a.clock.hatBeta (u+1); rw [← beta_eq A.B.valid] at hv; have hb := hv β h.senses.2.1 h.senses.2.2
      have he: ((Issue.trail P).rep (u+1) n (u+1))= h.inPort:= U.charged (u+1) u n (by omega); rw [he]; apply le_trans _ hb; refine mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (zero_le_one.trans (X.p.profile _).columns_ge)) ?_
      exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
    let h:=U.port N i n ht; rw [if_neg ht.ne]; have hv := hS.frame _ _ (step_paid A.B.a i) _ (A.B.valid.pays i)
    let β:= h.inPort.beta; rw [← beta_eq A.B.valid] at hv; have hb:= hv β h.senses.2.1 h.senses.2.2; rw [U.charged N i n ht]; apply le_trans _ hb; rw [add_right_comm]; refine mul_le_mul_of_nonneg_right ?_ ?_
    · apply le_add_of_nonneg_right (zero_le_one.trans (X.p.profile _).columns_ge)
    exact Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
variable (d':ℕ)(hR': r0 d' ≤ i) {δ C₀:ℝ} (Z₀ Q: Coefficient ((Labels.frames G).level d') ((Issue.trail P).S.side i n))
    (α:B.Mode)
local notation "Fp"=> ((Labels.frames G).level d')
local notation "AZ"=> (localSection G d')
variable {b' s':ℕ}
include H₁ hR'
lemma diamond (h: Z₀.Format 0 (hol G) ((Issue.trail P).rep N n i))(hQ:Exhibition (localSection G d') κ b' s' (hol G) ((Issue.trail P).rep N n i) Z₀ Q (Real.sqrt (A.B.a.clock.forcedAllowance i)) C₀ (powerR p0 φ)) (ht': Z₀.remBound 0 ((Issue.trail P).rep N n i) (Real.sqrt (A.B.a.clock.forcedAllowance i)) δ) (hZ: ∀ x,(vista («P»:=P) («n»:=n) B Wz v i he x).part α= Z₀.density 0 AZ Z' x): Booklet (P:=P) B Wz v i he κ p p0 C₀ α d' Z₀ Q b' s':=by -- hr not used
    let S₀ := ((Issue.trail P).rep N n i).p
    have hs :S₀=A.B.a.budget i:= (P.choice.represents N n i he).vac
    have ha:(X.p.profile (A.B.a.clock.J i)).columns=(A.B.a.params i).columns:= congr_arg Stage.columns (params_eq A.B.valid i).symm
    have hD(j:Fp|>.Index): S₀.Regular (AZ|>.footprint (0:Site (A.B.a.S.side i n))) (AZ|>.places (Pi.single j 1) (0:Site (A.B.a.S.side i n))) ∧ S₀.supBounds 0 (AZ|>.footprint (0:Site (A.B.a.S.side i n))) (AZ|>.places (Pi.single j 1) (0:Site (A.B.a.S.side i n))) (a* S₀.threshold^((Fp).grades j).2):=by rw [hs,ha]; exact H₁.priced _ _ n hR' _ j -- beta
    refine ⟨h,hQ,hZ,fun x hx=>?_⟩
    have ht:= Spool.sparkle (Z') AZ x h hQ ht' hD hx (glyphBound A.B.a i|>.2) (X.p.profile (A.B.a.clock.J i)).columns_ge
    intro c y; have he':(y.part α) = ((c:ℂ)⁻¹*((Z₀).density 0 AZ Z' x)):=by change (c⁻¹:ℝ) • (((vV i _ x)).part α) = _; rw [hZ x]; simp [Complex.real_smul] -- proof irrelevance
    exact ⟨ht.1,he'.trans ht.2.1,he'.symm ▸ (ht.2.2.trans (Harmonics.fees U hm i he hS))⟩ -- shadow
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
