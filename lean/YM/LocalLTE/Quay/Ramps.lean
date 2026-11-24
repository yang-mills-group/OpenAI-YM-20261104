import YM.LocalLTE.Quay.Priority
/-!
# Multi results as full density-moment modules. Actual supports/log currency
-/
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
open Accent MeasureTheory Extra.Trajectories
variable {V:Type}[DecidableEq V][Fintype V]
    (B:Marker.Census V) (Wz:V→ℕ)(v:∀ i:V, ((Labels.frames G).level (Wz i)).Coeff)
local notation "vV"=> vista («P»:=P) (N:=N) (n:=n) B Wz v
local notation "Φ"=> (H).rep N n N
local notation "S"=> A.B.a
variable (X' : ∀ i:ℕ, FrameBox.Grove (0:Site (A.B.a.S.side i n)))
-- inspect any study. at all lengths m<= sj
variable (i:ℕ)(hΨ:m ≤ i)(he:i ≤ N)
local notation "f'"=> (Hx).angle 0
local notation "k"=> ((Labels.frames G).level 0)
local notation "Z'"=> (Issue.trail P).rep N n i
local notation "g"=> A.B.a.clock.hatBeta i
local notation "φ"=> (if i=N then (Φ).beta else ((Issue.trail P).rep N n (i+1)).beta)
local notation "εs"=> (powerR p φ)
local notation "u₀"=> Real.sqrt (A.B.a.clock.forcedAllowance i)
variable (α:B.Mode) (E:∀ i:ℕ,SlipRole G (Issue.trail P) i n)
    (hE:Harmonics.Orator (N:=N) U hr hp hR Wz α.val v X' E c p d ι₀ m)
local notation "E₀"=> ((E i).X)
local notation "P₀"=> Harmonics.proposal i (E i) K

local notation "R₀"=> ((Issue.trail P).S.side i n)
set_option quotPrecheck false
include hm
include hT hE hΨ
-- single mixed-mode.
lemma linesT : (∀ x:Config G (R₀), (vV i he x).part α=(E₀).density 0 (localSection G 0) Z' x) ∧ (E₀).Format 0 (hol G) Z' ∧ Exhibition (localSection G 0) κ (l*Pressure.radiusB g) (Hx.angle 0 K) (hol G) Z' E₀ P₀ u₀ (g+4) εs :=by
    have ht:= hE.schedule i hΨ he
    have h := crystalV U (m:=m) hm i he (E i) ht hT -- includes implicit p etc.
    refine ⟨fun x=> ?_, h.1,h.2.1⟩; exact congr_fun ((arms B Wz v i he α (giddy B Wz v («P»:=P))).trans ht.sampling.symm) x -- order
omit hT hE
variable (j:V) (V':Extra.Histories.Music ((Labels.frames G).level (Wz j)) (Issue.trail P) N n) {ρ:ℕ}
    (ht:Sung (localSection G (Wz j)) (Issue.trail P) N n (hol G) W ρ V')
    (Aξ: TransferData ((Labels.frames G).level (Wz j)) (Issue.trail P) N n)(hA : Aξ.entries=(V'.draft (Issue.trail P)).inits)
    (hf:Aξ.Based (hol G) (localSection G (Wz j)) ρ)
    (hx:m≤N) (hv:((Labels.frames G).level (Wz j)).coeffSize (v j)≤ 1)
    (hr':ρ ≤ m)(hρ: Wz j+3 ≤ (Issue.trail P).levels.clock.J ρ)
variable (fX:∀ i:ℕ, ((Labels.frames G).level (Wz j)).Coeff → ℕ→ Coefficient ((Labels.frames G).level (Wz j)) ((Issue.trail P).S.side i n)) (ht':TourX U hr hp hR (Wz j) V' X' fX ρ) (hK:Scope K p0 A.delay)
local notation "φS"=> panorama Wz v j V'
local notation "pS" i:max=> Extra.Histories.stretch (Sail.sampleNorm (Issue.trail P) N (Wz j) i) (fX i (v j) K)
local notation "ιZ"=> ((vV i he))
-- stamps make actual hats. Unit.E.Step. gStrong
include hm hΨ he ht hA hf hv hr' hρ ht' hK
lemma portV : (∀ x:Config G (R₀), (vV i he x).part (B.fire j)=(φS i).density 0 (localSection G (Wz j)) Z' x) ∧ (φS i).Format 0 (hol G) Z' ∧ Exhibition (localSection G (Wz j)) κ (l*Pressure.radiusB g) (Hx.angle (Wz j) K) (hol G) Z' (φS i) (pS i) u₀ (2*g) (powerR p0 φ) :=by
   have hC:= tune Wz v i he j V' ht Aξ hA hf (hr'.trans hΨ)
   refine ⟨fun x=> congr_fun ((arms B Wz v i he (B.fire j) (giddy B Wz v («P»:=P))).trans hC.2.symm) x,hC.1,?_⟩
   rcases eq_or_lt_of_le he with hi|hi
   · subst i; rw [if_pos rfl]; unfold panorama; rw [Sail.sample_top]; unfold Extra.Histories.stretch; simp only [one_smul];
     obtain ⟨k',he⟩:∃ k',N=k'+1:= ⟨N-1,by omega⟩
     have hq:= Harmonics.summitP U (show k'<N from by omega) hr hp hR (Wz j) (v j) hv V' ht X' fX ht' hρ hK he (show ρ ≤ k' from by omega)
     apply hq.pledge _ le_rfl; exact le_mul_of_one_le_left (zero_le_one.trans ((A.B.a.fits.delayed N).le)) one_le_two
   rw [if_neg hi.ne]; exact (Harmonics.orderX U hi hr hp hR (Wz j) (v j) hv V' ht X' fX ht' hρ hK (hr'.trans hΨ)).1
-- vacuum exact.No K decomposition from another pole or canon coefficients. 
omit hm hΨ ht hA hf hv hr' hρ ht' hK
lemma first_cost : (fun x=> (vV i he x).part B.quiet)= liftVac H N n i:=by
   rw [Harmonics.arms («P»:=P) B Wz v i he B.quiet (giddy B Wz v («P»:=P))]; let f:= gValue («N»:=N) («P»:=P) («n»:=n) Wz (B.quiet|>.val) v
   induction he using Nat.decreasingInduction with
   | self => rw [gust_base]; funext x; unfold gValue; simp only [Marker.Census.quiet,Vault.fareK,Finset.prod_empty,Pi.one_apply, mul_one,liftVac]
   | of_succ i hi ih=> rw [gust_step H N n N _ hi,vac_transfer H N n i P.choice hi]; exact congr_arg _ ih
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
