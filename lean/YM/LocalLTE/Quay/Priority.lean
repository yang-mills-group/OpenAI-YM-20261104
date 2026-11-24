import YM.LocalLTE.Quay.Beam
import YM.MergeProof.South.Window
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
local notation "F0"=> ((Labels.frames G).level 0)
open MeasureTheory Accent Marker
open Set Function Lattice Wilson RG Source Labels Extra.Histories Motion
-- supported polynomial coefficient book stays full.This file assembly from actual kernels not ℂ guess. Proof physical.
set_option quotPrecheck false
variable {V:Type}[DecidableEq V][Fintype V]
    (B:Marker.Census V) (Wz:V→ℕ)(v:∀ i:V, ((Labels.frames G).level (Wz i)).Coeff)
local notation "b"=> localSection G
local notation "Ψ"=> (Issue.trail P).rep N n N
-- shape exact products (actual normalization at substrate.Address not assuming reference scale for unscaled).
noncomputable def rawN(v':V): Config G (A.B.a.S.side N n)→ℂ:= presented (localSection G (Wz v')) (0:Site (A.B.a.S.side N n)) (Ψ).p.threshold (v v')
local notation "rN"=> (rawN (N:=N) (n:=n) (P:=P) Wz v)
local notation "qN"=> Accent.birth B Ψ rN
local notation "δ" i:max=> Real.sqrt (A.B.a.clock.forcedAllowance i)
-- every position sector
include P N n
lemma outlays (i:B.Mode): (fun x=>(qN x).part i)= gValue («N»:=N) (P:=P) (n:=n) Wz i.val v:=by
    let bX:= ((Issue.trail P).rep N n N).p
    funext V; unfold Accent.birth; rw [Poly.part_smul]; unfold Accent.Mach gValue; rw [Extra.Trajectories.pass_fire, fareK, Finset.prod_apply]; rfl
-- use dominated.W. finite Poly terms integrable individually. 
lemma giddy : Integrable (qN) (prior G (A.B.a.S.side N n)):=by
    apply (integrable_pi_iff).mpr; intro i; change Integrable (fun U=> (qN U).part i) _
    have hc : Continuous (fareK (Ψ).p Wz v i.val (0:Site (A.B.a.S.side N n))):=by
       let f(z:V):= rN z; have hp: Continuous (fun x=>∏ z∈ i.val,f z x):= continuous_finsetProd _ (fun z _=> (localSection G (Wz z)).continuous_places _ 0)
       change Continuous (∏ z∈ i.val, f z); rw [show (∏ z∈ i.val, f z)=_ from (show _=(fun x=>∏ z∈ i.val,f z x) from (by funext i; rw [Finset.prod_apply]))]; exact hp
    rw [outlays (N:=N) (P:=P)]
    have hz : Continuous ((Issue.trail P).rep N n N|>.eval):=by rw [show ((Issue.trail P).rep N n N|>.eval)=_ from (P.choice.starts N n).2]; exact bare_cont _
    have h : Continuous (gValue («N»:=N) (P:=P) (n:=n) Wz i.val v) := (Complex.continuous_ofReal.comp hz).mul hc
    let f : Config G (A.B.a.S.side N n)→ℂ:= gValue («N»:=N) (P:=P) (n:=n) Wz i.val v; change Integrable f (prior G (A.B.a.S.side N n)); have hx:Continuous f:=h; exact Continuous.integrable_of_hasCompactSupport hx (HasCompactSupport.of_compactSpace _)
variable (i:ℕ)(hM:i≤N)
noncomputable abbrev vista : Config G (A.B.a.S.side i n) → Poly B:= Accent.gust (Issue.trail P) N n N (qN) i hM
local notation "s'"=> vista B Wz v i hM -- inference? make
lemma arms (J':B.Mode)(hq:Integrable qN (prior G (A.B.a.S.side N n))) : (fun x=>(vista («P»:=P) (N:=N) (n:=n) B Wz v i hM x).part J')=Accent.gust (Issue.trail P) N n N (gValue («N»:=N) (P:=P) (n:=n) Wz J'.val v) i hM:=by
    induction hM using Nat.decreasingInduction with
    | self => rw [vista,gust_base,gust_base]; exact outlays ..
    | of_succ i h ih=>
       rw [vista,gust_step («k»:=i) H N n N qN h,gust_step («k»:=i) H N n N _ h]; exact (Accent.push_get ((Issue.trail P).levels.transition_mass ..) (Accent.gust_live _ _ _ _ _ hq h) J').trans (congr_arg _ ih)
-- actual SINGLE summit units.S at THAT Y calibrations. equality push precise.
variable (j:V) (K':Extra.Histories.Music ((Labels.frames G).level (Wz j)) (Issue.trail P) N n) {ρ:ℕ}
    (ht:Sung (localSection G (Wz j)) (Issue.trail P) N n (hol G) W ρ K')
variable (hdT: TransferData ((Labels.frames G).level (Wz j)) (Issue.trail P) N n)
    (hΨ:hdT.entries=(K'.draft (Issue.trail P)).inits)
    (he:hdT.Based (hol G) (localSection G (Wz j)) ρ)
include hΨ he
local notation "Pp" j:max=> ((Issue.trail P).rep N n j)
local notation "z" i:max=> (Sail.sampleNorm H N (Wz j) i)
noncomputable def panorama (i:ℕ): Coefficient ((Labels.frames G).level (Wz j)) ((Issue.trail P).S.side i n):= Extra.Histories.stretch (z i) ((K'.tone i).plays (v j))
local notation "P₁" i:max=> panorama Wz v j K' i
include ht hM
omit [DecidableEq V] [Fintype V] in
lemma tune (hi:ρ ≤ i) : (P₁ i).Format 0 (hol G) ((Issue.trail P).rep N n i) ∧ (P₁ i).density 0 (localSection G (Wz j)) ((Issue.trail P).rep N n i)= gust H N n N (gValue («N»:=N) (P:=P) (n:=n) Wz {j} v) i hM:=by
    let H':=H; let d:= Wz j; let q:= (localSection G d)
    have he'(s:ℕ): (P₁ s).density 0 (localSection G d) (H'.rep N n s)= z s • (hdT.entries s (v j)).density 0 q (H'.rep N n s):=by rw [hΨ]; funext U'; apply stretch_density
    refine ⟨stretch_format _ ((ht.earned i hi hM).earns (v j)|>.1),?_⟩
    induction hM using Nat.decreasingInduction with
    | self=>
       rw [show _ = _ from (he' N), Sail.sample_top, one_smul, gust_base]; funext U; let v':=(v j); let Z':ℂ:= ((H').S.a N : ℂ)^d
       rw [he.encode]; unfold gValue; let h₀ := (P.choice.represents _ n _ (show N ≤ N from le_rfl)).vac; rw [h₀]; unfold Vault.fareK; rw [Finset.prod_singleton];
       let u := (presented (localSection G (Wz j)) (0:Site ((H).S.side N n)) ((Issue.trail P).levels.clock.threshold N) (v j)) U; let x:ℂ:=↑((H'.rep N n N).eval U); change Z'*x*(Z'⁻¹*u)=x*u; have hh: Z'≠0:= pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H'.S.a_pos N).ne'); field_simp
    | of_succ i hS ih=>
       let S':= (Issue.trail P).levels.clock.op i n; let x:=(H).β N n (i+1); let c':=(q); have hg:=Extra.Histories.play_integrable (B:=q) H' N P.choice hS (he.format _ (hi.trans i.le_succ) hS (v j)) (he.cap _ (hi.trans i.le_succ) hS (v j))
       rw [gust_step H' N n N _ hS,←ih (hi.trans i.le_succ), he', he', he.unnormalized i hi hS (v j),Sail.sample_step] -- Goal smul. uses H'.levels congr.
       rw [StepData.push_smul _ _ _ _ hg,smul_smul, mul_comm]
-- End articulation of cylinders with assigned symbol.V.A.Path.
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
