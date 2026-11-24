import YM.LocalLTE.Quay.Gate
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
-- summit READ. period accounting.File compatibility
local notation "p'"=> (Issue.trail P).rep N n N
local notation "s'"=> A.B.a.S.side N n
local notation "F0"=> ((Labels.frames G).level 0)
local notation "B0"=> (localSection G 0)
local notation "c'"=> (X.p.profile (A.B.a.clock.J N)).columns
local notation "Ux"=> (A.B.a.clock.hatBeta N)
variable {Jt:Type} (Wz: Jt→ℕ)(I':Finset Jt)(k:∀ i:Jt, ((Labels.frames G).level (Wz i)).Coeff)
     (hv:∀ i∈I',Wz i≤d)(ht: I'.card ≤ c)(hq':∀ i∈I', ((Labels.frames G).level (Wz i)).coeffSize (k i) ≤ 1)
variable (χ:FrameBox.Grove (0:Site (A.B.a.S.side N n)))
set_option quotPrecheck false
local notation "Zi"=> fareK ((p').p) Wz k I' (0:Site (A.B.a.S.side N n))
local notation "Px"=> ((s'):(Side))
noncomputable def tentN (K:ℕ) := (U.kube N N n (le_refl _)).supply (fun _:ℕ=> Push.AbsoluteSums.Animals.neighbors (terr G K + 1) (0:Site (A.B.a.S.side N n)))
noncomputable abbrev escortP (d:ℕ) := draw F0 p' (Animals.neighbors (terr G d+1) (0:Site (A.B.a.S.side N n))) Zi (Harmonics.tentN («N»:=N) (n:=n) U d)
local notation "Q"=> escortP (N:=N) (n:=n) U Wz I' k d -- order
noncomputable def hintN (d j:ℕ)(κ:ℝ)(_s:ℕ):= Vault.roughHat (Zi-Vault.halcyon (Zi)) χ F0 (terr G d) j κ
local notation "AQ"=> hintN (P:=P) Wz I' k χ d ι₀ κ
-- permits even Φ∈α. ensure arity slots have income.
local notation "S"=> (A.B.a.clock)
include hκ hT hr hp hv ht hq' hm
lemma winter (he:1 ≤ ι₀)(hz: ι₀ ≤Hx.angle 0 0+1)(hP: ∀ z∈I',∀ i, (p'|>.p).Regular ((localSection G (Wz z)).footprint (0:Site (s'))) ((localSection G (Wz z)).places (Pi.single i 1) (0:Site (s'))) ∧ (p'|>.p).supBounds 0 ((localSection G (Wz z)).footprint (0:Site (s'))) ((localSection G (Wz z)).places (Pi.single i 1) (0:Site (s'))) ((c')*(p'|>.p.threshold)^(((Labels.frames G).level (Wz z)).grades i).2)):
    Staff («P»:=P) («N»:=N) («n»:=n) (m:=N) Q (AQ) ((Zi 1) • (F0).e0) (Hx.angle 0) l K c p κ ∧ (∀ U', (Q).density 0 B0 (p') U'= ((p').eval U':ℂ)* Zi U') ∧ (F0).coeffSize ((Q).x)≤1:=by
    obtain ⟨k',hk⟩:∃ x,N=x+1:=⟨N-1,by omega⟩; subst N; let Z':=(U.port (k'+1) k' n (by omega)); have hκ': (Z').ranch.allocation.κ=κ:= (hκ _ _ _ (by omega)).2; obtain ⟨v',hz'⟩:= (Z').ranch.allocation.paid
    let W:=X.p.profile (A.B.a.clock.J (k'+1)); let y:= A.B.a.clock.hatBeta (k'+1); let θ:= R; let H':= A.B.a
    have hx' : 0<l:= lt_of_le_of_lt (Nat.zero_le _) hp; have hR1:= hT.bought _ _ (step_paid A.B.a k')|>.2 _ (A.B.valid.pays k')|>.1; rw [←beta_eq A.B.valid] at hR1
    have hy: terr G d+1 ≤ Pressure.radiusB y:= hR1.tempo
    have hX: terr G d+1 ≤ l*(A.B.a.budget (k'+1)).B:= hy.trans (Nat.le_mul_of_pos_left (radiusB y) hx'); let ZZ1:= (Issue.trail P).rep (k'+1) n (k'+1)
    have hs:ZZ1.p=A.B.a.budget (k'+1):=(P.choice.represents _ _ _ le_rfl).vac
    have hq: ∀ i,Hx.angle 0 0≤ Hx.angle 0 i:=by
          intro i; induction i with
          | zero=> exact le_rfl
          | succ i ih=> exact ih.trans (hr.born.pour 0 i)
    have he' : 2*(2*(terr G d+1))<(A.B.a.S.side (k'+1) n).val:=by have he:= Harmonics.corridor hr (k'+1) n;change terr G d+1≤ l*(Pressure.radiusB (A.B.a.clock.hatBeta (k'+1))) at hX; omega
    have hQ:= Spool.cakeB W ZZ1 d c K (Hx.angle 0) (Harmonics.tentN («N»:=k'+1) (n:=n) U d) χ ι₀ he (hκ' ▸ hz') (fun i _=>hz.trans (Nat.succ_le_succ (hq i))) hR1 he' (P.choice.represents (k'+1) n (k'+1) le_rfl|>.good) (Extra.Histories.forcedPos _ _) (show Real.sqrt (A.B.a.clock.forcedAllowance (k'+1))=Urns.divisor y from ?_) (by rw [hs];exact ⟨Rain.jersey (A:=A) (m:=k'+1)|>.2.1,Rain.jersey (A:=A) (m:=k'+1)|>.1,Rain.jersey (A:=A) (m:=k'+1)|>.2.2.1⟩) (congr_arg BudgetPoint.B hs) (congr_arg BudgetPoint.threshold hs) Wz I' k hv ht hq' hP _ hX -- order. Rain.jersey. _ limits.
    swap
    · apply Blush.glyph_eq
    obtain ⟨hf₁,hU,hT,hp₁,hV⟩:= hQ
    refine ⟨⟨hf₁,?_,?_,hV⟩,hU,hp₁⟩
    · rw [Harmonics.limitT,if_pos rfl,params_eq A.B.valid]; exact hT
    let r:= (fareK (n:=(A.B.a.S.side (k'+1) n)) (((Issue.trail P).rep (k'+1) n (k'+1)).p) Wz k I' 0 1) • (F0).e0; change (F0).coeffSize (r-r) ≤ _
    rw [sub_self, show (F0).coeffSize 0=0 from (by simp [Labels.Frame.coeffSize])]; exact pow_nonneg (inv_nonneg.mpr (zero_le_one.trans hR1.β)) _
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
