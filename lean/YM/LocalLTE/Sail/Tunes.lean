import YM.LocalLTE.Sail.Font
/-! Stage-width cone budgets on customer digit stencils. -/
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
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Sail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n d:ℕ} (V:Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n) (f:((Labels.frames G).level d).Coeff)
    {r0:ℕ}(hv:Sung (localSection G d) (Issue.trail P) N n (hol G) W r0 V)
local notation "T₀"=> localSection G d
set_option quotPrecheck false
local notation "F"=> ((Labels.frames G).level d)
local notation "T"=> A.B.a
set_option quotPrecheck false -- above F
local notation "sz"=> fun p=> (F).coeffSize ((V.tone p).index f)
local notation "z" i=> sampleNorm (Issue.trail P) N d i
variable (he:((Labels.frames G).level d).coeffSize f ≤ 1) -- notation
variable (m:ℕ)
-- convenient collective stage constant. bounded jobs at given H.Read
noncomputable def colPay (s: RG.Supply.Sheet G) (j TT:ℕ):ℝ:= 1+∑ i∈ Finset.range (j+TT+2),(s.profile i).columns
lemma colBig (s:RG.Supply.Sheet G) (i j TT:ℕ)(h:i≤j+TT+1): (s.profile i).columns≤ colPay s j TT:=by
    have hz: i ∈ Finset.range (j+TT+2):= Finset.mem_range.mpr (by omega)
    exact (Finset.single_le_sum (f:=fun i=>(s.profile i).columns) (fun i _=> zero_le_one.trans (s.profile i).columns_ge) hz).trans (le_add_of_nonneg_left zero_le_one)
lemma col_bound (s:RG.Supply.Sheet G) (j TT:ℕ) : 1 ≤ colPay s j TT:= le_add_of_nonneg_right (Finset.sum_nonneg fun i _=> zero_le_one.trans (s.profile i).columns_ge)
noncomputable def capStone (s:RG.Supply.Sheet G)(j K:ℕ):ℝ:= (colPay s j K)^(K+1)
-- cone expense on EXACT path.
include U hv he
local notation "J'" i=> A.B.a.clock.J i
local notation "c" i=> (Issue.trail P).S.block i
local notation "X'"=> X.p
set_option quotPrecheck false
lemma cornerstone (hm:r0≤ m) (hn:m≤N) (K:ℕ)(hk:N-m≤K+1) : ∀ i, m≤ i→ i ≤ N→ ‖z i‖* (sz i) ≤ capStone X.p (J' m) K:=by
    let s:= X.p; let J:= A.B.a.clock.J; let r:= colPay s (J m) K
    have ht : 1 ≤r:= col_bound ..
    have hM(j:ℕ)(hi:m≤j): J j ≤ J m + (j-m):=by
       induction hi with
       | refl=> simp only [Nat.sub_self,add_zero,le_refl]
       | @step j hi ih=> have he:= (T).fits.stepSlow j; exact (le_trans he (by change J _+1≤ _;have ht : m≤ j:= hi;omega))
    have hx(i:ℕ)(he:m≤ i)(hi:i≤N): (A.B.a.params i).columns ≤ r:=by
       rw [params_eq A.B.valid]; refine colBig s _ _ _ (le_trans (hM _ he) ?_);omega
    suffices Hx:∀ i,m≤ i→ i≤N→ ‖z i‖* (sz i) ≤ r^(N-i) from fun i hi h'=> (Hx i hi h').trans (pow_le_pow_right₀ ht (by omega))
    intro i hi hu; induction hu using Nat.decreasingInduction with
    | self=>
       have heN : (V.tone N|>.index f)= f:= ((hv.head.heard.currents _).symm.trans (hv.head.out _))
       rw [sample_top, norm_one,one_mul,show sz N=(F).coeffSize f from congr_arg _ heN,Nat.sub_self,pow_zero]; exact he
    | of_succ i hs ih=>
       obtain ⟨h1,h₀⟩:= And.intro (hv.earned (i+1) (by omega) hs) (hv.earned i (hm.trans hi) hs.le)
       have hC := h1.cone f; rw [← h1.currents] at hC; have he:=(Work.G08.cone_step W (Issue.trail P) U.tag.clock.room U.tag.clock.bank _ _ _ _ _ _ ((hv.step i (hm.trans hi) hs).tally f) hC).2.2
       rw [h₀.currents,h1.currents] at he
       have hu := sample_step H (N:=N) (d:=d) (m:=i)
       have hy: ‖z (i+1)‖=((c i).val:ℝ)^d*‖z i‖:=by rw [hu,norm_mul,norm_pow,Complex.norm_natCast]
       have hS : ‖z i‖*(sz i) ≤ ((T).params (i+1)).columns*(‖z (i+1)‖*(sz (i+1))):=by rw [hy]; refine (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (?_); change ‖z i‖*( (A.B.a.params _).columns*_ *_ )= _; ring -- change maybe
       have hp := ih (by omega); change _ ≤ _ at hp; refine hS.trans ((mul_le_mul (hx _ (by omega) hs) hp (mul_nonneg (norm_nonneg _) (Work.G08.size_nonneg ..)) (zero_le_one.trans ht)).trans_eq ?_); nth_rw 1 [mul_comm]; exact (pow_succ ..).symm.trans (congr_arg _ (show N-(i+1)+1=N-i by omega))
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
