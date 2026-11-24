import YM.LocalLTE.Sail.Dispatcher
/-! # Actual explicit birth proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Sail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n m:ℕ}(V:∀ d,Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
    (r0:ℕ→ℕ)(hV:∀ d,d+3 ≤ (Issue.trail P).levels.clock.J (r0 d))
open Spiral Pressure ConnectedActivityE6
variable {M p0 r q TT K P0 :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)(hp: Market M K P0 p0 TT l G ζ A.delay)
variable {I:Type} [DecidableEq I][Fintype I]
    (B:Marker.Census I)(Y:Batch (Issue.trail P) N n I)(v₀:I)
    (h:Y.Roles V m W r0 K)
variable {i:ℕ}
set_option quotPrecheck false
local notation "B₀"=> P.history N n N
local notation "V'"=> (Issue.trail P).rep N n N
open Guard Accent
set_option quotPrecheck false
local notation "F"=> (Y.requested V N)
local notation "Z"=> (fun j=> Sail.zone H N n (Y.voice j) (Y.motion j) (fun i=>Y.origin i j))
local notation "X'"=> (fun j=> window H N n (Y.motion j) (fun i=>Y.origin i j) (Y.demand j))
local notation "K'"=> U.kube N N n (le_refl _)
local notation "kN"=> Sail.captain B V' Z
-- all queries d-axis tuned independently.
structure Registers (d:ℕ)(t:ℕ):Prop where
   summit : (V d).tone N=Guard.summit ((Labels.frames G).level d) (localSection G d) H N n (Keeper.sufficient ((Harmonics.mission U).born N n)) (Keeper.blank ((Harmonics.mission U).born N n)) d
   contract : Sung (localSection G d) H N n (hol G) W t (V d)
   pattern (i:ℕ) (hi:t≤ i) (hm:i<N): LocalLTE.Vinca.Arranged H N n (hol G) i ((V d).tone (i+1)) ((V d).tone i) (U.lays d N n i hm) (U.kube N (i+1) n hm)
   motion i : t ≤ i→ i ≤ N → Chorus H N n i ((V d).tone i)
variable (hR:∀ d, r0 d ≤ N → Registers U V d (r0 d))
-- Appendix at BIRTH, cost in full exponent especially. pass at ALL.
noncomputable def commence : Appendix B ((Issue.trail P).rep N n N):= let q:= Sail.frontier B V' (Y.origin N) K' v₀ kN; ⟨0,kN,q,Sail.priorP B V' (Y.origin N) K' v₀,q⟩
local notation "x"=> A.B.a.clock.hatBeta i
local notation "y"=> A.B.a.clock.hatBeta N
local notation "E"=> commence U B Y v₀
variable (π:Y.steering N) -- no unused.V in E
local notation "tt"=> (allocationK y ζ)
local notation "u"=> Real.sqrt (A.B.a.clock.forcedAllowance N)
-- prove w arbitrary ≤1.Endpoint also startup weight ONE with true budgets g^... same. Orientation all Mark canopy.
include hp h hR hV hr
lemma born_precision (hi:i+1=N)(hm:m≤ i) (w:I→ℝ)(hw:∀ i,0<w i)(hq:∀ i,w i ≤ 1) : Appendix.Prepared B V' E (Y.origin N) F (fun v=> (Y.named V π v).forced) (Batch.raw Y B) ∧ Appendix.Budget B V' E w 0 0 tt 0 u ∧ ∀ j l κ,Port.Shine B ((E).model) j l κ:=by
   let J:= A.B.a.clock.J (i+1); let I':= A.B.a.clock.J i; let R':= V'; let t:= marksExpense G I' y; let v:= marksVolume G I'; have he: i<N:= hi ▸ i.lt_succ_self
   have he' (k): r0 (Y.demand k)≤ i:= (h.phase.registered k).trans hm
   have heZ:= step_paid A.B.a i; have hx:y= betaF G x (D.L J):= (congr_arg _ hi).symm.trans (beta_eq A.B.valid i)
   have hP : R'.p=A.B.a.budget N:= (P.choice.represents _ _ _ le_rfl).vac
   have ht' :1≤ y:= (A.B.a.fits.delayed N).le; have ht:0≤ t:=by unfold t marksExpense; exact Finset.sum_nonneg fun j _=> mul_nonneg (zero_le_one.trans (Doors.cameras_ge G j)) (pow_nonneg (zero_le_one.trans ht') _)
   have hd k: Y.demand k ≤ I':= ((Nat.le_add_right (Y.demand k) 3).trans ((hV _).trans (A.B.a.fits.mono (he' k))))
   have hmin(k):minSide G (Y.demand k) ≤ ((Issue.trail P).levels.budget N).B:=by
       obtain ⟨_,hv,_⟩:= hr.provision.limits J I' heZ x (A.B.valid.pays i)|>.2 _ (hd k); rw [←hx] at hv; exact hv
   have hK k:= Sail.rays_paid H N n (Y.voice k) (Y.motion k) (fun i=>Y.origin i k) (V (Y.demand k)) (Keeper.sufficient ((Harmonics.mission U).born N n)) (Keeper.blank ((Harmonics.mission U).born N n)) P.choice ((hR _ ((he' k).trans he.le)).summit) (h.text k) (h.phase.marks k) (π k) (hmin k)
   have hr(k):Attainment R'.p (Y.origin N k) (Z k) (Real.exp (R'.p.supportExponent+2)*t):= stackFee (hK k|>.2.2.1) (mul_le_mul_of_nonneg_left (expense_ge G I' _ _ (hd k) (zero_le_one.trans ht')) (Real.exp_nonneg _))
   have ht0 : Garnish R'.p (Y.origin N) (Z) w R'.p.supportExponent (Real.exp (R'.p.supportExponent+2)*t):= Accent.cloth hr (fun i=> mul_le_of_le_one_left (mul_nonneg (Real.exp_nonneg _) ht) (hq i)) (fun i=> (hw i).le)
   let Zx(v):= (Y.named V π v).forced; let Vx:= U.kube N N n le_rfl
   have hvX:= (P.choice.represents N n N le_rfl).good.labels
   let X0:= (E); have hb(i U'): (R'.eval U':ℂ)* Y.wavelengths i U'= Accent.coin R' (F i) (Zx i) U':= Sail.prim_ray H N n (Y.voice i) (Y.motion i) (fun i' =>Y.origin i' i) (Y.label V i) P.choice (π i) (h.text i).head U'
   have hℓ:= Sail.restart B R' (Y.origin N) Y.wavelengths Z ht0 hvX (fun v=> (Y.financed V π h (hm.trans he.le) le_rfl v).2) (fun i=>(hK i).1.symm) hb (fun U=> (Tour.bright H P.choice _ _ _ le_rfl U).ne')
   let C:= (Y.raw B); let q:= Z
   have hx': R'.p.supportExponent=(X.p.profile J).supportExponent:=by rw [hP]; unfold J; rw [hi,← params_eq A.B.valid N]; rfl
   have hh : Towed w Prod.fst (kN) R'.p.B R'.p.supportExponent (tt * u):=by
       have hQ:= (hp.terms J I' heZ x (A.B.valid.pays i)).1; rw [←hx] at hQ
       apply Towed.shrink (Sail.alpine B R' q X' t (fun k=> (hK k).2.1) (fun i V=> ((hK i).2.2.2.1 V).trans (expense_ge G _ _ _ (hd i) (zero_le_one.trans ht'))) h.phase.lines w hw hq hvX (fun i=> ((hK i).2.2.2.2.1).trans (volume_ge G I' _ (hd i))) ht (fun i=>?_)) le_rfl ?_ hw
       rw [← hx'] at hQ; exact hQ
       rw [hP]; exact ((hK i).2.2.2.2.2).trans (show 1≤ marksVolume G I' from Nat.le_add_right ..)
   have hb0:0< (u):= Real.sqrt_pos.mpr (forcedPos ..)
   obtain ⟨hA,hs,hΩ,hQ,hβ,hΦ,hX,hY,hO,hS,hT⟩:= hull_receipts B R' _ Vx v₀ kN (fun i=>(hℓ.1.flag i).1) (fun i=>(hℓ.1.flag i).2) hh hw hb0 -- order? K before v₀
   refine ⟨Appendix.preiss B V' E (Y.origin N) F Zx (Y.raw B) hQ hA hQ rfl rfl hΩ ⟨fun i hx=> False.elim (hx rfl),hT⟩ (fun i=>?_) hY hℓ.1 (show Y.raw B=Accent.birth B R' Y.wavelengths from rfl) hℓ.2 (fun j t=>?_),⟨hβ,hs,hβ⟩,hΦ⟩
   · erw [show (∑ i_1 : Support (A.B.a.S.side N n), (E|>.H) i_1 i)=0 from Finset.sum_const_zero] -- maybe X0.H in situ
     exact hX _
   exact (Accent.boot B _ _ _ _).trans (hb j t)
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
