import YM.OPE.Script.Wagon
import YM.OPE.Therm.Law
/-!
# Stroboscope. Simultaneous local probes at observer station k in addition

Cells used once, but many marks may be in a cell. Requires exact compatibility
of the cutoff kernels on the pushed **test** cone too. `Sings` doesn't carry
information for subsequent adding of a spectator at k; since measurements all
use one hot epoch (cannot attach a new lens here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Set
open MergeProof Accent Ribbons ManyCopies Patrol Push Marker Source Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open GridApprox Cells Extra.Multi GridApprox.Nil MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{I J : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {A:History G}
set_option quotPrecheck false
local notation "K" => Finset
variable {N p i j k : ℕ} {s: i≤N} {F:I→ Config G (A.S.side N p)→ℂ} {Q:Config G (A.S.side i p)→ Poly (Bud I)}
local notation "R" => A.rep N p
local notation "f" => A.S.side N p
local notation "c" => A.S.side i p
local notation "T" => tilesAt A.S p
local notation "β" => A.β N p N
local notation "∆" => (Wilson.partition G f β:ℂ)
structure Sings (A:History G)(N p i:ℕ)(Q:Config G (A.S.side i p)→ Poly (Bud I))(F:I→ Config G (A.S.side N p)→ℂ):Prop where
   budget: Integrable Q (prior G _)
   cost j: Envelope (F j)
   budgets (a : Finset I): (∫ W,(Q W).part (Fibers.mark a)∂prior G _)=(Wilson.partition G (A.S.side N p) (A.β N p N):ℂ)*moment (A.β N p N) (fineJob F a)
namespace Sings
lemma focused (hp:Sings A N p i Q F) (he:k ≤ i): Sings A N p k (gust A N p i Q k he) F:=by
    refine ⟨gust_live A N p _ _ hp.budget he,hp.cost,fun a=>?_⟩; rw [← hp.budgets]; have ht:= gust_choose A N p Q hp.budget he (Fibers.mark a); refine (congr_arg (fun f'=> ∫ W,f' W∂prior G _) ht).trans (pushTo_integral A N p he _ (Script.part_int hp.budget _))
lemma gathered (L:Fibers I J)(hp:Sings A N p i Q F): Sings A N p i (fun U=>Fibers.reap L (Q U)) (fun i=>fineJob F (L.contents i)):=by
   refine ⟨(L.reap.restrictScalars ℝ).integrable_comp hp.budget,fun j=> Envelope.prodC _ _ (fun i _=>hp.cost _), ?_⟩; intro a; let s:= Fibers.mark a; let B:= (L.plena s); rw [show fineJob (fun i=>fineJob F (L.contents i)) a=fineJob F B.val from funext fun U=> (L.prod_plena s (fun i=>F i U)).symm]; exact hp.budgets B.val
lemma jargon {F:I→ Config G (A.S.side N p)→ℂ}(ht:i≤N)(X:I→ Config G c→ℂ) (hx:∀ (a:Finset I), backTo A N p ht (fineJob X a)=fineJob (fun i=>backTo A N p ht (X i)) a)(hw : ∀ i, Envelope (X i))(hV:∀ i,Envelope (F i))(hA:A.Selected)(hq:Integrable (birth (Bud I) (R N) F) (prior G _)) : Sings A N p i (couple (gust A N p N (birth (Bud I) (R N) F) i ht) X) (F+(fun i=>backTo A N p ht (X i))):= by
    let w(x:Finset I):= Fibers.mark x; let F':= birth (Bud I) (R N) F; let Q':=gust A N p N F' i ht; let Z:=couple Q' X; let P' s U:=(F' U).part (w s); let H(j):= backTo A N p ht (X j); have hy(j): Envelope (H j):= backTo_env A N p ht (hw j); let T' a U:= fineJob H a U; let Y'(j):=F j+H j; have hf:∀ j,Envelope (Y' j):=fun j=>(hV j).addC (hy j)
    let K' (a b: Finset I) (V:Config G c):= (Q' V).part (w (a\b))*fineJob X b V; have hh(s) := gust_choose A N p F' hq ht (w s); let q(x) (V:Config G c):= (Q' V).part (w x); let U(s : Finset I) (x:Config G f):ℂ:= (bare β x:ℂ)*fineJob F s x
    have hz s u : P' s u=U s u:=by unfold P' F' U birth; rw [Poly.part_smul,Mach, Extra.Trajectories.pass_fire,(hA.starts ..).2]; rfl
    have hZ (a): (fun U=> (Z U).part (w a))=fun V=>∑ b∈a.powerset,K' a b V := by
       funext x; unfold Z K' Accent.couple Mach; rw [Extra.Trajectories.pass_sum univ _ (fun i _=> singleton_nonempty _)]; exact GridApprox.Birth.array_read (Q' x) a (fun i=>X i x)
    have hU (x y): Integrable (K' x y) (prior G _):=by have hx:= gust_live A N p N F' hq ht; have ht : Envelope (fineJob X y):= Envelope.prodC _ _ (fun i _=>hw i); exact (Script.part_int hx (w (x \ y))).mul_bdd ht.meas.aestronglyMeasurable (Eventually.of_forall ht.cost.choose_spec)
    have h₀(s t : Finset I): (∫ U,K' s t U∂prior G _) = ∫ W,P' (s\t) W * T' t W∂prior G _:=by
       have hp := pushTo_dual A N p ht (show Envelope (fineJob X t) from Envelope.prodC _ _ (fun i _=>hw i)) _ (Script.part_int hq (w (s\t))); rw [← hh _,hx] at hp; exact hp
    refine ⟨integrable_pi_iff.mpr (fun i=>?_), hf,fun a=>?_⟩
    · change Integrable (fun U=> (Z U).part (w i.val)) _; rw [hZ]; exact integrable_finsetSum _ (fun i _=>hU _ _)
    change (∫ W,(Z W).part (w a) ∂prior G _) = ∆* moment β (fineJob Y' a)
    have hR: Envelope (fineJob Y' a):= Envelope.prodC _ _ (fun i _=> hf i)
    simp_rw [show ∀ W,(Z W).part (w a)=_ from fun W=> congr_fun (hZ a) W]; rw [integral_finsetSum («f»:=K' a) _ (fun i _=> hU a i),moment_formula β _ (hR.integrableC _),mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')]
    simp_rw [h₀]; rw [← integral_finsetSum]; swap; · intro l _; have he:= Script.part_int hq (w (a\l)); have hz': Envelope (T' l):=Envelope.prodC l H (fun i _=>hy i); exact he.mul_bdd hz'.meas.aestronglyMeasurable (Eventually.of_forall hz'.cost.choose_spec)
    apply integral_congr_ae (Eventually.of_forall fun v=>?_); simp only [hz]; have ht(v): fineJob Y' a v=∑ b∈a.powerset,T' b v*fineJob F (a\b) v
      := by
          unfold Y' fineJob; simp only [Pi.add_apply]; conv_lhs=> arg 2; ext x; rw [add_comm]
          exact Finset.prod_add (fun i=> H i v) (fun i=> F i v) a
    rw [ht,mul_sum]; refine Finset.sum_congr rfl (fun l _=>?_); unfold U; ring
end Sings
end YM.OPE.Strobe

