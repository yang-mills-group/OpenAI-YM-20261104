import YM.X.Haze.Press
import YM.X.Haze.Deter
/-!
# near-field aperture. compact radius arbitrary, nonempty root basin. length unit physical, Street comparisons eventually including shell change boundary.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Haze
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid
open scoped Topology ContDiff BigOperators Classical ENNReal
variable {q : ℕ+} (hq:1<q.val) {k m v:ℕ} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
structure Floor (R:ℝ) where
    s : ContDiffBump (0:E4)
    h : 4*s.rOut < R
namespace Floor
lemma make {R:ℝ}(h:0<R) : Nonempty (Floor R):=⟨⟨⟨R/16,R/8,by linarith,by linarith⟩,by dsimp;linarith⟩⟩
variable (w:Floor R)
include w in
lemma positive : 0<R:= by linarith [w.s.rOut_pos,w.h]
private lemma bounded (z:Cover)(h:w.s (spot (ε k) z)≠0): street z≤gate q (4*w.s.rOut) k:= by
    have ht: spot (ε k) z∈ Function.support w.s:= Function.mem_support.mpr h; rw [w.s.support_eq,mem_ball,dist_zero_right] at ht; rw [gate_mem _ (mul_nonneg (by norm_num) w.s.rOut_pos.le)]; linarith only [street_cost (q:=q) (k:=k) z,ht]
private lemma hasSample : (Function.support (fun z=> w.s (spot (ε k) z))).Finite:= by
    let A:= gate q (4*w.s.rOut) k; apply (Finset.finite_toSet (Lattice.box A)).subset; intro z hz; have h:= bounded w z (q:=q) (k:=k) hz; rw [Finset.mem_coe,box_iff_layers]; intro i; apply Finset.mem_Icc.mpr; have he: (z i).natAbs ≤ street z:= by unfold street; exact Finset.single_le_sum (f:=fun i:Axis=>(z i).natAbs) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)
    unfold A; omega
def maskL (q:ℕ+)(w:Floor R)(k:ℕ):Lane:= Finsupp.ofSupportFinite _ (hasSample (q:=q) (k:=k) w)
lemma masking (z:Cover): maskL q w k z = w.s (spot (ε k) z):= rfl
lemma tight (z:Cover)(h:z∈(maskL q w k).support): street z ≤ gate q R k:= by
    have he:= w.bounded (q:=q) (k:=k) z (Finsupp.mem_support_iff.mp h); refine he.trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_left w.h.le (amp_pos .. |>.le)))
lemma mask_one (z:Cover)(h:street z≤gate q w.s.rIn k): maskL q w k z= 1:= by rw [masking]; apply w.s.one_of_mem_closedBall; rw [mem_closedBall,dist_zero_right]; exact gate_range _ w.s.rIn_pos.le z h
include hq
lemma onboard : Starboard q R (fun i z=>maskL q w i z):= Eventually.of_forall (fun i z h=> w.tight z (Finsupp.mem_support_iff.mpr h))
lemma derivative_visa (l:List Axis)(T:ℝ)(ht:T≥0): Visa q T (l.length:ℤ) 0 (fun i=>Interval.grads l (fun z=>maskL q w i z)):= visa_smooth l w.s.contDiff ht hq
lemma mask_visa (T:ℝ)(ht:T≥0): Visa q T 0 0 (fun i z=> maskL q w i z):= derivative_visa hq w [] T ht
lemma becomes (z:Cover) : ∀ᶠ k:ℕ in Fℕ, maskL q w k z=1:= ((gate_asc hq w.s.rIn w.s.rIn_pos).eventually (eventually_ge_atTop (street z))).mono (fun k h=>w.mask_one z h)
lemma covers {G:Gauge}(P:Stems.Curly G) : ∀ᶠ i:ℕ in Fℕ, High (side q i) (maskL q w i) P:= by
    filter_upwards [(eventually_all_finset P.vars).mpr (fun x _=> becomes hq w x.1.1), spot_lift hq R] with k hk hp; refine ⟨hk,fun x hx y hy he=>?_⟩
    have hh (x:Hair G)(h:x.1.1∈ (maskL q w k).support) : lift (wrap (side q k) x.1.1)=x.1.1:= hp _ (gate_range _ w.positive.le _ (w.tight _ h)); simp only [place,west,Prod.mk.injEq,add_zero] at he;
    have heq:= (hh x (Finsupp.mem_support_iff.mpr (by rw [hk x hx]; norm_num))).symm.trans ((congr_arg Lattice.lift he.1.1).trans (hh y ((Finset.mem_product.mp (Finset.mem_product.mp hy).1).1))); exact Prod.ext (Prod.ext heq he.1.2) he.2
variable (a:Axis)
lemma changed_ship : Starboard q R (fun i z=>changed (maskL q w i) a z):= by
    have h:= w.h; filter_upwards [gate_shift hq _ _ h (mul_nonneg (by norm_num) w.s.rOut_pos.le) (step a)] with i hi z hz; by_cases hx:z∈ (maskL q w i).support; exact w.tight z hx
    rw [changed_point, Finsupp.notMem_support_iff.mp hx,sub_zero] at hz; simpa only [sub_add_cancel] using hi (z-step a) (w.bounded (q:=q) (k:=i) _ hz)
lemma changed_out : ∀ᶠ i:ℕ in Fℕ, ∀ z:Cover, street z≤gate q (w.s.rIn/2) i → changed (maskL q w i) a z=0:= by
    have h:= w.s.rIn_pos; filter_upwards [gate_shift hq _ _ (show w.s.rIn/2<w.s.rIn by linarith) (by positivity) (-step a)] with i hi z hz; rw [changed_point,w.mask_one,w.mask_one,sub_self] -- offset argument order reversed
    · exact hz.trans (Nat.floor_le_floor (mul_le_mul_of_nonneg_left (by linarith : w.s.rIn/2≤w.s.rIn) (amp_pos ..|>.le)))
    rw [sub_eq_add_neg];exact hi _ hz
lemma changed_visa : Visa q R 1 0 (fun i z=>changed (maskL q w i) a z):= by
    let f : Mist ℝ:= (fun i=> Interval.grads [a] (fun z=>maskL q w i z)); have h : Visa q (R+1) 1 0 f:= derivative_visa hq w [a] (R+1) (show R+1≥0 from by linarith [w.positive]) -- nat cast
    have ha(i:ℕ)(z:Cover): changed (maskL q w i) a z= - f i (z-step a):= by change _ = - (maskL q w i (z-step a+step a) - maskL q w i (z-step a)); rw [sub_add_cancel,changed_point]; ring
    simp_rw [ha]; apply Visa.neg -- shape
    obtain ⟨C,hc,he⟩:= h.who; refine ⟨⟨C,hc,?_⟩,fun x hx hr z hz=>?_⟩
    · filter_upwards [he,gate_shift hq _ _ (lt_add_one R) w.positive.le (-step a)] with i hi hh z hz; apply le_trans (hi (z-step a) (by rw [sub_eq_add_neg];exact hh _ hz)); simp [price]
    have hp:= (plot.sub hz (plot.constant hq (step a))); rw [sub_zero] at hp; exact h.whereL x hx (le_trans hr (lt_add_one R).le) _ hp -- shape
end Floor
end YM.PositionX.Haze
