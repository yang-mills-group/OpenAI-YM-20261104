import YM.LocalLTE.Concert.Glaze
import YM.Extra.MULTISOURCE_TRAJECTORIES.Stubs
import YM.Progress.DIRECTED_RECIPE.EvalBounds
/-! # Contact bound using *no extra support reserve*.

Price is polynomial in the marked region costs; OK even if mark cables not small.
Only a weak exponential in its total (marked) **volume times the OLD K cap**.
Can afford pockets even when close to UV. Critical: every formed K touches!
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side} (P:Rep G n)
variable {V α :Type}[DecidableEq V]{R:Census V} (X:Layers P R α)
local notation "W"=> X.Component
local notation "K"=> P.activities.K
-- every old K in a component touches a mask. (an immediate neighbor on a path to right label).
lemma necessity {x:W} {i :ℕ}(hi:i∈x.val.toLeft): ∃ j∈ x.val.toRight,¬Disjoint ((P.activities.forced i).support) (X.region j):=by
    obtain ⟨a,ha⟩:=x.property.mark; have hf:=x.property.join.2 _ (mem_toLeft.mp hi) _ (mem_toRight.mp ha)
    by_contra hJ
    have loop(l) (hl: Relation.ReflTransGen (Ac.bonds X.area x.val) (.inl i) l ):l=Sum.inl i:=by
       induction hl with
       | refl=> rfl
       | @tail e k h h' IH =>
          subst e; obtain ⟨-,hb,y,he,hf⟩:=h'; cases k with
          | inl k=> by_contra h; exact disjoint_left.mp (x.property.sep hi (mem_toLeft.mpr hb) (by intro he; subst i; exact h rfl)) he hf -- check
          | inr k=> exact (hJ ⟨k,mem_toRight.mpr hb,not_disjoint_iff.mpr ⟨y,he,hf⟩⟩).elim
    cases loop _ hf
-- Basic estimate. No marker factor needed here.X.g.You can charge EVEN weighed r high.u
variable [Fintype α]
def coastK:=(univ:(Finset α)).biUnion X.region
local notation "W₁"=> coastK P X
-- old payment witnesses.k.H.Post
variable (k: ℕ→ ℝ) (d: α→ℝ)
variable {u y a κ:ℝ} (h:∀ i U,‖P.activities.K i U‖ ≤ k i) (he:∀ i V, ‖X.residual i V‖ ≤ d i)
variable (hq : ∀ x, SumBudget (fun i=> if x∈ ((P.activities.forced i).support) then P.p.mass (P.activities.forced i).support (k i) else 0) u)
-- type syntax K used var commands? quot yes
variable (r:V→ℝ)(hr:∀ i,0<r i)
set_option quotPrecheck false
local notation "bk" i=> P.p.mass ((P.activities.forced i).support) (k i)
include h hq
-- estimate.Shows Exp.
def chargeFog (u:ℝ):= Real.exp ((coastK P X).card*u)-1
lemma budget_fog : SumBudget (fun i=> if ¬Disjoint ((P.activities.forced i).support) (coastK P X) then (bk i) else 0) ((coastK P X).card*u):=by
    let C (x:Site n)(i:ℕ):= if x∈ (P.activities.forced i).support then (bk i) else 0
    have ht:= budget_over W₁ C (fun _=>u) (fun x _=> hq x); simp only [sum_const, nsmul_eq_mul] at ht
    refine budget_mono ht (fun i=> ?_) (fun i=>?_)
    · split; exact mul_nonneg (Real.exp_nonneg _) ((norm_nonneg _).trans (h i 1)); exact le_rfl
    split; next hv=> obtain ⟨x,hx,hj⟩:=not_disjoint_iff.mp hv; exact ((show C x i= _ from if_pos hx).symm.le).trans (single_le_sum (fun b _=> show 0 ≤ C b i from (hq b).1 i) hj)
    exact ht.1 _
-- W' tag toll. no Root.Volume.All terms.
def waft (k:ℕ→ℝ) (d:α→ℝ) (c:X.Component):= ∏ l∈ c.val, Sum.elim k d l
local notation "WΚ"=>waft P X k d
def chargeMark:= ∏ i:α,(1+Poly.toll r (X.tag i)*P.p.mass (X.region i) (d i))
local notation "C'"=> chargeMark P X d r
include he hr
lemma brightBudget : SumBudget (fun c:X.Component=> Poly.toll r (X.stamp c)* P.p.mass (X.skin c.val) (waft P X k d c)) ((chargeFog P X u)*chargeMark P X d r):=by
    let K'(i:ℕ):=(bk i); let κ(i:ℕ):=if ¬Disjoint ((P.activities.forced i).support) (coastK P X) then K' i else 0
    let D (i:α):= P.p.mass (X.region i) (d i); let M (i:α):= Poly.toll r (X.tag i); let J i:= M i*D i
    have hu(i:ℕ⊕α):0≤Sum.elim k d i :=Sum.rec (fun i=> (norm_nonneg _).trans (h i 1)) (fun i=> (norm_nonneg _).trans (he i 1)) i
    have h₁ (i): 0 ≤ J i:= mul_nonneg (Poly.worth hr _).le (mul_nonneg (Real.exp_nonneg _) (hu (.inr i)))
    have hh:SumBudget (fun s:Finset ℕ=> (∏ i∈s,κ i)- ∏ _∈s, (0:ℝ)) (chargeFog P X u):=by simpa only [zero_add,Real.exp_zero,one_mul,chargeFog] using Progress.DirectedRecipe.Payment.products (show SumBudget (fun _:ℕ=>(0:ℝ)) 0 from ⟨fun _=>le_rfl,summable_zero,by simp⟩) (show SumBudget κ _ from budget_fog P X k h hq)
    letI : DecidableEq α:= Classical.decEq _
    have hs :SumBudget (fun s:Finset α=>∏ i∈s,J i) C':=by
       refine ⟨fun i=>prod_nonneg fun i _=>h₁ i,Summable.of_finite,?_⟩
       unfold chargeMark; rw [tsum_fintype,prod_one_add,Finset.powerset_univ]
    let c (s:W):= Finset.sumEquiv s.val; have hc:Injective c:= fun i j h=>Subtype.ext (Finset.sumEquiv.injective h) -- notation
    refine budget_mono (budget_pull c hc (budget_prod hh hs)) (fun c=> mul_nonneg ((Poly.worth hr _).le) (mul_nonneg (Real.exp_nonneg _) (prod_nonneg fun j _=> hu j))) (fun j=>?_)
    have hi0 (i)(hx:i∈ j.val.toLeft): ¬ Disjoint ((P.activities.forced i).support) (coastK P X):=by
       obtain ⟨z,-,hv⟩:= necessity P X (x:=j) hx; obtain ⟨j,hj,hJ⟩:=not_disjoint_iff.mp hv; exact not_disjoint_iff.mpr ⟨j,hj,mem_biUnion.mpr ⟨z,mem_univ _,hJ⟩ ⟩
    have hu' i (hx:i∈j.val.toLeft):κ i=P.p.mass ((P.activities.forced i).support) (k i):= if_pos (hi0 _ hx)
    obtain ⟨i,hT⟩:= j.property.old
    let A:= j.val.toLeft; let B:= j.val.toRight
    change Poly.toll _ _*P.p.mass _ _ ≤ ((∏ i∈A,κ i)-∏ _∈A,0)*(∏ i∈B,M i*D i); rw [prod_eq_zero (f:=fun _=>0) (show i∈A from hT) (show (0:ℝ) = 0 from rfl),sub_zero,stamp,toll_union,prod_mul_distrib]
    let f:= Sum.elim k d
    have hz : P.p.mass (X.skin j.val) (∏ i∈j.val,f i) ≤ (∏ i∈j.val, P.p.mass (X.area i) (f i)):=by
       simp only [BudgetPoint.mass, prod_mul_distrib, ← Real.exp_sum,← mul_sum]; gcongr; · exact prod_nonneg fun i _=>hu i
       · exact P.p.exponent_pos.le
       have hx : coverNumber P.p.B _ ≤ _:= Ac.cover X.area P.p.B j.property.join; exact_mod_cast hx
    nth_rw 2 [prod_sum_eq_prod_toLeft_mul_prod_toRight] at hz -- first occurrence prod? want RHS first only
    have hk:(∏ i∈A,κ i)=∏ i∈A,K' i:=prod_congr rfl hu'
    have hV (i):0≤ M i:=(Poly.worth hr _).le
    rw [mul_left_comm,hk]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> hV i); exact hz
-- no capacity needed.H.Use quote. need ctor of Band.hits directly
end YM.LocalLTE.Port
