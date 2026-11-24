import YM.OPE.Compatible.Grout.Boost
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
import YM.Next.RANK.Swath
/-!
# Coarse kernel query anchored pieces and reward long witnesses
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m d M: ℕ} {W a r t σ E Λ μ x κ w C s ε D: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
local notation "Point_"=> Config G f → ℝ
structure Deckery (R:Rep G f)(ι:Type) where
 len:ι→ℕ
 home: Site f→ ι→ Support f
 knot(x i):x∈home x i
 serves : Site f→ ι→ Config G f → ℝ
 full : Site f→ι→ Config G f→ℝ
structure Decked {ι:Type} (R:Rep G f)(A:Deckery R ι)(σ E C : ℝ) (w:ι→ℝ): Prop where
 cash : SumBudget (fun i=> w i*Real.exp (σ*A.len i)) E
 value x i V: ‖A.serves x i V‖≤ w i
 raw x i : LocalOn (A.home x i) (A.full x i)
 scope x i:UsesFinal R.p.threshold (A.home x i) (A.serves x i)
 gauge x i:GaugeInvariant (A.serves x i)
 measurable x i:Measurable (A.serves x i)
 matchV x i U :Healthy R.p.threshold (A.home x i) U → A.serves x i U=A.full x i U
 space x i :(R.p.B:ℝ)*(coverNumber R.p.B (A.home x i)) ≤ R.p.B*C+A.len i
variable {J:Seats F} {X: Support f} {ι:Type}[Countable ι]
namespace Deckery
variable (A:Deckery R ι)
-- omit
abbrev moon (k:Signed) (j:Site f×ι)(U:Config G f):ℝ:= A.serves j.1 j.2 (pull k 0 U)
abbrev tower (k:Signed)(j:Site f × ι) := swath k 0 (A.home j.1 j.2)
def lathe (k:Signed)(r:ℕ) (U:Config G f) := ∑' j, if r ≤ A.len (Prod.snd j) then A.moon k j U else 0
def lobe (k:Signed)(r:ℕ) (U:Config G f) := ∑' j, if A.len (Prod.snd j)<r then A.moon k j U else 0
end Deckery
namespace Decked
variable {A:Deckery R ι}{w:ι→ℝ} (h:Decked R A σ E C w)
include h
omit [Countable ι] in
lemma nonneg (i:ι):0≤w i:=(norm_nonneg _).trans (h.value 0 i 1)
omit [Countable ι] in
lemma basin {s':Signed} (hs:0≤σ) :Dominated (A.moon s'):=by
    have hn i:w i≤ _:=le_mul_of_one_le_right (h.nonneg i) (Real.one_le_exp (mul_nonneg hs (show 0≤(A.len i:ℝ) by positivity)))
    have hw :Summable w:= h.cash.2.1.of_nonneg_of_le h.nonneg hn
    exact ⟨fun i=>w i.2,(summable_prod_of_nonneg (f:=fun p:Site f ×ι=> w p.2) (fun i=>h.nonneg i.2)).2 ⟨fun _=>hw,.of_finite⟩,fun p V=>h.value ..⟩
-- computation signed frame uses EXACT lengths and masks
lemma lit_budget (s':Signed) (hh: FoldsGrip F J X)(ht:t+ε ≤ R.p.supportExponent)(hε:0<ε)(_ha:0≤t)(hs : 0<σ)(hx:2*R.p.supportExponent ≤ R.p.B*σ) (l:ℕ):
   Sable R S X t (tweak J (A.lathe s' l)) (2*(X.card*(est R.p ε*((Real.exp (R.p.supportExponent*C-σ/2*l))*E)))):=by
    let Y:= Site f×ι; let Z(j:Y):= A.tower s' j; let U(j:Y):ℝ:= if l ≤ A.len j.2 then w j.2 else 0
    let F'(j:Y) (x:Config G f):ℝ:= if l ≤ A.len j.2 then A.moon s' j x else 0; let c:= Real.exp (R.p.supportExponent*C-σ/2*l)
    have he j:Paced R (Z j) S (F' j) (U j):=by
       unfold F' U; split_ifs
       · exact ⟨final_swath s' 0 _ _ (h.scope j.1 j.2), (h.measurable ..).comp (continuous_pull ..|>.measurable), fun k _ U=>p_invar s' 0 (h.gauge _ _) k U,fun V=>h.value ..⟩
       exact ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _ _=>rfl,fun _=> norm_zero.le⟩
    let V j:RegularAddress f :=⟨affine s' 0 (Prod.fst j),Z j,mem_image_of_mem _ (A.knot ..)⟩
    have hf x : SumBudget (fun j=> if (V j).site=x then R.p.mass (Z j) (U j) else 0) (c*E):=by
       obtain ⟨y,hy⟩ := (sends s' (0:Site f)).surjective x
       have hy : affine s' 0 y=x:=hy; subst x
       let u j:= if (V j).site=affine s' 0 y then R.p.mass (Z j) (U j) else 0
       have hp(i:Y): (V i).site=affine s' 0 y↔ i.fst=y:= (sends s' (0:Site f)).injective.eq_iff
       have hI : Injective fun i:ι=> (y,i):=fun i j h=> congr_arg Prod.snd h
       have hc : SumBudget (fun i=>u (y,i)) (c*E):=by
           apply budget_mono (budget_scale (f:=fun i=> w i*Real.exp (σ*A.len i)) (Real.exp_pos _).le h.cash) (fun i=>?_) (fun i=>?_)
           · unfold u;rw [if_pos ((hp _).2 rfl)]; exact mul_nonneg (Real.exp_pos _).le (he _).safe
           unfold u U; rw [if_pos ((hp _).2 rfl)]; split
           next hz =>
             let b:= R.p.supportExponent; have hb := R.p.exponent_pos; let B:ℝ:= R.p.B; have hB:0<B:=by unfold B; exact_mod_cast R.p.B_pos
             unfold BudgetPoint.mass; rw [mul_comm (w i),←mul_assoc]; refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_ |>.trans (le_of_eq (Real.exp_add _ _))) (h.nonneg _)
             have hh : Z (y,i)= swath s' 0 (A.home y i):=rfl; rw [hh,swath_cover]; have hc:= h.space y i; have hm : b * coverNumber R.p.B (A.home y i) ≤ b*C + (σ/2)*A.len i:=by
               apply le_of_mul_le_mul_left _ hB; unfold B b; nlinarith only [mul_le_mul_of_nonneg_left hc hb.le, mul_le_mul_of_nonneg_right hx (show 0≤(A.len i:ℝ) by positivity)]
             linarith only [hm,mul_le_mul_of_nonneg_left (show (l:ℝ)≤ (A.len i:ℝ) from Nat.cast_le.mpr hz) hs.le,show b=R.p.supportExponent from rfl] -- defeq
           next=> simp only [BudgetPoint.mass,mul_zero]; exact mul_nonneg (Real.exp_pos _).le (h.cash.1 i)
       have hv := hc.2.1.hasSum
       have hm := (hI.hasSum_iff (f:=u) (fun i hi=> if_neg (fun h=> hi ⟨_,Prod.ext ((hp _|>.1 h).symm) rfl⟩))).1 hv
       refine ⟨fun i=>?_,hm.summable,hm.tsum_eq.trans_le hc.2.2⟩; change 0≤u i; unfold u; split; exact mul_nonneg (Real.exp_pos _).le (he _).safe; exact le_rfl
    refine one_collection (v:=F') hh he ?_ (perceive (u:=V) (w:=U) hε ht (fun j=>(he j).safe) hf)
    intro x; have hv:= (h.basin (s':=s') hs.le).absolute x
    exact Summable.of_norm (hv.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> by unfold F'; split; exact le_rfl;exact norm_zero.trans_le (norm_nonneg _)))
end Decked
end YM.PhysicalNext.Repeat.Aroma
