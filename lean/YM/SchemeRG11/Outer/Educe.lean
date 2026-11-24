import YM.SchemeRG11.Outer.Basin
/-! Separated geometry along mark paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric Set
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long Air North Wolt Sew
open scoped Classical Pointwise
variable {I:Type*} [DecidableEq I]{T:Align.Itinerary} {R:ℝ}
abbrev Landmarks(I:Type*):= I→ℕ → Cover
def Spaced (R:ℝ)(v:I→E4)(s:Finset I):Prop:=∀ i∈s,∀ j∈s,i≠j→4*R<‖v i-v j‖
omit [DecidableEq I] in
lemma Spaced.distinct {v:I→E4}{s:Finset I}(h:Spaced R v s)(he:R>0) (i:I)(hi:i∈s)(j:I)(hj:j∈s)(e:i≠j): v i≠ v j:=by have ht:=h _ hi _ hj e; contrapose! ht; rw [ht,sub_self,norm_zero]; linarith
abbrev Footpath (T:Align.Itinerary)(t:Landmarks I)(s:Finset I)(z:I→E4):Prop:=∀i∈s,Along T (t i) (z i)
variable (B:Window)(s:Finset I) (t:Landmarks I) {z:I→E4}
def rest (T: Itinerary)(B: Window)(s:Finset I)(t:Landmarks I): Slate:=fun i p=> 1-∑ k∈s,cove T B i (p-t k i)
omit [DecidableEq I] in
lemma overlap(h:Footpath T t s z)(e:Spaced R z s)(hp:B.rOut<R):∀ᶠ i in atTop,∀x:Cover,∀ j∈s, ‖incVec (T.gap i) (x-t j i)‖≤ B.rOut → ∀ k∈s,k≠j → cove T B i (x-t k i)=0:=by
 -- strict
 have ht(j:I)(hj:j∈s)(k:I)(hk:k∈s)(he:k≠j):∀ᶠ i in atTop,2*R< ‖incVec (T.gap i) (t j i-t k i)‖:=by
    have he':0<R:= (B.rIn_pos.trans (B.rIn_lt_rOut)).trans hp
    exact (Tendsto.norm ((h j hj).sub (h k hk))).eventually (lt_mem_nhds (by linarith only [e j hj k hk he.symm,he']))
 have hh(j:I)(hj:j∈s)(k:I)(hk:k∈s):∀ᶠ i in atTop,k≠j→2*R< ‖incVec (T.gap i) (t j i-t k i)‖:=by
   by_cases he:k≠j; · exact (ht j hj k hk he).mono fun i hi _=>hi
   simp [he]
 filter_upwards [eventually_all_finset s|>.mpr (fun j hj=>(eventually_all_finset s).mpr (fun k hk=>hh _ hj _ hk))] with i H x j hj hv k hk he
 specialize H j hj k hk he
 apply B.zero_of_le_dist; rw [dist_zero_right]; let h:= T.gap i
 rw [show t j i-t k i=(x-t k i)-(x-t j i) from by abel,inc_sub] at H; exact le_of_not_gt (fun w=>by linarith [norm_sub_le (incVec h (x-t k i)) (incVec h (x-t j i))])
omit [DecidableEq I] in
lemma away_h (h:Footpath T t s z)(e:Spaced R z s)(hp:B.rOut<R):∀ᶠ i in atTop,∀x:Cover,∀ j∈s, Near T (B.rIn/2) i (x-t j i)→ rest T B s t i x=0:=by
 filter_upwards [overlap B s t h e hp] with i H x j hj hx
 have he:‖incVec (T.gap i) (x-t j i)‖ ≤ B.rIn:= (cord T i _).trans (by linarith only [show _≤ _ from (hx : baseU T _ _ ≤ _)])
 unfold rest; rw [Finset.sum_eq_single_of_mem j hj (fun k hk h=> H x _ hj (he.trans B.rIn_lt_rOut.le) _ hk h)]
 rw [cove,B.one_of_mem_closedBall (mem_closedBall.mpr (by rw [dist_zero_right]; exact he)),sub_self]
omit [DecidableEq I] in
lemma far_cove (X:ℕ → Cover)(h:Footpath T t s z)(e:Spaced R z s)(hp:B.rOut<R)(j:I)(hj:j∈s)(hx:Along T X (z j)):∀ᶠ i in atTop,rest T B s t i (X i)=0:=by
 have he:=Tendsto.norm (hx.sub (h j hj)); rw [sub_self,norm_zero] at he
 filter_upwards [away_h B s t h e hp, (he.add T.cutoff).eventually (gt_mem_nhds (show 0+(0:ℝ)< B.rIn/2 by simpa only [zero_add] using half_pos B.rIn_pos))] with i hi hv -- check
 exact hi _ j hj ((allowNear ..).trans hv.le)
omit [DecidableEq I] in
lemma far_finish (X:ℕ → Cover){y:E4}(h:Footpath T t s z)(hx:Along T X y):Finishes (fun i=>rest T B s t i (X i)):=by
 unfold rest; apply (Finishes.const 1).sub (Finishes.sum _ _ ?_)
 intro j hj; exact ⟨_, B.continuous.continuousAt.tendsto.comp (hx.sub (h _ hj):Tendsto _ atTop _)⟩
omit [DecidableEq I] in
lemma rest_pow (T:Align.Itinerary): (fun v:Crawl=>rest T B s t v.1 v.2)∈Funds (S:=fun _ _=>True):=by
 unfold rest; apply (Funds _).toSubmodule.sub_mem (x:=fun _=>1) (y:=fun i=>∑ j∈s,cove T B i.1 (i.2-t j i.1)) (Funds _).one_mem
 let S:=Funds (fun _ _=>True)
 let f(j)(v:Crawl):=cove T B v.1 (v.2-t j v.1)
 have he(j:I):f j∈S:=by obtain ⟨C,hC,H⟩:=(Long.choice T B).wall; exact ⟨C,hC,H.mono fun i hi x _=>by unfold f; simpa only [zpow_zero,mul_one] using hi (x-t j i) trivial⟩
 convert! S.sum_mem (t:=s) (f:=f) (fun i _=>he i) using 1; funext j; rw [Finset.sum_apply]
lemma sidecar {y:E4}{x:ℕ → Cover}(h:Along T x y) : ∃ C>0,∀ᶠ i in atTop, baseU T i (x i) ≤ C:=by
 refine ⟨‖y‖+2,by positivity,?_⟩; filter_upwards [(Tendsto.norm h).eventually (gt_mem_nhds (lt_add_one ‖y‖)), T.cutoff.eventually (ge_mem_nhds zero_lt_one)] with i hi he; exact (allowNear ..).trans (by linarith)
lemma abs_z (T:Align.Itinerary)(i:ℕ)(x y:Cover):baseU T i x≤ baseU T i (x-y)+baseU T i y:=by
 unfold baseU; rw [←mul_add]; apply mul_le_mul_of_nonneg_left _ (T.positive i).le; simpa only [sub_add_cancel] using mantle (x-y) y
end YM.SchemeRG11.Dock
