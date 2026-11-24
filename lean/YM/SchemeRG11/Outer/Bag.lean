import YM.SchemeRG11.Outer.Cask
/-! Lift infinite shell. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Dock
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt Sew
open scoped Classical Pointwise
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}
local notation "D₁"=> Atoll.land G
omit [DecidableEq I] in
lemma luggage(s:Finset I)(p:I→ vellum G)(t:I → Cover)(i j:Axis):Summable (turnup s p t i j):=by
 obtain ⟨C,hC,H⟩:= Acorn.cargo (G:=G) s p i j
 let m:=Finset.univ.sup (fun i=> Catch.diam (t i)); exact (H t m (fun i=> Finset.le_sup (s:=Finset.univ) (f:=fun i:I=> Catch.diam (t i)) (Finset.mem_univ i)) (4*(m+2)) le_rfl).1
variable {T: Align.Itinerary} {z:I→E4} (s:Finset I)(t:Landmarks I)(p:I→ pLabel G)(B:Window)
omit [DecidableEq I] in
lemma dashPay(j k:Axis)(T:Align.Itinerary)(i:ℕ): Summable (directV s t p j k (T:=T) i):= (luggage ..).mul_left _ -- check inferred
omit [DecidableEq I] in
lemma peered(i j:Axis)(T: Itinerary)(k:ℕ) : Summable (external s t p B i j T k):=by
 have he(r:ℕ)(x:Cover):|cove T B r x| ≤ 1:= (abs_of_nonneg B.nonneg) ▸ B.le_one
 let f := external s t p B i j T k
 let g:= directV s t p i j (T:=T) k
 let z:= (s.card:ℝ)+1
 have hp:= (Summable.norm (dashPay s t p i j T k)).mul_left z
 apply Summable.of_norm
 refine hp.of_nonneg_of_le (fun i=> norm_nonneg _) (fun x=>?_) -- sums
 change |rest T B s t k x * g x| ≤ z*|g x|; rw [abs_mul]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg (g x)); unfold rest; apply le_trans (abs_sub _ _)
 unfold z; rw [abs_one,add_comm (s.card:ℝ)]; apply add_le_add_right
 calc _ ≤ _:=Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _ ∈ s,(1:ℝ):= Finset.sum_le_sum fun _ _=> he k _
      _ = _:=by simp
lemma hilly{R:ℝ}(h:Footpath T t s z)(e:Spaced R z s)(hp:B.rOut<R)(i j:Axis): Finishes (fun k=>∑' x:Cover,rest T B s t k x *turnup s (fun l=>castZero (T.gap k) (p l)) (fun l=>t l k) i j x):=by
 have hz:= seaCost (T:=T) (peered s t p B i j T) (ship s t p B h e hp i j) (fun x=> ready s t p B i j _ x h e hp (follows x)); apply hz.same; filter_upwards with k; rw [← tsum_mul_left]; apply tsum_congr; intro x
 unfold external; simp only [Pi.mul_apply,directV]; unfold turnup; have H:=T.positive k; field_simp -- check
end YM.SchemeRG11.Dock
