import YM.Frontier6.Bouquet.Truth.Apex
/-! Need not reset for offsets. Transmission in projection moments at exact
 common data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S)(A:Teller S)(T:Veins){P Q:Ensemble}(h:Q≤P)
    (w:ℕ)
variable {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y][CompleteSpace Y]
variable {Z:Type}[NormedAddCommGroup Z] [NormedSpace ℂ Z][NormedSpace ℝ Z][IsScalarTower ℝ ℂ Z][CompleteSpace Z]
lemma transformed (x:Seats P)(H:Patron S P Y)(L:Y→L[ℂ] Z)(f:Full (fiber P))(p:Trip A Q): ink K A T h x (L.toLinearMap.compMultilinearMap H) p f= L ∘ ink K A T h x H p f:=by funext z; unfold ink Function.comp; simp_rw [convey_at,_root_.map_smul]; rfl -- RHS comp issue check
lemma select_map (u:Finset (Down P))(x:Seats P)(H:Patron S P Y)(L:Y→L[ℂ] Z)(f:Full (fiber P))(he: Appointed K A T x H f): select K A T u x (L.toLinearMap.compMultilinearMap H) f=L (select K A T u x H f):=by
   unfold select branch essay; simp_rw [map_sum,Bouquet.transformed K A T]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _ => L.integral_comp_comm (he i j)))
lemma linear_fair {u:Pod}{x: Seats (only u)}{r:ℝ} (f:Full (fiber (only u)))(he:Fits r f) : Fair f (fun i=> closedBall (x i) r) x:= by
   intro p hp i j hj; rw [Metric.mem_closedBall, dist_eq_norm]; unfold actual; rw [add_sub_cancel_right]; exact (norm_house j p.val).trans (mem_closedBall_zero_iff.mp (he hp))
lemma moment_welcomes {r:ℝ} (u:Pod)(x:Seats (only u))(f:Full (fiber (only u)))(he:Fits r f)(hy:0<r)(hk:Frontier6.Safe K w (2*r)) : Welcomes (hearing u (StageWeight K (x (me u)) w)) x f:=by
   refine ⟨_,Bouquet.Gentle.hearing u _ (A:=fun i=>closedBall (x i) r) ?_,linear_fair f he⟩; intro I _ i v hv
   have hz(y:E4)(he: y ∈ closedBall (x default) r):‖y-x (me u)‖< 2*r:=by unfold me; rw [← dist_eq_norm]; linarith only [mem_closedBall.mp he,hy]
   exact (weight K w).continuous.continuousAt.comp (hv.purchased K w (y:=fun _=> x (me u)) hz continuousAt_const hk)
-- translation all organizations. visibility equality needed only on test
-- (get it with the same μ margin).
lemma sends (x:Seats P)(p:Trip A Q)(a:E4)(z:Margin P Q)(i:P):
   landed S a (garland h (togetherS K A p (transit h x z)) i)=garland h (togetherS K A p (transit h (fun i=> x i+a) z)) i:=by
    unfold garland; rw [landed_ring,map_prod]; refine prod_congr rfl (fun j hj=> ?_); let y := (A j.val).payment (p j)
    change landed S a (suit K _ y.fst y.snd)=suit K (centroid j.val z.val+(x (assign h j)+a)) _ _; rw [travels,← add_assoc];rfl
section
variable {p:Pod}(x:Seats (only p)) {h:Q≤only p}{r:ℝ} (f:Full (fiber (only p))) (hr:Fits r f) (hR: Frontier6.Safe K w r)
include hr hR
lemma ink_at_site (q: Trip A Q): ink K A T h x (hearing p (StageWeight K (x (me p)) w)) q f= ink K A T h 0 (hearing p (StageWeight K 0 w)) q f:=by
   ext1 z; by_cases he : Active T f z
   · let c:=x (me p); let X:= garland h (togetherS K A q (transit h 0 z)) (me p); have hp: Visible K 0 w X:= ((legitimate K A T h q he (x:=0) (linear_fair (x:=0) f hr) (me p)).act).visible K hR (by intro y hy; rw [sub_zero]; exact mem_closedBall_zero_iff.mp hy)
     have hv:landed S c X=garland h (togetherS K A q (transit h x z)) (me p):=by unfold X; rw [sends, show (fun i:only p=> (0: Seats (only p)) i + c)=x from funext (fun i=> (zero_add c).trans (congr_arg x (Subsingleton.elim ..)))]
     have hh:= shifts_cost K c 0 w hp; rw [zero_add,hv] at hh; unfold ink; simp_rw [convey_at,hearing_at]; exact congr_arg (_ • ·) hh
   unfold Active at he; unfold ink; rw [image_eq_zero_of_notMem_tsupport (fun h=> he (train_support _ _ h)), zero_smul,zero_smul]
end
end YM.Frontier6.Bouquet
