import YM.Frontier6.Bouquet.Carnival.Cloud

/-! Host powers flow through this Spin account. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable (K:Final C F S){P Q:Ensemble}{d:Slot →ℕ}(i:P) (M:Pod→ℝ)(p:Part d i)(R: Air (S:=S) P I L Y) (B: ℝ)
set_option quotPrecheck false
local notation "A"=> landscape K i M p R B

lemma prize (he:Dais K d P M)(hp:R.Welkin M)(hr:Air.Hosts K R)(hB:0<B): Air.Hosts K A := by
    intro J f T hT V x hx hV hV' hx' u v hv
    let a:= x (some (R.role i)); let b:=x none; let D:=insert a V; let z:= fun j:J=>(R.region (f j).here).center i; let y j:=(f j).here
    have ht: T.Mint (fun j:J=>(f j).radius) (-b):= hx none; have hu: R.route.Speaks T y (x ∘ some):= fun j=> hx (some j)
    have ha:0 ≤ a:= R.route.speaks_nonneg T y hu (R.role i); have hb: b∈ V:=by have hh:(A).role i=none:= if_pos rfl; simpa only [hh] using hx' i
    have hh: V⊆ D:= Finset.subset_insert ..; have hD(j:P): x (some (R.role j))∈D:=by by_cases h:j=i; subst j; exact Finset.mem_insert_self ..; exact hh ((show (A).role j=some (R.role j) from if_neg h) ▸ hx' j)
    let α:= slope i p; let W:= (α:ℝ)*(b-a); let β:= update u i (u i-W); let F(j:J):= movedBy K i p (z j) (v i j); let v':=update v i F
    have hv'(j:P): Pen K T D (x (some (R.role j))) (R.foci y j) (v' j) (β j) := by
        unfold v' β; by_cases h:j=i; · subst j; rw [update_self,update_self]; exact slides K i M p R B f T he hp ht (hu (R.role i)) (hh hb) hB ((show x ((A).role i)=b from congr_arg x (show (A).role i=none from if_pos rfl)) ▸ ((hv i).spectrum hh))
        rw [update_of_ne h,update_of_ne h]; have hs:(A).role j=some (R.role j):=if_neg h; rw [← hs]; refine ((hv j).spectrum hh).weaker (Eventually.of_forall fun k=>?_); change (ruffle i (shift i p (R.region (y k)) M) _).foot j ⊆ (R.region (y k)).foot j; rw [ruffles i _ h,shifted_unchanged i _ _ p h]
    have hβ:= hr J y T D (x ∘ some) hu (hh hV) (fun j hj=> by rcases mem_insert.mp hj with h|h; rw [h]; exacts [ha,hV' j h]) hD β v' hv'
    let Y(j:J):=((f j).radius/R.lengths (y j) i)^α
    have hw:T.Mint Y (-W):=by
       have hx:T.Mint (fun j=> R.lengths (y j) i) (-a):= hu (R.role i)
       exact ((ht.div hx).power α).eq (by unfold W; ring)
    have hY:= hβ.scalarR₀ (hw.inv.pay); rw [neg_neg, show W+ ∑ j:P,β j = ∑ j:P,u j from ?_] at hY
    · refine hY.cf (Eventually.of_forall fun j=>?_); dsimp only; rw [smul_smul]; change ((Y j)⁻¹*(R.account (y j))⁻¹) • R.sky (y j) (fun k=> v' k j) = (_* Y j)⁻¹ • moves K i (R.sky (y j)) p (R.region (y j)).center _; rw [mul_inv_rev,moves,transactions]; congr 2; ext1 k; by_cases h:k=i; subst k; unfold v'; simp only [update_self]; rfl; unfold v'; simp only [update_of_ne h]
    let D:= Finset.univ.erase i; have he: (∑ j∈D,β j)= (∑ j∈D,u j):=Finset.sum_congr rfl fun j hj=> update_of_ne (ne_of_mem_erase hj) _ _; rw [← Finset.sum_erase_add _ _ (mem_univ i), ← Finset.sum_erase_add _ u (mem_univ i),show ∑ j∈ Finset.univ.erase i,β j = _ from he]; unfold β; rw [update_self]; abel
end YM.Frontier6.Bouquet.Atelier
