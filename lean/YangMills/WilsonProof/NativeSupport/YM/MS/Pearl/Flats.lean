import YM.MS.Pearl.Flats
import YM.MS.Pearl.Group
/-!
# The compact (formal finite perturbative) spectrum of single Φ(t,y) at scale
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{n m h ℓ:ℕ}{x:ℂ}
def Press (v: Flats G)(j m:ℕ)(y:ℝ): Mob G := v.sum fun ℓ x=>priceY j m ℓ x y
variable {f:Coat G}{V F X H:Flats G} {k:ℕ}
lemma Page (P:Finset ℕ)(hp:V.support⊆P)(h:ℕ)(s y:ℝ): Parade V h y s=∑ j∈P,(fun i:ℂ=> hikeP i h j y s (V j i)):= by
    funext i; unfold Parade; rw [Finset.sum_apply]; exact Finsupp.sum_of_support_subset V hp _ (fun i hi=> by simp [hikeP, ← cert])
lemma meritP (x:ℂ) (s y:ℝ)(F H:Mob G): hikeP x n ℓ y s (F+H)=hikeP x n ℓ y s F+hikeP x n ℓ y s H:= by simp [hikeP, ←cert, smul_add]
lemma page_add (F H:Flats G)(h:ℕ)(y s:ℝ): Parade (F+H) h y s= Parade F h y s+ Parade H h y s:= by
    rw [Page (F.support ∪ H.support) Finsupp.support_add, Page (F.support ∪ H.support) Finset.subset_union_left, Page (F.support ∪ H.support) Finset.subset_union_right]; funext k; simp only [Finsupp.add_apply, Pi.add_apply, meritP, Finset.sum_apply, Finset.sum_add_distrib]
lemma page_sl (f:Coat G)(m h:ℕ)(y s:ℝ)(x:ℂ): Parade (.single m f) h y s x=hikeP x h m y s (f x):= by unfold Parade; rw [ Finsupp.sum_single_index]; simp only [hikeP,Pi.zero_apply,←cert,map_zero,smul_zero]
lemma pageZ (h:ℕ)(y s:ℝ): Parade (0:Flats G) h y s=0:= by ext; simp [Parade]
lemma page_sub (F H:Flats G)(h:ℕ)(y s:ℝ): Parade (F-H) h y s= Parade F h y s- Parade H h y s:= by rw [eq_sub_iff_add_eq,← page_add,sub_add_cancel] -- patch below
lemma siphon0 (i:ℂ)(s y:ℝ): hikeP i n 0 y s (0:Mob G)=0:= by rw [hikeP,← cert,map_zero,smul_zero]
lemma pureP (f:Coat G)(h:∀ i, Home (f i) n)(s y:ℝ): Parade (.single 0 f) n y s=f:= by funext x; simp [page_sl,hikeP,h x s,weight, amount, toll]
lemma raypage (S:Finset ℕ)(hp:V.support ⊆ S) (y:ℝ): Press V m n y=∑ i∈ S,priceY m n i (V i) y := by refine Finsupp.sum_of_support_subset _ hp _ (fun i hi=>?_); change priceY m n i (0:Coat G) y=0; have hm:paid n (0:Coat G)=0:= (by ext; simp [paid]); simp only [priceY,hm,ruby0]; simp
abbrev Merg (F:Flats G) : Prop:= ∀ i,mer (F i)
lemma tallP (h:Merg F): ∃ j,Rent F j:= by
    suffices hv : ∀ S:Finset ℕ,∃ j,∀ i∈ S, altitude j ( F i) by
       obtain ⟨j,hj⟩:= hv F.support; refine ⟨j,fun i=>?_⟩; by_cases he:i∈F.support; exact hj i he; rw [Finsupp.notMem_support_iff.mp he]; exact altitude.zero
    intro S; induction S using Finset.induction with
    | empty=> exact ⟨0,fun i hi=> (Finset.notMem_empty _ hi).elim⟩
    | insert b s he ih=>
       obtain ⟨j,hj⟩:= ih; obtain ⟨N,h⟩:= h b; refine ⟨ max j N, fun i t=>?_⟩; rcases Finset.mem_insert.mp t with rfl|t; exact h.climb (le_max_right ..); exact (hj i t).climb (le_max_left ..)
lemma paidSum (S:Finset I)(f:I→ ℂ→ Mob G)(i:ℕ): paid i (∑ j∈S,f j)=∑ j∈S, paid i (f j):= by funext; simp [paid,Finset.sum_apply,Finset.mul_sum]
lemma press_pick (h:Rent F n)(t:ℕ)(s y:ℝ): Pick m (paid n (Parade F t y s)) (plow (-(t:ℂ)) s (Press F m n (y+s))) := by
   rw [ Page F.support (by rfl) , paidSum, Press, Finsupp.sum, ←cert,map_sum]; exact Pick.fin _ (fun i _=> lexP (h i) ..) -- proof above hp
lemma pressB (h:Rent F n)(m:ℕ) (y:ℝ): kPrice (Press F m n y):= by simpa only [posing,add_zero] using ( press_pick h 0 0 y (m:=m)).price
lemma press_ready (m:ℕ): Ready (Press F m n):= by convert! Ready.sums F.support (fun i (_:i∈F.support)=> grip m n i (F i)) using 1; ext; simp [Press,Finsupp.sum,Finset.sum_apply]
lemma viewP (V:Flats G) (m n:ℕ)(Q:LeanC G)(h:Need Q)(hp:Rent V n)(ht:∀ i:ℕ, To (V i) Q)(y:ℝ): Press V m n y∈Q:= Q.sum_mem fun i _=> priceC Q h (hp i) (ht i) y
lemma viewR (V:Flats G)(m n:ℕ) (Q:LeanR G)(h:Will Q)(hp:Rent V n)(ht:∀ i:ℕ,realAlong ( V i) Q)(y:ℝ) : Press V m n y∈Q:= Q.sum_mem fun i _=> priceR Q h (hp i) (ht i) y
end YM.MS.Pearl
