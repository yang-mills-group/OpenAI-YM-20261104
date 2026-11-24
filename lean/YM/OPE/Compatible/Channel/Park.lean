import YM.OPE.Compatible.Channel.Borders
/-!
# Type relocation on polynomial toll.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter MeasureTheory Finset Lattice Wilson Laurent RG
open scoped BigOperators Classical Topology
variable {I J K:Type*}
namespace Sack
variable {f g:I→ℝ}{w:J→ℝ}{v:I→ℝ}{t r:ℝ}
def rope (p:I→J) [DecidableEq J](f:I→ℝ) :J→ℝ:= fun j=> ∑' i:I,if p i=j then f i else 0
variable (p:I→J) [DecidableEq J]
lemma lineOne (j:J)(u : J→ℝ) (hp:0 ≤ u)(x:ℝ): Sack u (Pi.single (M:=fun _=>ℝ) j x) (u j *‖x‖):=by
   let f:=Pi.single (M:=fun _=>ℝ) j x
   have hv i (hx:i≠j):u i*‖f i‖=0:=by unfold f; simp [Pi.single_eq_of_ne hx]; --
   refine ⟨fun i=>mul_nonneg (hp i) (norm_nonneg _), summable_of_ne_finset_zero (s:={j}) (by intro i h; exact hv i (by simpa using h)),?_⟩
   rw [tsum_eq_single j hv]; simp [f]
lemma cart (h:Sack v f r)(ht:0≤t)(hp:1 ≤ w)(hu: ∀ i,w (p i) ≤ v i*t): Sack w (rope p f) (r*t):=by
   let g(i:I): J→ℝ:=Pi.single (p i) 1
   have he(i:I) : Sack w (g i) (v i*t):=(lineOne (p i) w (fun i=>zero_le_one.trans (hp i)) 1).tips (by rw [norm_one,mul_one];exact hu i)
   have hg:= Sack.carried h he ht
   rw [show rope p f=(fun j=>∑' i, (fun i j=> f i*g i j) i j) from funext fun j=> tsum_congr (fun i=> by by_cases h:p i=j<;>simp [g,h,Pi.single_apply])]
   exact hg.draw hp
-- cost no weight p needed for regrouping linear identity if both h(v) and Φ(p) polynomial.
lemma rope_add (h:Summable f)(hg:Summable g) : rope p (f+g)=rope p f+rope p g:=by
    ext j; unfold rope; simp only [Pi.add_apply]; rw [← Summable.tsum_add]; swap
    · exact ((h.indicator {x| p x=j}).congr fun i=> by simp [Set.indicator]) --
    swap; · exact ((hg.indicator {x|p x=j}).congr fun i=> by simp [Set.indicator])
    refine tsum_congr fun i=> ?_; split_ifs; rfl; simp
lemma anchor_sum (h:Summable f): ∑' j,(rope p f) j= ∑' i,f i:=by
    let l := fun i=> Pi.single (M:=fun _=>ℝ) (p i) (f i)
    have ha:= h.norm
    have hv : Summable (uncurry l) := (Sack.barrel (u:=fun _=>1) (fun i=> lineOne (p i) 1 (fun _=>zero_le_one) (f i)) (show SumBudget (fun i=>1*‖f i‖) (∑' i,‖f i‖) from by simp only [one_mul]; exact ⟨fun _=>norm_nonneg _,ha,le_rfl⟩)).water le_rfl --
    calc
      _ = ∑' j,∑' i, l i j:= tsum_congr fun j=>tsum_congr fun i=>by simp only [l, Pi.single_apply,eq_comm]
      _ = ∑' i,∑' j,l i j := hv.tsum_comm
      _ = _:= tsum_congr fun i=>by rw [tsum_eq_single (p i)]; simp [l]; intro a ha; simp [l,Pi.single_eq_of_ne ha]
lemma cart_bill (F:J→ℝ)(h:Summable fun i=> f i*F (p i)): ∑' j,rope p f j*F j=∑' i,f i*F (p i):=by
    rw [← anchor_sum p h]; refine tsum_congr fun j=> ?_ ; unfold rope; rw [← tsum_mul_right]; refine tsum_congr fun i=> ?_; split_ifs with ha; simp only [ha];simp
lemma stack (h:Summable f)(q:J→K)[DecidableEq K] : rope q (rope p f)=rope (q∘p) f:=by
    ext x; unfold rope; let a(i):ℝ:= if q (p i) = x then f i else 0
    have ht : Summable a:=(h.indicator {i|q (p i)=x}).congr fun i=>by simp only [Set.indicator, Set.mem_setOf_eq,a]; split_ifs <;> rfl
    change _= ∑' i,a i; rw [← anchor_sum p ht]; refine tsum_congr fun i=> ?_; by_cases H:q i=x
    · rw [if_pos H]; apply tsum_congr; intro j; unfold a; by_cases h': p j=i<;> simp [H,h'] -- tsum synt
    rw [if_neg H]; unfold rope a; simp_rw [show ∀ j:I,(if p j=i then if q (p j)=x then f j else 0 else 0)=(0:ℝ) from fun j=> by split_ifs with h' ha; exact False.elim (H (h' ▸ ha)); rfl; rfl];simp
end Sack
end YM.OPE.Flume
