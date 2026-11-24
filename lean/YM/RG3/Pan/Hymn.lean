import YM.RG3.Pan.Moon

/-! # Reading all group's visits and base transports: derivative prices on
actual group arrays, retaining negative traversals and displacement paths. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan
open Function FreeResolvent Lattice RG Wilson WilsonStartup Next.Rank.Spindle Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {R : Type*} [AddCommGroup R] [One R] {G : Gauge} {n : Side}

/-- Exact itinerary with signs and current origins evaluated in R. -/
def rails (x : Four R) : Walk→List (Edge (Four R) × Bool)
 | []=> []
 | d::l=> (d.used x,d.neg):: rails (x+d.vec) l

@[simp] lemma rail_count (x : Four R) (w : Walk): (rails x w).length=w.length:= by
  induction w generalizing x with
  | nil=>rfl
  | cons a w ih=> simpa [rails] using ih (x+a.vec)
lemma rail_proof (U : Links R G.El) (x : Four R) (w : Walk) : travel U x w=((rails x w).map (flourish U)).prod:= by
  induction w generalizing x with
  | nil=>rfl
  | cons a w ih=> rw [travel,ih]; rfl

lemma rail_fits (x : Four R) (w : Walk) (i : Edge (Four R) × Bool) (h:i∈ rails x w):
    i.1.1∈ visits x w ∧ i.1.1+step i.1.2∈ visits x w:= by
  induction w generalizing x with
  | nil=> simp [rails] at h
  | cons a w ih=>
    have hx: x∈visits x (a::w) := List.mem_cons_self
    have he y (h:y∈visits (x+a.vec) w) : y∈visits x (a::w):=List.mem_cons_of_mem x h
    have hy:x+a.vec∈visits x (a::w):=he _ (by cases w <;> simp [visits])
    rcases List.mem_cons.mp h with hp|h
    · rw [hp]; cases hh:a.neg
      · exact ⟨by simpa only [Step.used,hh,Bool.false_eq_true,if_false] using hx,by simpa only [Step.used,Step.vec,hh,Bool.false_eq_true,if_false] using hy⟩
      exact ⟨by simpa [Step.used,hh,Step.vec,sub_eq_add_neg] using hy,by simpa [Step.used,hh] using hx⟩
    obtain ⟨hp,hq⟩:=ih _ h; exact ⟨he _ hp,he _ hq⟩

variable {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
 [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k : ℕ} {A d : ℝ}

/-- A path of genuine field letters starting at a specific site, with
edge-variation prices only at the read stencil and INCLUDE the last link's
positive partner in X even for inverse traversals. -/
lemma hymn {x : E} (U : E→ Links R G.El) (o : Four R) (w : Walk)
    (hA : 0≤ A) (hd : 0 ≤ d) (X : Finset (Four R)) (hX : ∀ y∈visits o w,y∈X)
    (h : ∀ i : Edge (Four R), i.1∈X → i.1+step i.2∈X → GroupHit k A d (fun z=> U z i) x) :
    Bill k ‖(1:G.Mat)‖ ((1+2^k*A*w.length)*d) (fun z=>G.mat (travel (U z) o w)) x := by
  let u (i:Edge (Four R) × Bool) z:=flourish (U z) i
  have he (i) (hh:i∈rails o w): GroupHit k A d (u i) x := by
    obtain ⟨h₁,h₂⟩:=rail_fits o w i hh
    have hi:= h i.1 (hX _ h₁) (hX _ h₂)
    unfold u flourish; split
    · exact hi.backtrack hA hd
    exact hi
  have ht:=song_bill _ hA hd he
  rw [rail_count] at ht; simp_rw [rail_proof]; exact ht

lemma refrain (Q : Bath G k) (o : Four R) (w : Walk) {x : E} (U : E→ Links R G.El)
    (hd : 0 ≤ d) {N : ℕ} (hw:w.length ≤ N)
    (h : ∀ i, GroupHit k Q.price d (fun z=>U z i) x) :
    Bill k ‖(1:G.Mat)‖ (span Q N*d) (fun z=>G.mat (travel (U z) o w)) x:= by
  classical
  let X:Finset (Four R):= (visits o w).toFinset
  exact (hymn U o w (zero_le_one.trans Q.extra) hd X (fun p hp=> List.mem_toFinset.mpr hp) (fun i _ _=>h i)).drift
    (mul_nonneg (zero_le_one.trans (span_one_le Q _)) hd) (mul_le_mul_of_nonneg_right (span_le _ hw) hd) (norm_nonneg _)

/-- Pan.plain with a rate on the external directions; use on true LEFT
ordered stacks etc. No factorial. -/
lemma Bill.gust {x : E} (L : E→L[ℝ] F) {A d C: ℝ} {f : F→Y}
    (h : Bill k A d f (L x)) (hL : ∀ v, ‖L v‖ ≤ C*‖v‖) (hd : 0 ≤ d) (hC : 0 ≤ C): Bill k A (d*C) (f ∘ L) x:= by
  refine ⟨h.smooth.comp _ L.contDiff.contDiffAt,fun i hi=>?_⟩
  rw [WardBin.Lies.liner L (h.smooth.of_le (Nat.cast_le.mpr hi)), mul_pow,←mul_assoc]
  have hA:=h.pos
  apply FreeResolvent.Affine.slot_op (by positivity)
  intro l hl; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine (ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ (fun j=>(hL (l j)).trans ((mul_le_of_le_one_right hC (hl j))))).trans ?_
  simpa using mul_le_mul_of_nonneg_right (h.B i hi) (pow_nonneg hC i)

end YM.RG3.Pan
