import YM.FormalBulk08.Jets.Bent

/-! Fibrewise smooth substitutions into `Pap` for Elan. Longitude fixes Jacobian
in the particular `Sum` order, `DecidableEq` indices made explicit. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Jets
open Series Wick Orb Matrix PowerSeries Function Filter Set
open scoped BigOperators Classical Topology ContDiff
variable {V I J B E : Type*}
lemma roam_compose (f : I→Pap V) (g : J → Pap I) (p : Pap J) : roam ℝ f (roam ℝ g p)= roam ℝ (fun i=> roam ℝ f (g i)) p := by
   unfold roam;rw [change_comp];
   have ht : (changeBy (insertAt ℝ f)).comp (insertAt ℝ g)=insertAt ℝ (fun i=>roam ℝ f (g i)) := ?h
   rw [ht]; rfl
   case h => ext <;> simp; rfl

variable [Fintype V] [Fintype I] [Fintype J]
lemma motor_compose (f : Rays I→ Rays V) (g : Rays J → Rays I) (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) (p : f 0=0) (q : g 0=0) (i : V) : roam ℝ (motor g) (motor f i)=motor (f∘g) i := by
   apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R:=Glyphs ℝ J))
   rw [town _ _ (by simp [p,q]), ← show roam ℝ (motor g) X=X from change_X _,←map_mul, town f i p, ←paste_steps (fun x=> f x i) g (coord_diff f hf i) hg q];rfl
-- coordinate lifts
lemma paste_index (i:I) : paste (fun z:Rays I=> z i)= X*C (MvPolynomial.X i) := by
   apply photo; intro x; refine unique_gaze (fixed_path x _ (contDiffAt_apply ..)) ?_
   rw [map_mul]; simpa [glimpse] using (gaze_leaf (x i) 1)
omit [Fintype V] in
lemma motor_wires (k : V→I) (i : V) : motor (fun z:Rays I=> z ∘ k) i=C (MvPolynomial.X (k i)) := by
   apply mul_left_cancel₀ PowerSeries.X_ne_zero
   rw [town _ _ rfl]; exact paste_index _
omit [Fintype V] [Fintype I] in
lemma pure_translate (k : I→ V) (p:Pap I) : roam ℝ (fun i=> C (MvPolynomial.X (k i))) p=PowerSeries.map (MvPolynomial.rename k).toRingHom p := by
   unfold roam;rw [← pure_map,show insertAt ℝ _= C.comp (MvPolynomial.rename k).toRingHom from ?_];
   ext <;> simp
omit [Fintype I] in
lemma fit_translate (k : I→ V) (p : Pap I) : roam ℝ (motor (fun x:Rays V=> x ∘ k)) p=PowerSeries.map (MvPolynomial.rename k).toRingHom p := by
   rw [show motor _=_ from funext (motor_wires k)]; exact pure_translate k p

def hitch (u : Rays (V⊕J)→ Rays V) (w : Rays J→Rays I) : Rays (V⊕J)→ Rays (V⊕I) := fun z=> Sum.elim (u z) (w (z ∘ Sum.inr))
lemma hull_dish (u : Rays (V⊕J)→Rays V) (j : Rays J→ Rays I) (a : ContDiffAt ℝ ∞ j 0) (b:j 0=0) (p : Pap (V⊕I)) : dish (motor u) (motor j) p=roam ℝ (motor (hitch u j)) p := by
   unfold dish; have hh : Sum.elim (motor u) (fun i => upstream V (motor j i))=motor (hitch u j) := by
     ext1 i; cases i with
     | inl i=> rfl
     | inr i=>
       let f:= fun z:Rays (V⊕J)=>z ∘ Sum.inr
       change PowerSeries.map (MvPolynomial.rename Sum.inr).toRingHom (motor j i)=motor (j ∘ f) i
       rw [←fit_translate,motor_compose j f a ?_ b rfl]
       exact (contDiffAt_pi.mpr fun t => contDiffAt_apply ..)
   rw [hh]
omit [Fintype V] [Fintype I] [Fintype J] in
lemma hitch_zero (u : Rays (V⊕J)→ Rays V) (w : Rays J→Rays I) (h : u 0=0) (p : w 0=0) : hitch u w 0=0 := by
   funext i; cases i <;> simp [hitch,h,p,show (0 : Rays (V⊕J)) ∘ (Sum.inr : J→V⊕J)=0 from rfl]
lemma hitch_smooth (u : Rays (V⊕J)→ Rays V) (w : Rays J→Rays I) (h : ContDiffAt ℝ ∞ u 0) (p : ContDiffAt ℝ ∞ w 0) : ContDiffAt ℝ ∞ (hitch u w) 0 := by
   refine contDiffAt_pi.mpr ?_; rintro (i|i)
   · exact coord_diff _ h _
   let E := (fun x:Rays (V⊕J)=>x ∘ Sum.inr)
   exact coord_diff (w ∘ E) ((show ContDiffAt ℝ ∞ w (E 0) from p).comp 0 (contDiffAt_pi.mpr fun j=>contDiffAt_apply ..)) i
lemma still_on : still V J=motor (fun z:Rays (V⊕J) => z ∘ Sum.inl) := by funext i; rw [motor_wires];rfl
end YM.FormalBulk08.Jets
