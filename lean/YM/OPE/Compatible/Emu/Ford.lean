import YM.OPE.Compatible.Emu.Basin
/-!
# Flat flag bound — every free link recovered at small face price
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter Lattice Laurent Wilson Matrix RG Gauge
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
open Finset
variable {r s m i b k:ℕ} {R:Type*}[AddCommGroup R][One R] {G:Gauge} {a:Axis}
-- elementary circulation.identity, b>a
lemma circ (q:PlaqAxes) (U:Links R G.El)(x:Four R): let a:=q.val.1;let b:=q.val.2; faceValue U (x,q)=U (x,a)*U (x+step a,b)*(U (x+step b,a))⁻¹*(U (x,b))⁻¹:=by
      intro a b; unfold faceValue square travel; simp only[travel, Step.pos_read, Step.vec_pos, Step.neg_read, Step.vec_neg, mul_one]; rw[show x+step a+step b-step a=x+ step b by abel,show x+step a+step b+(-step a)-step b=x by abel]; group; rfl
lemma chordI (p q x y:G.El):G.chord p ≤ G.chord (p*q*x*y)+G.chord q+G.chord x+G.chord y:=by
       calc
           _ = G.chord ((p*q*x*y)*(q*x*y)⁻¹):= by group
           _ ≤ G.chord (p*q*x*y)+ G.chord (q*x*y)⁻¹:= G.chord_triangle ..
           _ ≤ _ :=by rw[G.chord_inv]; linarith only[G.chord_triangle q x,G.chord_triangle (q*x) y]
lemma chordJ (p q x y:G.El):G.chord y ≤ G.chord (p*q*x*y)+G.chord p+G.chord q+G.chord x:=by
       calc
           _ = G.chord ((p*q*x)⁻¹*(p*q*x*y)):= by group
           _ ≤ G.chord (p*q*x)⁻¹+G.chord (p*q*x*y):= G.chord_triangle ..
           _ ≤ _:=by rw[G.chord_inv]; linarith only[G.chord_triangle p q,G.chord_triangle (p*q) x]
lemma tread (a:Axis)(he:a≠perch): perch<a:= Nat.lt_of_le_of_ne (Nat.zero_le _) (fun h=>he (Fin.ext h.symm))
def blade (a:Axis)(he:a≠perch): PlaqAxes:= ⟨(perch,a),tread a he⟩
lemma chordK (x:Four R)(U:Links R G.El)(a:Axis)(he:a≠perch):
    G.chord (U (x,a)) ≤ G.chord (faceValue U (x,blade a he)) + G.chord (U (x,perch)) + G.chord (U (x+step perch,a))+G.chord (U (x+step a,perch)) ∧
    G.chord (U (x,perch)) ≤ G.chord (faceValue U (x,blade a he)) + G.chord (U (x+step perch,a))+G.chord (U (x+step a,perch))+G.chord (U (x,a)):=by
       let p:=U (x,perch); let q:=U (x+step perch,a); let z:=U (x+step a,perch); let y:=U (x,a); rw[show faceValue U (x,blade a he)=p*q*z⁻¹*y⁻¹ from circ ..]; constructor
       · exact (G.chord_inv y).symm.trans_le ((chordJ p q z⁻¹ y⁻¹).trans_eq (by rw[G.chord_inv]))
       exact (chordI p q z⁻¹ y⁻¹).trans_eq (by rw[G.chord_inv,G.chord_inv])
-- interior as finite patch. Free links only, nonlinear direct estimate.
noncomputable abbrev arrival (j:ℕ) (t f:ℝ):ℝ:= t+↑j*(2*t+f)
noncomputable abbrev maxArr (r:ℕ):=arrival (2*r+1)
noncomputable abbrev soilV (j r:ℕ)(t f:ℝ):ℝ:= t+↑j*(t+maxArr r t f+f)
noncomputable abbrev soil (r:ℕ):=soilV (2*r+1) r
variable {U:Links ℤ G.El} {t f:ℝ}
structure Ripe (r:ℕ)(t f:ℝ)(U:Links ℤ G.El):Prop where
       hpos : 0 ≤ t
       fees : 0 ≤ f
       gem : ∀ x:Edge Cover,x∉fieldP r→ G.chord (U x) ≤ t
       chordK (B:Face ℤ): B.1∈Lattice.box (r+1)→G.chord (faceValue U B) ≤ f
lemma plane (x:Cover)(i a:Axis)(h:i≠a): (x+step i:Cover) a=x a:=by simp[h.symm]
lemma sky (r:ℕ)(x:Cover): knot x perch∈fieldP r↔ x perch= -(r:ℤ)-1 ∧ dotUp (knot x perch)∈Lattice.box r:=by
       constructor
       · intro h; obtain ⟨hx,hK⟩:= mem_sdiff.mp h; have he:x∉Lattice.box r:=fun he=>hK ((beamH _).mpr ⟨rfl,he⟩); rcases(deck _).mp hx with h|h; exact False.elim (he h); refine ⟨?_,h⟩
         obtain ⟨ht,hI⟩:= box_test.mp h; dsimp only [knot,dotUp] at ht hI; have hp(a):a≠perch → (x+step perch:Cover) a=x a:=by intro he';exact plane x _ a he'.symm
         have hV:= ht perch; have hY:= hI perch; rw [Pi.add_apply,step_apply,if_pos rfl] at hV hY; by_contra h; apply he; refine box_test.mpr ⟨?_,?_⟩<;>intro i<;> by_cases hx:i=perch<;> first | (subst i; omega)| (specialize ht i; specialize hI i; rw [hp _ hx] at ht hI; omega)
       rintro ⟨hx,h⟩; refine mem_sdiff.mpr ⟨deck ..|>.mpr (Or.inr h),fun h=>?_⟩; have hh:= (beamH _).mp h|>.2; have hp:-(r:ℤ) ≤ x perch:=(box_test.mp hh).1 _; omega
namespace Ripe
variable (h:Ripe r t f U)
include h
lemma column (x:Cover)(hv:x perch ≠ -(r:ℤ)-1): G.chord (U (x,perch)) ≤ t:= h.gem _ (fun ht=>hv ((sky ..).1 ht).1)
-- Towers start on row. n.steps to boundary or EOS
lemma wing (i:Axis)(hi:i≠perch)(n:ℕ)(x:Cover)(hz:(r:ℤ)+1-x perch ≤ n): G.chord (U (x,i)) ≤ arrival n t f:=by
       induction n generalizing x with
       | zero=>
           simp only [arrival,Nat.cast_zero,zero_mul,add_zero]; apply h.gem; intro hp; rcases (deck _).1 (mem_sdiff.mp hp).1 with hu|hu; · have hh:= (box_test.mp hu).2 perch; change x perch ≤ (r:ℤ) at hh; omega
           have hh:= (box_test.mp hu).2 perch; change (x+step i:Cover) perch≤ (r:ℤ) at hh; rw [plane _ _ _ hi] at hh;omega
       | succ n ih=>
           have ht:= h.hpos; have hF:= h.fees; by_cases hv:knot x i ∈ Delta r; swap
           · unfold arrival; apply le_trans (h.gem _ fun H=> hv (mem_sdiff.mp H).1); exact le_add_of_nonneg_right (by positivity)
           have hy:=arcP hv|>.1; have he:-(r:ℤ) ≤ x perch:=by
                  rcases(deck _).1 hv with hu|hu; exact (box_test.mp hu).1 perch; have hh:= (box_test.mp hu).1 perch; change -(r:ℤ) ≤ (x+step i:Cover) perch at hh; rw[plane _ _ _ hi] at hh;exact hh
           have hb:= h.column x (show x perch≠ -(r:ℤ)-1 by omega); have hp:= h.column (x+step i) (by rw [plane _ _ _ hi]; omega); have hh:= ih (x+step perch) (by rw[Pi.add_apply,step_apply,if_pos rfl]; omega)
           have hs:= (Merchant.chordK x U _ hi).1; have hd:= h.chordK (x,blade i hi) hy; unfold arrival at *; push_cast at *; linarith
lemma pricey (x:Cover)(a:Axis)(hx:a≠perch): G.chord (U (x,a))≤ maxArr r t f:=by
       by_cases hv:knot x a ∈ Delta r; swap
       · have he:=h.hpos; have hk:=h.fees; unfold maxArr arrival; apply le_trans (h.gem _ fun H=> hv (mem_sdiff.mp H).1); exact le_add_of_nonneg_right (by positivity)
       have hm:-(r:ℤ)≤ x perch:=by
            rcases(deck _).1 hv with hp|hp; exact (box_test.mp hp).1 perch; have hh:= (box_test.mp hp).1 perch; change -(r:ℤ)≤ (x+step a:Cover) perch at hh; rw[plane _ _ _ hx] at hh; exact hh
       exact h.wing _ hx _ _ (by omega)
lemma down (x:Cover)(hx:knot x perch∈fieldP r)(i:Axis)(hi:i≠perch): G.chord (U (x,i)) ≤ t:=by
       apply h.gem; intro h; have he:= (sky ..).1 hx|>.1; rcases(deck _).1 (mem_sdiff.mp h).1 with hp|hp; · have hy:= (box_test.mp hp).1 perch; change -(r:ℤ)≤ x perch at hy;omega
       have hy:= (box_test.mp hp).1 perch; change -(r:ℤ)≤ (x+step i:Cover) perch at hy; rw[plane _ _ _ hi] at hy; omega
lemma bone (x:Cover)(a:Axis)(ha:a≠perch)(m:ℕ)(hm:(r:ℤ)+1-x a ≤ m):G.chord (U (x,perch)) ≤ soilV m r t f:=by
      have hp:=h.hpos; have hq:=h.fees; have hv:0 ≤ maxArr r t f:=by unfold maxArr arrival; positivity
      induction m generalizing x with
      | zero=>
         unfold soilV; push_cast; rw [zero_mul,add_zero]; apply h.gem; intro hx; obtain ⟨ht,hX⟩:= (sky ..).1 hx; have hh:= (box_test.mp hX).2 a; change (x+step perch:Cover) a ≤ _ at hh; rw [plane _ _ _ ha.symm] at hh; omega
      | succ m ih=>
         by_cases hT:knot x perch∈fieldP r; swap; · unfold soilV; apply (h.gem _ hT).trans; exact le_add_of_nonneg_right (by positivity)
         let y:= x+step a; have hx:y a=x a+1:=by simp[y]
         have he:= (Merchant.chordK x U _ ha).2; have hk:= ih y (by omega); have hh:=h.chordK (x,blade a ha) (arcP (mem_sdiff.mp hT).1).1; have hU:=h.down x hT a ha; have hd:= h.pricey (x+step perch:Cover) a ha; unfold soilV at *; change G.chord (U (x+step a,perch)) ≤_ at hk; rw[Nat.cast_add_one]; linarith
lemma sand (x:Cover): G.chord (U (x,perch)) ≤ soil r t f:=by
      by_cases hm:knot x perch∈fieldP r; swap; · have he:=h.fees; have hf:=h.hpos; unfold soil soilV maxArr arrival; apply (h.gem _ hm).trans; exact le_add_of_nonneg_right (by positivity)
      let a:Axis:= 1; have hv:a≠perch:=by decide +revert -- fails?
      apply h.bone x a hv; obtain ⟨ht,hX⟩:= (sky ..).1 hm; have he:= (box_test.mp hX).1 a; change -(r:ℤ)≤ (x+step perch:Cover) a at he; rw[plane _ _ _ hv.symm] at he; omega
lemma sumV (x:Edge Cover): G.chord (U x) ≤ soil r t f+maxArr r t f:=by
      obtain ⟨x,i⟩:=x; have he:= h.hpos; have hv:=h.fees; by_cases hq:i=perch; · subst i; exact (h.sand _).trans (le_add_of_nonneg_right (by unfold maxArr arrival; positivity))
      exact (h.pricey _ _ hq).trans (le_add_of_nonneg_left (by unfold soil soilV maxArr arrival; positivity))
end Ripe
end YM.OPE.Merchant
