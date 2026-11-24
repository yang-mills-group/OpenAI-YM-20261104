import YM.RegulatorIR.Budget.Fold

/-! Fixed-length moments of tensor packets. Keep slack when comparing steps, no
hidden exponent increases on the diagonal. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Finset Function Motion Spatial
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X : Type} {r : ℕ}

namespace Tariff
lemma diam_mono {A B:Tariff X} (h:∀ i j,A.road i j≤ B.road i j)(x:Tuple X r): A.diameter x ≤ B.diameter x:= A.diameter_le (B.diameter_unit _) fun _ _=>(h ..).trans (B.diameter_ge x ..)
private lemma finDiam (A:Tariff X) (x:Tuple X r) : A.diameter x=1 ∨ ∃ i j,A.diameter x = A.road (x i) (x j) := by
  cases r with
  | zero=>left; simp [diameter]
  | succ r=>
     right
     let f (p:Fin (r+1) × Fin (r+1)) := A.road (x p.1) (x p.2)
     obtain ⟨⟨i,j⟩,_,h⟩:=exists_max_image (Finset.univ : Finset (Fin (r+1) × Fin (r+1))) f univ_nonempty
     exact ⟨i,j,le_antisymm (A.diameter_le (A.unit ..) fun i j=>h (i,j) (mem_univ _)) (A.diameter_ge x ..)⟩
lemma diamPow (A B:Tariff X)(k : ℕ)(h:∀ i j,A.road i j ^ k=B.road i j) (x:Tuple X r): A.diameter x^k=B.diameter x:= by
  apply le_antisymm
  · obtain he | ⟨i,j,he⟩ := A.finDiam x
    · rw [he,one_pow]; exact B.diameter_unit _
    rw [he,h]; exact B.diameter_ge x ..
  apply B.diameter_le (one_le_pow₀ (A.diameter_unit x))
  intro i j; rw [← h]; exact pow_le_pow_left' (A.diameter_ge x i j) _
end Tariff

namespace Premium
lemma prem_mono {A C:Tariff X}{B:Premium A}{D:Premium C} (h:∀ i j,A.road i j≤C.road i j)(he:∀ x,B.mark x≤ D.mark x) (x:Tuple X r) : B.width x≤ D.width x:= B.width_le ((A.diam_mono h x).trans (D.width_diameter x)) fun i=>(he _).trans (D.width_ge x i)
lemma witness {A:Tariff X}(B:Premium A) (x:Tuple X r) : B.width x=A.diameter x ∨ ∃ i,B.width x=B.mark (x i):=by
  cases r with
  | zero=>left;unfold width;simp
  | succ r=>
      obtain ⟨i,hi,h⟩:=Finset.exists_max_image (univ (α:=Fin (r+1))) (fun i=>B.mark (x i)) univ_nonempty
      rcases le_total (A.diameter x) (B.mark (x i)) with hh|hh
      · exact Or.inr ⟨i,le_antisymm (B.width_le hh fun _=>h _ (mem_univ _)) (B.width_ge ..)⟩
      exact Or.inl (le_antisymm (B.width_le le_rfl fun _=>(h _ (mem_univ _)).trans hh) (B.width_diameter x))
lemma width_pow (k:ℕ)(A C:Tariff X)(B:Premium A)(D:Premium C)(hr:∀ a b,A.road a b^k=C.road a b)(he:∀ x,B.mark x^k=D.mark x) (x:Tuple X r):B.width x^k=D.width x:=by
 apply le_antisymm
 · obtain hh|⟨i,hh⟩:=B.witness x
   · rw [hh,A.diamPow _ _ hr]; exact D.width_diameter x
   rw [hh,he]; exact D.width_ge ..
 apply D.width_le (by rw [← A.diamPow _ _ hr]; exact pow_le_pow_left' (B.width_diameter x) _)
 intro i; rw [← he]; exact pow_le_pow_left' (B.width_ge x i) _
end Premium

namespace Tariff
lemma pow_amount (l)(u)(d): amount l 1 d^u=amount l u d:=by simp [amount]

lemma diam_native (l : ℝ)(h:0<l)(f:X→Room)(j:ℕ)(x:Tuple X r) :
    ((native l h j).uses f).diameter x=((native l h 1).uses f).diameter x^j :=
 (diamPow _ _ _ (fun _ _=>pow_amount ..) _).symm
lemma diam_plus (l : ℝ)(h:0<l)(f:X→Room)(j k:ℕ)(x:Tuple X r) :
    ((native l h (j+k)).uses f).diameter x=((native l h j).uses f).diameter x*((native l h k).uses f).diameter x := by
 rw [diam_native l h f (j+k),diam_native l h f j,diam_native l h f k,pow_add]
lemma width_native (l : ℝ)(h:0<l)(f:X→Room)(x:Room)(j:ℕ)(v:Tuple X r) :
    ((Premium.rooted (native l h j) x).uses f).width v=((Premium.rooted (native l h 1) x).uses f).width v^j := (Premium.width_pow _ _ _ _ _ (fun _ _=>pow_amount ..) (fun _=>pow_amount ..) _).symm
lemma width_plus (l : ℝ)(h:0<l)(f:X→Room)(x)(j k:ℕ)(v:Tuple X r) :
    ((Premium.rooted (native l h (j+k)) x).uses f).width v=((Premium.rooted (native l h j) x).uses f).width v*((Premium.rooted (native l h k) x).uses f).width v:= by rw [width_native l h f x (j+k),width_native l h f x j,width_native l h f x k,pow_add]
end Tariff
end YM.RegulatorIR.Budget
