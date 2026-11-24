import YM.AlbaMS.Super.Stem
import Mathlib.RingTheory.Nilpotent.Exp
/-!
# Commutation and exponentials over ℚ-algebras

BV exponent identities including non-geometric number of generators (no
finiteness on latter). Labels nilpotent (arbitrary here; for these uses
choose perturbative order tags and mark couplings separately, commuting
and square null as needed). Do not assume variable dag calculus real Ward.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {ι R E : Type*} [CommRing R] {ρ : ι→Bool} {p q e : Bool} {x y : ι}
variable {F G H : Coil ρ R} {l : List ι} {n m : ℕ} {k : ι→ι→R} {s : Finset ι}
namespace Coil
lemma Tone.glides (h:Tone false F)(p): plane p F=F:= by simp [h.pl]
lemma Tone.skim (h:Tone false F)(G : Coil ρ R): F*G=G*F:= h.slider G
lemma Tone.even_pow (h:Tone false F)(n): Tone false (F^(n:ℕ)):=by induction n with|zero=>simp [Tone.one]|succ n ih=> rw [pow_succ]; exact ih.mul h
lemma Cap.pow (h:Cap F n)(m:ℕ): Cap (F^m) (m*n):=by induction m with|zero=>simp [Cap.one]|succ m ih=> rw [pow_succ,Nat.add_mul,Nat.one_mul];exact ih.mul h
lemma Inside.pow {s : Set ι} (h:Inside s F)(n:ℕ): Inside s (F^n):=by induction n with|zero=>simp [Inside.one]|succ n ih=>rw [pow_succ];exact ih.mul h

def FinRank (F : Coil ρ R) :Prop:=∃ n,Cap F n
namespace FinRank
lemma none : FinRank (0:Coil ρ R):=⟨0,Cap.zero⟩
lemma put (c:R): FinRank (put ρ c):=⟨0,Cap.const c⟩
lemma one : FinRank (1:Coil ρ R):= put 1
lemma d (h:FinRank F): FinRank (D x F):=⟨h.choose,(h.choose_spec.up (Nat.le_succ _)).dz x⟩
lemma plane (h:FinRank F): FinRank (plane p F):=⟨_,h.choose_spec.pane⟩
lemma add (h:FinRank F)(H:FinRank G):FinRank (F+G):=⟨_,(h.choose_spec.up (le_max_left _ _)).add (H.choose_spec.up (le_max_right _ _))⟩
lemma smul (h:FinRank F)(c:R):FinRank (c • F):=⟨_,h.choose_spec.smul c⟩
lemma neg (h:FinRank F):FinRank (-F):=⟨_,h.choose_spec.neg⟩
lemma sub (h:FinRank F)(H:FinRank G):FinRank (F-G):=sub_eq_add_neg F G ▸ h.add H.neg
lemma sum (v: Finset E)(f:E→Coil ρ R)(h:∀ i∈v,FinRank (f i)):FinRank (∑ i∈v,f i):=by
  induction v using Finset.induction_on with|empty=>simp [none]|@insert i t ht IH=>rw [Finset.sum_insert ht]; apply add (h i (by simp)) (IH (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
lemma mul (h:FinRank F)(H:FinRank G):FinRank (F*G):=⟨_,h.choose_spec.mul H.choose_spec⟩
lemma pow (h:FinRank F)(n:ℕ):FinRank (F^n):=⟨_,h.choose_spec.pow n⟩
lemma touch (h:FinRank F): FinRank (touch k s F):=⟨h.choose,(h.choose_spec.up (by omega : h.choose ≤ h.choose+2)).touch _ _ _ _⟩
lemma cross (h:FinRank F)(H:FinRank G):FinRank (cross p k s F G):=(((h.mul H).touch).sub (h.touch.mul H)).sub (h.plane.mul H.touch)
end FinRank

-- even derivational operators, any grading. Only require Leibniz with first operand even.
variable {A : Coil ρ R →+ Coil ρ R}
def lever (A : Coil ρ R →+ Coil ρ R) :Prop:=∀ F G,Tone false F→ A (F*G)=F*A G+A F*G
lemma leverD : lever (D (ρ:=ρ) (R:=R) x).toAddMonoidHom:= by
  intro F G h; exact (mulD ..).trans (by change D x F * G+ (plane (ρ x) F)*D x G=_; rw [h.glides,add_comm];rfl)
lemma cross_lev (h:Graded ρ p k)(H:Tone e F): lever ((tether p k s F):_→ₗ[_]_).toAddMonoidHom:=by
  intro a b ha; apply (cross_leib H h).trans; rw [ha.glides,add_comm];rfl
lemma lever_one (h:lever A) : A 1=0:=by have he:=h 1 1 Tone.one; simp only [mul_one,one_mul] at he; rw [← sub_eq_iff_eq_add,sub_self] at he;exact he.symm
variable [Algebra ℚ R]
open IsNilpotent
-- use IsNilpotent.exp directly, no local polynomial-exp alias confusion
lemma Cap.exponent (h:Cap F n): Cap (exp F) (nilpotencyClass F*n):=by
  refine Cap.sum _ _ fun i hi=>?_ ; rw [← algebraMap_smul R];exact ((h.pow i).up (Nat.mul_le_mul_right _ (Nat.le_of_lt (Finset.mem_range.mp hi)))).smul _
lemma Tone.exponent (h:Tone false F): Tone false (exp F):=by
  refine Tone.sum _ _ fun i _=>?_ ; rw [← algebraMap_smul R]; exact (h.even_pow i).smul _
lemma Inside.exponent {s : Set ι}(h:Inside s F): Inside s (exp F):=by
  refine Inside.sum _ _ fun i _=>?_ ; rw [← algebraMap_smul R]; exact (h.pow i).smul _
lemma FinRank.exponent (h:FinRank F):FinRank (exp F):=⟨_,h.choose_spec.exponent⟩

omit [Algebra ℚ R] in
lemma sweep (h:lever A)(ht:Tone false F)(n): A (F^((n:ℕ)+1))=(n+1:ℕ) • (F^n*A F):=by
  induction n with
  | zero=> simp
  | succ n ih=>
    rw [pow_succ',h _ _ ht, ih,← (ht.even_pow (n+1)).skim (A F),mul_smul_comm] -- skim direction
    rw [← mul_assoc F,← pow_succ'];simp only [add_smul,one_smul]
lemma swept (h:lever A)(ht:Tone false F)(hv:IsNilpotent F): A (exp F)=exp F * A F:=by
  obtain ⟨n,hn⟩:=hv
  calc
    _ = ∑ i ∈Finset.range n, (↑(i+1).factorial:ℚ)⁻¹ • A (F^(i+1)):= by
      rw [exp_eq_sum (show F^(n+1)=0 from pow_eq_zero_of_le (Nat.le_succ n) hn),Finset.sum_range_succ',map_add,map_sum]; simp_rw [map_rat_smul];simp [lever_one h]
    _ = ∑ i∈Finset.range n, (↑i.factorial:ℚ)⁻¹ • (F^i*A F):=Finset.sum_congr rfl fun i _=> by
      rw [sweep h ht,← Nat.cast_smul_eq_nsmul ℚ, smul_smul]; congr 1; rw [Nat.factorial_succ, Nat.cast_mul,mul_inv_rev, mul_assoc]; field_simp
    _ = _:=by simp_rw [exp_eq_sum hn, Finset.sum_mul,smul_mul_assoc]
lemma D_exp (h:Tone false F)(hv:IsNilpotent F): D x (exp F)=exp F * D x F:= swept (leverD (x:=x)) h hv
lemma cross_exp (h:Tone false F)(tv:Tone p G)(hk:Graded ρ e k)(H:IsNilpotent F): cross e k s G (exp F)= exp F*cross e k s G F:= swept (A:=(tether e k s G).toAddMonoidHom) (cross_lev hk tv) h H
lemma linked (h:Tone false F)(x y : ι): halve R • link ρ x y F F = D y F*D x F := by
  rw [link,h.glides]; rw [show plane (ρ y) (D x F)*D y F = D y F*D x F from ?_,twice_halve]; rw [(h.dz x).pl]; have he:=(h.dz x).commute (h.dz y); cases hx : ρ x<;>cases hy: ρ y<;> simp [hx,hy,he] at *
lemma touch_exp (h:Tone false F)(hk:Graded ρ p k)(H:IsNilpotent F): touch k s (exp F)= exp F *(touch k s F + halve R • cross p k s F F):=by
  rw [from_cross _ _ _ _ _ hk,touch_apply,touch_apply]; simp_rw [Finset.smul_sum]; simp only [smul_comm (halve R) (k _ _), linked h]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [← Finset.sum_add_distrib,Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [D_exp h H,mulD,D_exp h H,h.exponent.glides]; simp only [mul_assoc,mul_add, smul_add,mul_smul_comm]; abel

end Coil
end YM.MSBar.Bric
