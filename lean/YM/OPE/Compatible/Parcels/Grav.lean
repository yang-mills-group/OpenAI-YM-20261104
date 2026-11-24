import YM.OPE.Compatible.Parcels.Vales
/-!
# Integer Taylor expansion. Programs use *all* directions, distinguish spatial degree from field jets
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG
open scoped Topology BigOperators Classical
variable {I: Type*}[Fintype I][DecidableEq I]
def pedal (x:ℤ) :ℕ→ℝ
| 0=>1
| n+1=> pedal x n*(x-n) /(n+1:ℝ)
lemma pedal_zero (n):pedal 0 (n+1)=0:=by induction n with
   | zero=>simp [pedal]
   | succ n ih=> rw [pedal,ih]; simp
lemma pedal_succ (x:ℤ)(n:ℕ): pedal (x+1) (n+1)=pedal x (n+1)+pedal x n:=by
    induction n with
    | zero=>simp [pedal]
    | succ n ih=> rw [pedal,ih]; simp only [pedal]; push_cast; field_simp; ring
-- monomial index use Multiset axes.
def pine (m:Multiset I)(x:Shift I):ℝ:=∏ i,pedal (x i) (m.count i)
lemma pine_zero (m:Multiset I): pine m 0=if m=0 then 1 else 0:=by
    classical
    split
    next h => rw [h,pine]; simp [pedal]
    next h=>
        obtain ⟨x,hx⟩:=Multiset.exists_mem_of_ne_zero h
        unfold pine; apply Finset.prod_eq_zero (Finset.mem_univ x)
        obtain ⟨i,hi⟩:=Nat.exists_eq_succ_of_ne_zero (Multiset.count_pos.mpr hx|>.ne')
        rw [hi]; exact pedal_zero _
lemma pine_step (m:Multiset I)(x:I)(h:x∈m): numDiff x (pine m)=pine (m.erase x):=by
    ext1 p; unfold numDiff pine; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x),← Finset.mul_prod_erase _ (fun i=> pedal (p i) (m.count i)) (Finset.mem_univ x), ← Finset.mul_prod_erase _ (fun i=> pedal (p i) ((m.erase x).count i)) (Finset.mem_univ x)]
    have hx: (p+stint x) x=p x+1:=by simp [stint]
    have he: p x ≠ (p+stint x) x:=by omega
    have ht(j:I)(hj:j∈Finset.univ.erase x): pedal ((p+stint x) j) (m.count j)=pedal (p j) (m.count j):=by simp [stint,Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    have hz(j:I)(hj:j∈Finset.univ.erase x):pedal (p j) ((m.erase x).count j)=pedal (p j) (m.count j) :=by rw [Multiset.count_erase_of_ne (Finset.ne_of_mem_erase hj)]
    have hM : (m.erase x).count x+1=m.count x:=by
        rw [Multiset.count_erase_self]; have := Multiset.count_pos.mpr h; omega
    rw [Finset.prod_congr rfl ht, Finset.prod_congr rfl hz,hx];
    have hR:= pedal_succ (p x) ((m.erase x).count x);rw [hM] at hR; rw [hR];ring
lemma pine_dies (m:Multiset I)(x:I)(h:x∉m): numDiff x (pine m)=0 :=by
   ext1 p; change pine m (p+stint x)-pine m p=0; apply sub_eq_zero.mpr; unfold pine; apply Finset.prod_congr rfl; intro j _; by_cases ht:j=x; rw [ht,Multiset.count_eq_zero.mpr h]; rfl
   simp [stint,Pi.single_eq_of_ne ht]
-- dvol zero projections
omit [Fintype I] in
lemma dvol_zero {Y:Type*}[AddCommGroup Y](l:List I): dvol l (0:Shift I→Y)=0:=by
    induction l with
    | nil=>rfl
    | cons i l ih=>rw [dvol,ih]; ext; simp [numDiff]
lemma known (m:Multiset I)(l: List I): dvol l (pine m) 0= if (l:Multiset I)=m then 1 else 0 := by
    induction l generalizing m with
    | nil=>rw [dvol,pine_zero]; simp [eq_comm]
    | cons i l ih=>
       rw [dvol,rotate_tail]; by_cases hi:i∈m
       · rw [pine_step m i hi,ih]; have he:(↑(i::l):Multiset I)=m ↔ ↑l=m.erase i:=by
            change i ::ₘ (l:Multiset I) = m ↔ _; conv_lhs => rw [← Multiset.cons_erase hi]
            exact Multiset.cons_inj_right i
         simp only [he]
       have hx: (↑(i::l):Multiset I)≠m:=by rintro rfl; simp at hi
       rw [pine_dies m i hi,dvol_zero]; simp [hx]
lemma overrun (m:Multiset I)(l: List I)(h:m.card<l.length): dvol l (pine m)=0:=by
    induction l generalizing m with
    | nil=>simp at h
    | cons i l ih=>
       rw [dvol,rotate_tail]; by_cases hi:i∈m
       · rw [pine_step m i hi]; apply ih; have he:= congr_arg Multiset.card (Multiset.cons_erase hi); simp only [Multiset.card_cons] at he; rw [← he] at h; simpa using h
       rw [pine_dies m i hi,dvol_zero]
end YM.OPE.Flume
