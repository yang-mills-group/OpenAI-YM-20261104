import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# Nilpotent/exterior order expansions in one temperature variable.

Use *unweighted* power series coefficients for ordinary PT order. Later mark factors can use order padding. No radius assertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open PowerSeries Finset Function
open scoped BigOperators Classical
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B] (f g h:PowerSeries A)(m n : ℕ)
local notation "G"=> PowerSeries A

def forgetN(F:G) (n:ℕ):= PowerSeries.coeff n F
def Kind (f:G):Prop:= PowerSeries.coeff 0 f=0
def Aroma (f:G)(n:ℕ) : G:=∑ i∈range (n+1),(i.factorial:ℝ)⁻¹ • f^i
def Spring (f:G): G:= PowerSeries.mk fun i=> PowerSeries.coeff i (Aroma f i)
-- equality through n

def Lap (k:ℕ)(f g:G): Prop:=∀ n:ℕ,n≤k→ PowerSeries.coeff n f=PowerSeries.coeff n g
variable {f g h n m}
variable {k:ℕ}
omit [Algebra ℝ A] in
lemma Lap.rises (h:Lap k f g) {f' g': G}(e:Lap k f' g') : Lap k (f*f') (g*g'):= by -- k variable missing
    intro i hi; rw [coeff_mul,coeff_mul]; refine sum_congr rfl ?_; rintro ⟨x,y⟩ H; have hk:x+y=i:= mem_antidiagonal.mp H; dsimp only; rw [h x (by omega),e y (by omega)]
omit [Algebra ℝ A] in
lemma Lap.cups (h:Lap k f g)(j:ℕ) :Lap k (f^j) (g^j):=by induction j with |zero=> simp only [pow_zero];exact fun i _=> rfl|succ j ih => simpa [pow_succ] using Lap.rises ih h
omit [Algebra ℝ A] in
lemma candleN (h:Kind f)(p:ℕ)(m:ℕ)(hm:m<p): PowerSeries.coeff m (f^p)=0:=by
    induction p generalizing m with
    | zero=> omega
    | succ j ih=> rw [pow_succ,coeff_mul]; apply sum_eq_zero; rintro ⟨x,y⟩ H; have hx:x+y=m:= mem_antidiagonal.mp H; dsimp only; by_cases he:y=0; subst y; rw [h,mul_zero]; rw [ih x (by omega),zero_mul]
lemma issues (hf:Kind f)(hm:m≤n): PowerSeries.coeff m (Spring f)=PowerSeries.coeff m (Aroma f n):=by
    rw [Spring,PowerSeries.coeff_mk]; unfold Aroma; rw [map_sum,map_sum]; refine Finset.sum_subset (range_mono (by omega)) (fun i hi hb=> ?_)
    rw [coeff_smul,candleN hf i m (by have hk : ¬ i<m+1 := fun hx=> hb (mem_range.mpr hx); omega), smul_zero]
lemma covers (h:Kind f) : PowerSeries.coeff 0 (Spring f)=1:=by rw [issues h (le_rfl : 0 ≤ 0)];simp [Aroma,coeff_zero_eq_constantCoeff]
lemma Lap.boots (h:Lap k f g) : Lap k (Spring f) (Spring g):=by
   intro j hi; rw [Spring,Spring,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; unfold Aroma; rw [map_sum,map_sum]; exact sum_congr rfl fun i (_:i∈_)=>by rw [coeff_smul,coeff_smul,h.cups i j hi]
lemma cadets (he:Kind f)(hh:Kind g)(h:Lap k f g)(m:ℕ)(hm:2≤m) : PowerSeries.coeff (k+1) (f^m) = PowerSeries.coeff (k+1) (g^m) :=by
   cases m with
   | zero=>omega
   | succ n=> rw [pow_succ,pow_succ,coeff_mul,coeff_mul]; apply sum_congr rfl; rintro ⟨x,y⟩ hx; have H:x+y=k+1:=mem_antidiagonal.mp hx; dsimp only; by_cases hp:y=0
              · subst y; rw [he, hh, mul_zero,mul_zero]
              by_cases ht:x=0; subst x; rw [candleN he n 0 (by omega),candleN hh n 0 (by omega),zero_mul,zero_mul]
              rw [h.cups n x (by omega), h y (by omega)]
lemma gains (he:Kind f)(hh:Kind g)(hx:Lap k f g) : PowerSeries.coeff (k+1) (Spring f) - PowerSeries.coeff (k+1) (Spring g)= PowerSeries.coeff (k+1) f-PowerSeries.coeff (k+1) g:=by
    rw [issues he (le_refl _),issues hh (le_refl _)]; unfold Aroma; rw [map_sum,map_sum,← sum_sub_distrib, Finset.sum_eq_single_of_mem 1 (mem_range.mpr (by omega))]; · simp
    intro i hj hp; apply sub_eq_zero.mpr; by_cases h:i=0; subst i;rw [pow_zero,pow_zero]; rw [coeff_smul,coeff_smul,cadets he hh hx i (by omega)]
lemma forecast (v:G)(h:PowerSeries.coeff 0 v=1):∃ a:G,Kind a∧Spring a=v:=by
    suffices h:∀ n,∃ t:G, Kind t ∧ Lap n (Spring t) v by
        choose S ht hc using h; have he : ∀ k m n:ℕ,k≤ m → k≤n → Lap k (S m) (S n) := by
            intro k; induction k with
            | zero=> intro m n e X i hi; rw [Nat.eq_zero_of_le_zero hi,ht m,ht n]
            | succ i ih=> intro j k hj hk n hn; by_cases h:n≤ i; exact ih j k ((by omega)) (by omega) n h
                          have ht':n=i+1:=by omega
                          have he:=gains (ht j) (ht k) (ih j k (by omega) (by omega)); rw [← ht',hc j _ (hn.trans hj), hc k _ (hn.trans hk),sub_self] at he; exact sub_eq_zero.mp he.symm
        let a:= PowerSeries.mk fun i=> PowerSeries.coeff i (S i); refine ⟨a,?_, PowerSeries.ext fun i=>?_⟩; · rw [Kind]; exact (coeff_mk ..).trans (ht _)
        refine (Lap.boots (g:=S i) (k:=i) ?_ i le_rfl).trans (hc i i le_rfl)
        intro j hj; exact (coeff_mk ..).trans (he j j i le_rfl hj j le_rfl)
    intro n; induction n with
    | zero=> have hz : Kind (0:G):= _root_.map_zero _; refine ⟨0,hz,fun i hi=>?_⟩; rw [Nat.eq_zero_of_le_zero hi, covers hz, h]
    | succ k ih=>
       obtain ⟨t,hT,hU⟩:=ih; let c:= PowerSeries.coeff (k+1) v-PowerSeries.coeff (k+1) (Spring t); let a:= t+monomial (k+1) c; have ht :Lap k t a:= fun i hi=>by unfold a; rw [_root_.map_add,PowerSeries.coeff_monomial,if_neg (by omega),add_zero] -- lemma name
       have hv:Kind a:=(ht 0 (by omega)).symm.trans hT; refine ⟨a,hv,fun i hi=>?_⟩
       by_cases he:i≤k; exact ((Lap.boots ht) i he).symm.trans (hU i he)
       have ht': i=k+1:=by omega
       rw [ht']; have hb:= gains hT hv ht; rw [show PowerSeries.coeff (k+1) a=PowerSeries.coeff (k+1) t+c from (by unfold a; rw [map_add,PowerSeries.coeff_monomial]; simp)] at hb
       unfold c at hb; exact sub_right_inj.mp (show PowerSeries.coeff _ (Spring t)-PowerSeries.coeff (k+1) (Spring a)= PowerSeries.coeff _ (Spring t)-PowerSeries.coeff (k+1) v from hb.trans (by abel)) -- type equality
lemma singular (he:Kind f)(hh:Kind g)(hx : Spring f=Spring g): f=g:=by
   suffices H:∀ k, Lap k f g from PowerSeries.ext fun n=> H _ n le_rfl
   intro k; induction k with |zero=>intro i hi;rw [Nat.eq_zero_of_le_zero hi,he,hh]|succ k ih=>
      intro i hi; by_cases h:i ≤ k; exact ih i h;have hp:=gains he hh ih; rw [hx,sub_self] at hp; rw [show i=k+1 by omega]; exact sub_eq_zero.mp hp.symm
def Autumn (f:G): G:= if h: PowerSeries.coeff 0 f=1 then Classical.choose (forecast f h) else 0
lemma fall_1 (hx:PowerSeries.coeff 0 f=1):Kind (Autumn f) ∧ Spring (Autumn f)=f:=by unfold Autumn;rw [dif_pos hx]; exact Classical.choose_spec (forecast f hx)
lemma fall_2 (hx : Kind f): Autumn (Spring f) = f:= singular (fall_1 (covers hx)|>.1) hx (fall_1 (covers hx)|>.2)
lemma sunshine (e:A →ₐ[ℝ] B): Spring (PowerSeries.map e.toRingHom f)= PowerSeries.map e.toRingHom (Spring f):=by
    apply PowerSeries.ext; intro n; simp only [Spring,PowerSeries.coeff_mk, coeff_map]; unfold Aroma; rw [map_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [← map_pow, coeff_smul, coeff_map,coeff_smul]; exact (_root_.map_smul e _ _).symm
end YM.MSbar.Cacao
