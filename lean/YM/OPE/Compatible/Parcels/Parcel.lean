import YM.OPE.Compatible.Parcels.Rails
/-!
# Taylor with free-kernel call; polymer norm is polynomial on both sides
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset
open scoped Topology BigOperators Classical
variable {I J:Type*}[Fintype I][DecidableEq I] {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
variable {s f:Shift I→J→Y}{w:J→ℝ}{v:Shift I→ℝ}{a U:ℝ}{m n L:ℕ}
def Abstemious (n:ℕ)(v:Shift I→ℝ): Prop := ∀ i∈trail I n, ∑' x, v x*pine i x=0
def courier (f:Shift I→J→Y) (v:Shift I→ℝ):J→Y:=fun j=>∑' i,v i • f i j
structure Survey (J:Type*) (s:Shift I→ J→ Y)(L n m:ℕ)(U:ℝ)(w:J→ℝ): Prop where
    overall (x: Shift I) : L<size x→ Sack w (s x) (((size x:ℝ)/L)^m *U)
    polish (l:List I) : l.length ≤ n→ ∀ x,size x ≤ L→ Sack w (dvol l s x) (U/(L:ℝ)^l.length)
variable (hP:Survey J f L n m U w) (ht: n≤m)(hu:1≤ w)(hv:0≤U)(he:0<L)
include hP ht hu hv he
omit [CompleteSpace Y] in
private lemma carry_wide (x:Shift I) :
    let c:ℝ:= (1+↑(trail I n).card:ℝ)*U/(L:ℝ)^n
    Sack w (f x - sketch n f x) (poise m x * c):=by
    intro c
    have hl:1 ≤ (L:ℝ):=by exact_mod_cast he
    have hb:0≤ w:= fun i=> zero_le_one.trans (hu i); have hk:0 < (L:ℝ):=by linarith
    have hx: (size x:ℝ)^n ≤ poise m x:=by
        unfold poise; have he: (size x:ℝ)≤notch x:=by unfold notch; push_cast; linarith
        exact (pow_le_pow_left₀ (Nat.cast_nonneg _) he n).trans (pow_le_pow_right₀ (show 1≤ (notch x:ℝ) by exact_mod_cast notch_one x) ht)
    by_cases H:size x ≤ L
    · let V:= f-sketch n f
      change Sack w (V x) _; apply (polynomial_walk n (show 0 ≤ U/(L:ℝ)^n by positivity) hb (f:=V) (fun j hj=>?_) (fun l hl y hy=>?_) x H).tips
      · unfold c; apply (mul_le_mul_of_nonneg_right hx (by positivity)).trans; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (poise_one m x)); gcongr; exact le_mul_of_one_le_left hv (by simp)
      · unfold V; rw [run_sub,sketch_hits _ _ hj,sub_self]
      unfold V; rw [run_sub,sketch_fizz l f y hl.ge,sub_zero]; simpa [hl] using hP.polish l hl.le y hy
    have hs := Nat.lt_of_not_ge H; apply ((hP.overall x hs).subsumes (long_sketch ht hl hv hb (fun l hp=> hP.polish l hp.le 0 (by simp [size])) x (show (L:ℝ)≤size x by exact_mod_cast hs.le)) hb).tips
    let v:ℝ:=1+(trail I n).card; have hp:0 ≤ v:=by unfold v; positivity
    calc
       _ = ((size x:ℝ)/L)^m * (v*U):=by unfold v; ring
       _ ≤ (poise m x /(L:ℝ)^n) * (v*U):=by
            rw [div_pow]; apply mul_le_mul_of_nonneg_right _ (mul_nonneg hp hv)
            exact div_le_div₀ (by unfold poise; positivity) (pow_le_pow_left₀ (Nat.cast_nonneg _) (by unfold notch; push_cast; linarith) _) (by positivity) (pow_le_pow_right₀ hl ht)
       _ = _:=by dsimp only [c,v]; ring
lemma letter_charge (h:Sack (poise m) v a)(hz:Abstemious n v): Sack w (courier f v) ((1+(trail I n).card:ℝ)*U/(L:ℝ)^n * a):=by
    let c:ℝ := (1+(trail I n).card:ℝ)*U/(L:ℝ)^n
    let H:= sketch n f; let g x := f x - H x; have hg := Sack.carried (T:=g) h (carry_wide hP ht hu hv he) (show 0≤ c by unfold c; positivity)
    have hp : Sack w (courier g v) (a*c):=hg.draw hu
    -- tsum on Sketch exact 0, so equals
    have hh (j) : HasSum (fun x=> v x • H x j) 0:=by
        let s (i:Multiset I)(x:Shift I):Y:= (v x*pine i x) • dvol i.toList f 0 j
        have he (i:Multiset I)(hi:i∈trail I n) : HasSum (s i) 0:=by
           have hg: i.card≤m:= ((trailed _ n).1 hi).le.trans ht
           have hk(x:Shift I): ‖pine i x‖ ≤ poise m x:=by
               apply (pine_paths ..).trans; apply le_trans (b:= ((notch x):ℝ)^i.card); unfold notch; gcongr; apply (show size x≤1+size x by omega)
               exact pow_le_pow_right₀ (show 1≤ ((notch x):ℝ) by exact_mod_cast notch_one x) hg
           have hb: Summable fun x:Shift I => v x * pine i x:=by
               apply h.2.1.of_norm_bounded; intro x; rw [norm_mul,mul_comm]; exact mul_le_mul_of_nonneg_right (hk x) (norm_nonneg _)
           unfold s; rw [← zero_smul ℝ (dvol i.toList f 0 j), ← hz i hi]; exact hb.hasSum.smul_const _
        have hH (x) : v x • H x j = ∑ i∈trail I n,s i x:= by unfold H sketch; rw [Finset.sum_apply,Finset.sum_apply, Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=>by unfold s; rw [Pi.smul_apply,smul_smul]
        simp_rw [hH]; simpa only [Finset.sum_const_zero] using hasSum_sum fun i hi=> he i hi
    have hx : courier f v = courier g v:=by
        ext1 j; unfold courier; rw [show (fun x=>v x • f x j)= (fun x=> v x • g x j + v x • H x j) from ?_]; swap; · funext x; unfold g; rw [Pi.sub_apply,smul_sub, sub_add_cancel]
        rw [Summable.tsum_add, (hh j).tsum_eq,add_zero]
        · exact (hg.collectible hu j).of_norm
        exact (hh j).summable
    rw [hx]; exact hp.tips (by unfold c; rw [mul_comm a])
end YM.OPE.Flume
