import YM.Contacts.Pulse.Pour
/-! evaluate finite bows along unit and flat review. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.Pulse.Form
open Function Filter Set Finset PowerSeries
open scoped Topology BigOperators Classical NNReal
variable {α X Y : Type*}
namespace Grid
section
variable [CommRing X][Algebra ℝ X]
abbrev Scrolls (X : Type*) := PowerSeries (PowerSeries X)
-- finite angular sweep

def Fixed (f : Scrolls X): Prop:= ∀ i j:ℕ,3*i<j→ coeff j (coeff i f)=0
variable {f g : Scrolls X}{a b n:ℕ}
def rock (x:X) (n:ℕ)(f:PowerSeries X):= ∑ i∈Finset.range (n+1), x^i * coeff i f
def mature (x:X)(f:Scrolls X): PowerSeries X:= PowerSeries.mk fun i=> rock x (3*i) (coeff i f)
lemma Fixed.zero : Fixed (0: Scrolls X) := fun _ _ _=> by simp
lemma Fixed.one : Fixed (1:Scrolls X):= fun i j h=> by rw [coeff_one]; split <;> simp [coeff_one, show j≠0 by omega]
lemma Fixed.add (h:Fixed f)(hg:Fixed g): Fixed (f+g):= fun i j k=> by simp only [map_add]; rw [h i j k,hg i j k,add_zero]
lemma Fixed.scale (h:Fixed f)(c:ℝ): Fixed (c • f):= fun i j k=> by simp only [coeff_smul]; rw [h i j k,smul_zero]
lemma Fixed.mul (h:Fixed f)(k:Fixed g): Fixed (f*g) := by
   intro i j he; rw [coeff_mul,map_sum]; apply sum_eq_zero; intro u hu; rw [coeff_mul]; apply sum_eq_zero; intro v hv;
   have hu:=mem_antidiagonal.mp hu; have hv:=mem_antidiagonal.mp hv
   by_cases hh: 3*u.1<v.1; · rw [h u.1 v.1 hh,zero_mul]
   rw [k u.2 v.2 (by omega),mul_zero]
lemma Fixed.pow (h:Fixed f) (n:ℕ): Fixed (f^n):= by induction n with
                                                                      | zero=> rw [pow_zero]; exact Fixed.one
                                                                      | succ n ih=>rw [pow_succ]; exact ih.mul h
lemma Fixed.expand (h:Fixed f)(n:ℕ): Fixed (expansion f n) := fun i j k=> by unfold expansion; rw [map_sum,map_sum]; exact sum_eq_zero fun v _=> ((h.pow v).scale _) _ _ k
lemma Fixed.breathe (h:Fixed f): Fixed (breath f):= fun i j k=>by rw [breath,coeff_mk]; exact (h.expand i) _ _ k
variable (x:X)
lemma rock_zero (f: PowerSeries X): rock 0 n f=coeff 0 f:= by unfold rock; rw [sum_range_succ']; simp
lemma rock_prod (f g : PowerSeries X) (h:∀ i : ℕ, a < i→coeff i f=0)(hk:∀ i : ℕ,b < i→ coeff i g=0)(hn:a+b=n): rock x n (f*g)=rock x a f*rock x b g:= by
  simp_rw [rock,coeff_mul,mul_sum]; let z (i:ℕ×ℕ):= (x^i.1*coeff i.1 f)*(x^i.2*coeff i.2 g); let s:= (Finset.range (n+1)).biUnion antidiagonal
  calc
    _ = ∑ i∈s,z i:= by
      unfold s; rw [sum_biUnion]; swap
      · intro i hi j hj hf; apply Finset.disjoint_left.mpr; intro w hu hv; exact hf ((mem_antidiagonal.mp hu).symm.trans (mem_antidiagonal.mp hv))
      apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j hj; rw [← mem_antidiagonal.mp hj,pow_add]; unfold z; ring
    _ = ∑ i∈ Finset.range (a+1) ×ˢ Finset.range (b+1), z i := by
       symm; refine sum_subset (fun i hi=>?_) (fun i hi hk'=>?_);
       · obtain ⟨hx,h⟩:=mem_product.mp hi; rw [Finset.mem_range] at hx h; exact mem_biUnion.mpr ⟨i.1+i.2,Finset.mem_range.mpr (by omega),mem_antidiagonal.mpr rfl⟩
       simp only [mem_product,Finset.mem_range,not_and,not_lt] at hk'; by_cases he : i.1≤a
       · have := hk' (by omega); unfold z; rw [hk _ (by omega)]; ring
       unfold z; rw [h _ (by omega)]; ring
    _ = _ := by rw [sum_product]; simp_rw [sum_mul]; unfold z; rw [sum_comm]
lemma matures_times (h:Fixed f)(hg:Fixed g): mature x (f*g)=mature x f*mature x g:=by
   apply PowerSeries.ext; intro n; rw [coeff_mul]; simp only [mature,coeff_mk,coeff_mul]; conv_lhs => unfold rock; simp only [map_sum,mul_sum]
   rw [sum_comm]; apply sum_congr rfl; intro i hi; exact rock_prod x (n:=3*n) _ _ (h i.1) (hg i.2) (by have := mem_antidiagonal.mp hi; omega)
lemma matures_scale (f: Scrolls X)(a:ℝ): mature x (a • f)= a • mature x f:=by apply PowerSeries.ext; intro i; simp only [mature,coeff_smul,coeff_mk,rock,mul_smul_comm,smul_sum]
lemma matures_one: mature x (1:Scrolls X)=1:= by apply PowerSeries.ext; intro i; rw [mature,coeff_mk,coeff_one]; split <;> (rename_i h; simp_all [coeff_one,rock])
lemma matures_pow (h: Fixed f)(n:ℕ): mature x (f^n)= mature x f ^ n:= by induction n with
 | zero=> simp [matures_one]
 | succ n ih=>rw [pow_succ,matures_times x (h.pow n) h,ih,pow_succ]
lemma size_up (f:Scrolls X): coeff n (mature x f)=rock x (3*n) (coeff n f):= by simp [mature]
lemma breath_mature (h: Fixed f): breath (mature x f)= mature x (breath f):= by
  apply PowerSeries.ext; intro n; rw [size_up]; simp_rw [breath,coeff_mk,expansion,map_sum, ← matures_pow x h]; simp only [coeff_smul, size_up,rock,map_sum,mul_smul_comm, smul_sum, mul_sum]; rw [sum_comm];
end
end Grid
section
variable [Fintype α] (g:α→α→ℝ) {F:ℕ→ Rack α}
lemma remains (h:Snug F): Grid.Fixed (sermon g F):= fun i j hj=> by
   rw [sermon,coeff_mk,coeff_mk,stage]; apply sum_eq_zero; intro _ _; rw [h.timed g _ _ _ (by omega),verse_quiet]
end
open Grid
variable [Fintype α] (g:α→α→ℝ)
variable (F:ℕ→ Rack α)
-- rank-zero kept for normalized exponential calculation finite, arbitrary padded elsewhere.
omit [Fintype α] in
def massaged (g:α→α→ℝ)(F:ℕ→ Rack α) (e:ℕ)(r:ℕ) := ∑ i ∈ Finset.range (3*e+1),gathering g F i e r
-- The construction below applies to an arbitrary index type α.
def clouds (F:ℕ→ Rack α) : PowerSeries (Plate α):= PowerSeries.mk fun e=>stage e (F e)
lemma mature_zero : mature 0 (sermon g F)=clouds F:= by apply PowerSeries.ext; intro n; simp only [mature,coeff_mk,rock_zero,sermon,gathering_start,clouds]
lemma mature_one : mature 1 (sermon g F)=clouds (massaged g F):= by
   apply PowerSeries.ext; intro n; simp only [sermon,mature,coeff_mk,clouds,stage,massaged,rock,one_pow,one_mul,verse_sum]
   rw [sum_comm]
-- exp((1/2)Δ) on each positive-order normalized series, comparison engine uses
-- post facto bounds to trim the series. use eventually zero for any padding ≥3e
lemma storms (h:Snug F) (i e:ℕ): coeff i (coeff e (breath (sermon g F)))= stream g (coeff e (breath (clouds F))) i:= by
  have hx:coeff 0 (coeff e (breath (sermon g F))) = coeff e (breath (clouds F)):= by rw [← mature_zero g F,breath_mature _ (remains g h),size_up,rock_zero]
  rw [show coeff i _ = _ from fireplace g F h i e,hx]
lemma wick_heat_finite (h:Snug F) (n e:ℕ) (he:3*e≤ n):
    coeff e (breath (clouds (massaged g F))) = ∑ i∈ Finset.range (n+1), stream g (coeff e (breath (clouds F))) i:= by
  rw [← mature_one g F, breath_mature _ (remains g h),size_up,rock]; simp_rw [← storms g F h]; simp only [one_pow,one_mul]
  apply sum_subset (by intro i hi; rw [Finset.mem_range] at hi ⊢; omega); exact fun i _ hi=> (remains g h).breathe _ _ (by simp only [Finset.mem_range] at hi; omega)
lemma wick_heat_zero (h:Snug F) (n e:ℕ) (he:3*e<n): stream g (coeff e (breath (clouds F))) n=0:= by rw [← storms g F h]; exact (remains g h).breathe _ _ he
end YM.Pulse.Form
