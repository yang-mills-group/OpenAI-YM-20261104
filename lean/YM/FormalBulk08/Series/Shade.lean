import YM.FormalBulk08.Series.Canopy

/-!
Send coefficients of a formal series to series and retain the coupling variable, not
substituting anything into g. Used when an independent log-link coordinate is changed
by a perturbative Gauge transformation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Series
open PowerSeries
open scoped BigOperators
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable (f : R →+* PowerSeries S)

def fog (p : PowerSeries R) : PowerSeries S := mk fun i => ∑ j∈Finset.range (i+1), coeff i (f (coeff j p) * X^j)
lemma fog_through (p : PowerSeries R) (n : ℕ) : Through n (fog f p) (∑ j∈Finset.range (n+1),f (coeff j p) * X^j) := fun i hi=> by
  rw [fog,coeff_mk, map_sum]; exact Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hj' => by simp only [Finset.mem_range,not_lt] at hj'; rw [coeff_mul_X_pow',if_neg (by omega)])

private lemma layer (a b : PowerSeries S) (i j : ℕ) : a * X^i * (b * X^j)= a*b*X^(i+j) := by rw [pow_add]; ring

lemma fog_mul (p q : PowerSeries R) : fog f (p*q)= fog f p * fog f q := by
   ext1 n
   rw [(fog_through f _ n).apex, ((fog_through f p n).mul (fog_through f q n)).apex]
   -- lhs as diagonal grouping
   simp_rw [coeff_mul (φ:=p) (ψ:=q),map_sum,Finset.sum_mul,Finset.mul_sum,map_sum,layer]
   -- equality by sum_bij_ne_zero
   have h (i j : ℕ) : ¬i+j ≤ n → coeff n (f (coeff i p) * f (coeff j q) * X^(i+j)) =0 := fun t=> by rw [coeff_mul_X_pow',if_neg t]
   simp_rw [map_mul f]
   rw [Finset.sum_sigma' _ Finset.antidiagonal, ← Finset.sum_product']
   refine Finset.sum_bij_ne_zero (fun i _ _ => i.2) ?_ ?_ ?_ ?_
   · intro a ha _; simp only [Finset.mem_range, Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_product] at *; omega
   · rintro ⟨u,a⟩ ha _ ⟨v,b⟩ hb _ (rfl : a=b); simp only [Finset.mem_sigma,Finset.mem_antidiagonal] at *; congr 1; exact ha.2.symm.trans hb.2
   · intro a ha hn; refine ⟨⟨a.1+a.2,a⟩,?_,hn,rfl⟩
     rw [Finset.mem_sigma]; refine ⟨Finset.mem_range.mpr ?_,Finset.mem_antidiagonal.mpr rfl⟩
     exact Nat.lt_succ_of_le (le_of_not_gt fun t=> hn (h a.1 a.2 t.not_ge))
   intro a ha _
   rw [Finset.mem_antidiagonal.mp (Finset.mem_sigma.mp ha).2]

def changeBy : PowerSeries R →+* PowerSeries S where
   toFun p := fog f p
   map_mul' := fog_mul f
   map_one' := by
      ext1 i
      simp only [fog,coeff_mk,coeff_one (R:=R)]
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]; all_goals simp_all
   map_add' p q := by ext1 n; simp only [fog,coeff_mk,map_add,add_mul,Finset.sum_add_distrib]
   map_zero' := by ext1 i; simp [fog]
lemma liquid (p : PowerSeries R) (n : ℕ) : Through n (changeBy f p) (∑ j∈Finset.range (n+1), f (coeff j p) * X^j) := fog_through f p n
lemma Through.change_congr {p q : PowerSeries R} {n : ℕ} (hp : Through n p q) : Through n (changeBy f p) (changeBy f q) := by
    have he : ∑ j∈Finset.range (n+1), f (coeff j p)*X^j= ∑ j∈Finset.range (n+1), f (coeff j q)*X^j := Finset.sum_congr rfl fun j hj => by rw [hp j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    exact (he ▸ liquid f p n : Through n (changeBy f p) _).trans (liquid f q n).symm
@[simp] lemma change_C (a : R) : changeBy f (C a)=f a := by
   ext1 n;rw [(liquid _ _ n).apex]; congr 1; simp only [coeff_C]; rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]; all_goals simp_all
@[simp] lemma change_X : changeBy f X=X := by
   ext1 n; rw [(liquid _ _ n).apex]; by_cases hn:n=0
   · subst n; simp
   congr 1;simp only [coeff_X]; rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr (by omega))]; all_goals simp_all
lemma change_comp (g : S →+* PowerSeries T) (p : PowerSeries R) : changeBy g (changeBy f p)= changeBy ((changeBy g).comp f) p := by
    apply Through.top;intro n; refine Through.trans (Through.change_congr g (liquid f p n)) ?_
    rw [map_sum];simp_rw [map_mul,map_pow,change_X];
    simpa only [RingHom.comp_apply] using (liquid ((changeBy g).comp f) p n).symm
lemma change_coeff_zero (p : PowerSeries R) : coeff 0 (changeBy f p)= coeff 0 (f (coeff 0 p)) := by rw [(liquid f _ 0).apex]; simp
lemma change_subst {q : PowerSeries R} (hq : coeff 0 q=0) (p : PowerSeries R) (n : ℕ) : Through n (changeBy f (p.subst q)) (∑ j∈Finset.range (n+1), f (coeff j p) * (changeBy f q)^j) := by
    have h := Through.change_congr f ((dict p n).compose (Through.exact_eq q n) hq)
    refine h.trans ?_
    rw [←coe_substAlgHom (tribe hq),map_sum]; change Through n (changeBy f (∑ i∈_, _ : PowerSeries R)) _
    simp_rw [map_sum]; apply Through.finsetSum
    intro i _; rw [coe_substAlgHom]
    simp_rw [subst_mul (tribe hq),subst_pow (tribe hq),subst_X (tribe hq)]
    simp [show (PowerSeries.subst q (C (coeff i p)))= C (coeff i p) from subst_C _,Through.exact_eq]
lemma pure_map (φ : R →+* S) (p : PowerSeries R): changeBy (C.comp φ) p=PowerSeries.map φ p := by
   ext1 n; rw [(liquid _ _ n).apex]; rw [(dict (p.map φ) n).apex]; simp only [RingHom.comp_apply,coeff_map]
lemma change_expan [Algebra ℚ R] [Algebra ℚ S] {p : PowerSeries R} (hp : coeff 0 p=0) : changeBy f (expan p) = expan (changeBy f p) := by
   ext1 n; rw [show expan p = (exp R).subst p from rfl, (change_subst f hp (exp R) n).apex] -- need unfold expan selective
   have h:= til_expan (p:=changeBy f p) (by rw [change_coeff_zero, hp, map_zero, map_zero]) (le_refl n)
   rw [h.apex]
   simp [tray]
lemma change_covelog [Algebra ℚ R] [Algebra ℚ S] {p : PowerSeries R} (hp : coeff 0 p=1) : changeBy f (covelog p) = covelog (changeBy f p) := by
   have h : coeff 0 (changeBy f p)=1 := by rw [change_coeff_zero,hp,map_one,coeff_zero_one]
   apply (expan_inj (by rw [change_coeff_zero,covelog_rank hp,map_zero,map_zero]) (covelog_rank h)).mp
   rw [←change_expan _ (covelog_rank hp),expan_after h,expan_after hp]
lemma change_beam {g : S→+* T} (p : PowerSeries R) : PowerSeries.map g (changeBy f p) = changeBy ((PowerSeries.map g).comp f) p := by
   rw [←pure_map,change_comp]
   have h : changeBy (C.comp g)=PowerSeries.map g := RingHom.ext (pure_map g)
   rw [h]
lemma change_after {g : T→+* R} (p : PowerSeries T) : changeBy f (PowerSeries.map g p)=changeBy (f.comp g) p := by
   rw [←pure_map,change_comp, show (changeBy f).comp (C.comp g) = f.comp g from RingHom.ext (fun x=> by simp)]
end YM.FormalBulk08.Series
