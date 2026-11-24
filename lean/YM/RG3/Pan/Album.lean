import YM.RG3.Axial.Revalue
import YM.Push.FREE_RESOLVENT.Powers

/-!
# Moving any true group path inside a real smooth chart

Finite polynomial bounds (also for arbitrarily small width choices). The
chart need only be on germ data, not global and even not on a constant
neighborhood for path letters. Covers chains that can include boundaries,
faces, inverses, chords read via recover and *changing transport paths*.
At no point assume that curvature sums across these chains satisfy a linear
Bianchi identity. Like `assembled_jets` for the global travel prices: don't
pay `norm_mul_le` many times with degree zero factors!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan
open FreeResolvent TestD Function Matrix Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : E} {k j : ℕ} {A t : ℝ}

/-- Control only for HITS, i.e. DON'T pay A repeatedly for zeroth
variations. `t` can give e.g. one real threshold per hit. -/
structure GroupHit (k : ℕ) (A t : ℝ) (u : E→G.El) (x : E) : Prop where
  smooth : ContDiffAt ℝ k (G.mat ∘ u) x
  hit j : 1 ≤ j → j ≤ k → ‖iteratedFDeriv ℝ j (G.mat ∘ u) x‖ ≤ A*t^j

 lemma GroupHit.backtrack {u : E→G.El} (h : GroupHit k A t u x) (hA : 0 ≤ A) (ht : 0 ≤ t) : GroupHit k A t (fun v=> (u v)⁻¹) x := by
  let P: G.Mat→L[ℝ] G.Mat:= (starL' ℝ : G.Mat≃L[ℝ] G.Mat).toContinuousLinearMap
  constructor
  · exact P.contDiff.contDiffAt.comp _ h.smooth
  intro j hj he
  have hx:= P.iteratedFDeriv_comp_left h.smooth (i:=j) (by exact_mod_cast he)
  change ‖iteratedFDeriv ℝ j (P ∘ G.mat ∘ u) x‖ ≤ _
  erw [hx]
  apply FreeResolvent.Affine.slot_op (by positivity)
  intro i hi
  change ‖star ((iteratedFDeriv ℝ j (G.mat∘u) x) i)‖ ≤ _
  rw [Matrix.star_eq_conjTranspose,Matrix.frobenius_norm_conjTranspose]
  apply (ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ hi).trans
  simpa using (h.hit j hj he)

/-- Word of group functions, evaluated in left-to-right order. -/
def bands {ι : Type*} (u : ι→ E→ G.El) (p : List ι) (x : E) := (p.map (fun i=> u i x)).prod
 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] lemma bands_nil {ι} (u : ι→ E→ G.El) : bands u [] = fun _ => 1 := rfl
 omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] lemma bands_cons {ι} (u : ι→E→G.El) (i) (l) : bands u (i::l) = fun x=>u i x*bands u l x := rfl

/-- pay each expansion up to k for choices of every subvariation; polymer
length only enters polynomially. Exact scale factor `t` per variation -/
def light (G : Gauge) (k j m : ℕ) (A t : ℝ) := ‖(1:G.Mat)‖*(1+2^k*A*m)^j * t^j
lemma light_nn (G : Gauge) (k j m : ℕ) (hA : 0 ≤ A) (ht : 0 ≤ t) : 0 ≤ light G k j m A t:= by unfold light; positivity

/-- Strengthened assembled estimate for arbitrary germ words with polynomial
price at each differential order and no analyticity hypotheses at all. -/
theorem chorus {ι : Type*} (u : ι→E→G.El) (p : List ι) (hA : 0≤A) (ht : 0≤t) (h : ∀ i∈p, GroupHit k A t (u i) x):
    ContDiffAt ℝ k (G.mat∘bands u p) x ∧ ∀ j ≤ k, ‖iteratedFDeriv ℝ j (G.mat∘bands u p) x‖ ≤ light G k j p.length A t:= by
  induction p with
  | nil =>
    refine ⟨contDiffAt_const,fun j _=>?_⟩; rw [bands_nil]; simp only [Function.comp_def,G.mat_one]
    cases j; simp [light]
    rename_i j _; rw [iteratedFDeriv_succ_const]; exact (by simpa using light_nn G k (j+1) 0 hA ht)
  | cons a p H =>
    obtain ⟨hd,hZ⟩:= H (fun i hi=>h _ (List.mem_cons_of_mem _ hi))
    have hc:= h a (List.mem_cons_self)
    let U:=G.mat∘u a; let V:=G.mat∘bands u p
    refine ⟨hc.smooth.mul hd,fun j hj=>?_⟩
    by_cases h0 : j=0
    · subst j; rw [norm_iteratedFDeriv_zero, Function.comp_apply]
      have e:= Gauge.frob_mul_eq (1:G.Mat) _ (G.mat_mul_star (bands u (a::p) x))
      simp only [one_mul] at e
      simpa [light] using e.le
    classical
    let n:=p.length; let c:ℝ:=2^k*A
    let B:ℝ:=1+c*n; let W:=‖(1:G.Mat)‖
    have hc': 0 ≤ c:=by unfold c; positivity
    have hb: 1 ≤ B:= le_add_of_nonneg_right (by positivity)
    have hW : 0≤W:= norm_nonneg _
    apply FreeResolvent.Affine.list_op (light_nn G k j _ hA ht)
    intro l v he hv
    let q:=pureR l; let O (m : Masks l):= jet v U (lo l m) x * jet v V (hi l m) x
    change ‖jet v (fun y=>U y*V y) _ _‖ ≤ _
    have hr:= leibniz (A:=U) (B:=V) v (ContinuousLinearMap.mul ℝ _) l (smooth_of_le hc.smooth (he.trans_le hj)) (smooth_of_le hd (he.trans_le hj))
    change jet v (fun y=>U y*V y) _ _=_ at hr
    rw [hr]; change ‖∑ m, O m‖ ≤ _
    have hh (F:E→G.Mat) (L:List (Fin j)): ‖jet v F L x‖ ≤ ‖iteratedFDeriv ℝ L.length F x‖ := by
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_of_le_one_right (norm_nonneg _) ?_)
      simpa [Function.comp_def] using! (Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> hv (L.get i)) (s:=Finset.univ))
    have hh' : ‖O q‖ ≤ light G k j n A t:= by
      unfold O q; rw [lo_right,hi_right,zeroth,Gauge.mul_frob_eq (U x) _ (G.mat_star_mul (u a x))]; exact (hh V l).trans ((hZ _ (he.trans_le hj)).trans_eq (congr_arg (fun j=> light G k j n A t) he))
    have hm (m : Masks l) (hm:m ∈ Finset.univ.erase q) : ‖O m‖ ≤ A*W*B^(j-1) * t^j := by
      let i:=(lo l m).length; let b:=(hi l m).length
      have hj':i+b=j:=(lengths _ _).trans he
      have hi': 0 < i :=List.length_pos_iff.mpr (lo_ne (show m≠pureR l from Finset.ne_of_mem_erase hm))
      refine (norm_mul_le ..).trans ((mul_le_mul ((hh ..).trans (hc.hit i hi' (by omega))) ((hh ..).trans (hZ b (by omega))) (norm_nonneg _) (mul_nonneg hA (pow_nonneg ht _))).trans ?_)
      change A*t^i * (W*B^b*t^b) ≤ _
      calc
        _ = A*W*B^b*t^j := by rw [← hj', pow_add]; ring
        _ ≤ _ := by gcongr; omega
    have hj': j=j-1+1:= by omega
    have ho : (∑ m ∈ Finset.univ.erase q, ‖O m‖) ≤ c*W*B^(j-1)*t^j := by
      refine (Finset.sum_le_sum hm).trans ?_
      simp only [Finset.sum_const,nsmul_eq_mul]; unfold c
      have he' : ↑(Finset.univ.erase q).card ≤ (2:ℝ)^k:= by
        exact_mod_cast ((Finset.card_le_univ _).trans ((TestD.card l).le.trans (pow_le_pow_right₀ (by norm_num) (he.trans_le hj))))
      refine (mul_le_mul_of_nonneg_right he' ?_).trans_eq (by ring)
      positivity
    refine (norm_sum_le ..).trans ?_
    rw [← Finset.add_sum_erase (s:=Finset.univ) (fun m => ‖O m‖) (Finset.mem_univ q)]; apply (add_le_add hh' ho).trans
    change W*(1+c*n)^j*t^j + c*W*B^(j-1)*t^j ≤ W*(1+c*↑(n+1))^j*t^j
    rw [Nat.cast_add_one,mul_add,mul_one, ← add_assoc, ← show B=1+c*↑n from rfl]
    have he' : B^j=B^(j-1)*B:=by rw [←pow_succ,←hj']
    have he'' : (B+c)^j=(B+c)^(j-1)*(B+c):=by rw [←pow_succ,←hj']
    calc
      _ = W*(B^(j-1)*(B+c))*t^j := by rw [he']; ring
      _ ≤ W*((B+c)^(j-1)*(B+c))*t^j := by gcongr; exact le_add_of_nonneg_right hc'
      _ = _ := by rw [he'']

end YM.RG3.Pan
