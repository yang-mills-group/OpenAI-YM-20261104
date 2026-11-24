import YM.GradedFar.Moving.Vat

/-!
# Multilinear estimate with genuinely marked columns (compact step)
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I)

lemma priced_leap {X : I→ℂ} {Y : I→Portion ℂ} {t : I→ℂ} {f : I→ℝ} {B : I→ℂ}
    (h : Pays T X Y f p t) (he : Buys T (fun i=> B i-X i) f (p+1)) : Pays T B Y f p t :=
    ⟨h.1, (he.add h.2).congr_left (fun i=> by abel)⟩
lemma pool {x : J→I→ℂ} {F : J→I→PowerSeries ℂ} {L : I→ℝ} {g : I→ℂ} (s : Finset J)
    (h : ∀ j∈s, Pays T (x j) (fun i=> tells (F j i)) L p g) : Pays T (fun i=>∑ j∈s,x j i)
    (fun i=> tells (∑ j∈s,F j i)) L p g := by
  refine ⟨fun j hj=>?_,?_⟩
  · unfold tells; simp only [map_sum]; exact IsBigO.sum (fun k hk=> (h k hk).1 j hj)
  have he i : blend (tells (∑ j∈s,F j i)) p (g i)= ∑ j∈s,blend (tells (F j i)) p (g i) := by
    simp only [blend,tells,map_sum,Finset.smul_sum]; rw [Finset.sum_comm]
  simp_rw [he,← Finset.sum_sub_distrib]; exact IsBigO.sum (fun j hj=> (h j hj).2)
lemma owed {x : J→I→ℂ} {F : J→I→PowerSeries ℂ} {L : I→ℝ} {g : I→ℂ}
    (hg : Buys T g L 1) (ht : Tendsto L T (𝓝 0)) (s : Finset J)
    (h : ∀ j∈s, Pays T (x j) (fun i=> tells (F j i)) L p g) : Pays T (fun i=>∏ j∈s,x j i)
    (fun i=> tells (∏ j∈s,F j i)) L p g := by
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.prod_empty]; refine ⟨Till.const T _,?_⟩; simp [blend,tells]; exact isBigO_zero ..
  | insert j s hj ih => simp_rw [Finset.prod_insert hj, revenue_tells]; exact Pays.joint T hg ht (h _ (Finset.mem_insert_self ..)) (ih fun j hj=>h _ (Finset.mem_insert_of_mem hj))

section assembly
variable (A : ℕ→Point G d n) (S : Guard G d) (u : Fin n→Sec G d)
abbrev stockp (X : Point G d n) := X
abbrev shop (X : ℕ→ Point G d n) (a : Fin n→ Sec G d) := Reg.Point.story X a
abbrev one_grade (n d : ℕ) : Fin n → ℕ := fun _=>d
abbrev fcols (S : Guard G d) (u : Fin n→Sec G d) : Columns G (one_grade n d) := fun i q=> coeff q S (u i)
omit I T in
lemma against : shop (status S A) u= ∑ c:Choices G (one_grade n d),
      factors c (fcols S u) * shop A (basisInputs c) := by
    ext1 i; simp_rw [map_sum, shop, Reg.Point.story, factors,Dframe.Constants.admits,coeff_mk,seen]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j hj=>?_ ; exact basis_spelling (d:=one_grade n d) (A (j none)) (pulseU j S u)
end assembly

lemma coord_buys {x : I→Module.End ℂ (Sec G d)} {F:I→ℝ} (q : Toon G d) (u : Sec G d)
    (h : Buys T (fun i=> chairs G d (x i)) F p) : Buys T (fun i=>coord q (x i u)) F p := by
    obtain ⟨C,hC,h⟩:= h.exists_pos; apply IsBigO.of_bound (C*‖chair G d u‖)
    filter_upwards [h.bound] with i hi
    have hp: ‖coord q (x i u)‖ ≤ ‖chair G d (x i u)‖:= norm_le_pi_norm (f:=chair G d (x i u)) q
    apply hp.trans; rw [← appointed]; exact (ContinuousLinearMap.le_opNorm ..).trans
      ((mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans_eq (by ring))
lemma priced_column {L : I→ℝ} {t : I→ℂ} {x : I→FieldEnd G d} {X : I→Guard G d}
    (h : Pays T (fun i=> chairs G d (x i)) (fun i=> names (X i)) L p t) (q : Toon G d) (u : Sec G d) :
    Pays T (fun i=> coord q (x i u)) (fun i j=> coord q (coeff j (X i) u)) L p t := by
  refine ⟨fun j hj=>coord_buys T (x:=fun i=>coeff j (X i)) q u (h.1 j hj),?_⟩
  let A i:= ∑ j∈Finset.range (p+1), t i^j • coeff j (X i)
  have he := h.2
  have hu i : blend (names (X i)) p (t i)= chairs G d (A i) := by unfold A blend names; rw [map_sum]; simp_rw [_root_.map_smul]
  simp_rw [hu,← map_sub] at he
  refine (coord_buys T (x:=fun i=> x i-A i) q u he).congr_left (fun i=>?_)
  simp only [LinearMap.sub_apply,map_sub,A,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,_root_.map_smul, blend]

/-- Arithmetic buys any marked finite ensemble on this precise MLM. One price
for the ensemble. -/
lemma titles {F : I→Point G d n} (L:I→ℝ) (t:I→ℂ) (hv:Tendsto L T (𝓝 0)) (ht : Buys T t L 1)
    (S : I→Guard G d) (A : I→ℕ→Point G d n) (x : I→FieldEnd G d) (u : Fin n→Sec G d)
    (he : Pays T (fun i=>chairs G d (x i)) (fun i=> names (S i)) L p t)
    (hp : ∀ a : Fin n→Sec G d,Pays T (fun i=>F i a) (fun i=> tells (shop (A i) a)) L p t) :
    Pays T (fun i=> F i (x i∘u)) (fun i=> tells (shop (status (S i) (A i)) u)) L p t := by
  have hx i : F i (x i∘u)=∑ c:Choices G (one_grade n d), combo (d:=one_grade n d) (x i∘u) c * F i (basisInputs c) := basis_spelling (d:=one_grade n d) _ _
  simp_rw [hx,against]; apply pool; intro j hj; simp_rw [revenue_tells]
  refine Pays.joint T ht hv ?_ (hp _); unfold combo factors; apply owed T ht hv; intro a ha; unfold mode; unfold tells; simp_rw [coeff_mk]; exact priced_column T he (j a) _
end
end YM.FVA2.GradedFar.Moving
