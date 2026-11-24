import YM.Integration.SelectedCofactorCancellationHaar
import YM.Integration.SelectedCofactorCancellationReadout

/-! Product Haar disintegration at an actual lattice edge and absolute
summability over rooted finite packets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorProductHaar
open Function Finset MeasureTheory Lattice Wilson
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}

abbrev Outside (e : Edge (Site n)) := {j : Edge (Site n) // j ≠ e}

def exteriorPrior (G : Gauge) (e : Edge (Site n)) : Measure (Outside e → G.El) :=
  Measure.pi (fun _ => G.probHaar)

/-- Fill the link temporarily by the identity before taking its Haar integral. -/
def anchor (e : Edge (Site n)) (y : Outside e → G.El) : Config G n :=
  fun j => if h : j = e then 1 else y ⟨j, h⟩

/-- Exact Fubini decomposition on the original product Haar prior. -/
theorem edge_disintegration {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : Edge (Site n)) (f : Config G n → E) (hf : Integrable f (prior G n)) :
    Integrable (fun y => ∫ u, f (update (anchor e y) e u) ∂G.probHaar) (exteriorPrior G e) ∧
      (∫ U, f U ∂prior G n) = ∫ y, ∫ u, f (update (anchor e y) e u)
      ∂G.probHaar ∂exteriorPrior G e := by
  let X := {j : Edge (Site n) // j = e}
  let K := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge (Site n) => G.El) (· = e)
  let r := Measure.pi (fun _ : X => G.probHaar)
  let s := exteriorPrior G e
  haveI : IsFiniteMeasure r := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : X => G.probHaar)))
  haveI : IsFiniteMeasure s := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Outside e => G.probHaar)))
  haveI : SFinite r := inferInstanceAs (SFinite (Measure.pi (fun _ : X => G.probHaar)))
  haveI : SFinite s := inferInstanceAs (SFinite (Measure.pi (fun _ : Outside e => G.probHaar)))
  have ht : MeasurePreserving K (prior G n) (r.prod s) := by
    convert! measurePreserving_piEquivPiSubtypeProd (α := fun _ : Edge (Site n) => G.El)
      (fun _ => G.probHaar) (· = e) using 1
    unfold r s exteriorPrior
    congr
    apply Subsingleton.elim
  letI : Unique X := ⟨⟨⟨e, rfl⟩⟩, fun x => Subtype.ext x.property⟩
  let T := MeasurableEquiv.piUnique (fun _ : X => G.El)
  have he : MeasurePreserving T.symm G.probHaar r :=
    (measurePreserving_piUnique (fun _ : X => G.probHaar)).symm
  have hi : Integrable (fun z => f (K.symm z)) (r.prod s) :=
    (ht.symm.integrable_comp_emb K.symm.measurableEmbedding).2 hf
  have hinner (y : Outside e → G.El) :
      (∫ a, f (K.symm (a,y)) ∂r) = ∫ u, f (update (anchor e y) e u) ∂G.probHaar := by
    rw [← he.integral_comp' (fun x => f (K.symm (x,y)))]
    apply integral_congr_ae
    refine ae_of_all _ fun u => congrArg f ?_
    funext j
    by_cases h : j = e
    · subst j
      rw [update_self]
      exact congr_fun (congr_arg Prod.fst (K.apply_symm_apply (T.symm u,y))) ⟨e,rfl⟩
    rw [update_of_ne h]
    change _ = (if h : j = e then 1 else y ⟨j,h⟩)
    rw [dif_neg h]
    exact congr_fun (congr_arg Prod.snd (K.apply_symm_apply (T.symm u,y))) ⟨j,h⟩
  refine ⟨hi.integral_prod_right.congr (ae_of_all _ hinner), ?_⟩
  rw [← ht.symm.integral_comp' f, integral_prod_symm _ hi]
  exact integral_congr_ae (ae_of_all _ hinner)

/-- The same unrooted product pays once for every possible root. -/
def packetWeight (a : ℕ → ℝ) (p : ℕ × Finset ℕ) : ℝ :=
  if p.1 ∈ p.2 then ∏ j ∈ p.2, a j else 0

theorem packetWeight_summable {a : ℕ → ℝ} (hn : ∀ i, 0 ≤ a i) (ha : Summable a) :
    Summable (packetWeight a) := by
  let g (p : Finset ℕ × ℕ) := packetWeight a (p.2, p.1)
  have h0 (p) : 0 ≤ g p := by
    unfold g packetWeight
    split
    · exact prod_nonneg fun i _ => hn i
    exact le_rfl
  have hfin (s : Finset ℕ) :
      HasSum (fun i => g (s,i)) (∑ i ∈ s, g (s,i)) :=
    hasSum_sum_of_ne_finset_zero fun i hi => by simp [g, packetWeight, hi]
  have hc (s : Finset ℕ) : (∑' i, g (s,i)) = (s.card : ℝ) * ∏ j ∈ s, a j := by
    rw [(hfin s).tsum_eq]
    calc
      _ = ∑ _i ∈ s, ∏ j ∈ s, a j := Finset.sum_congr rfl (fun i hi => if_pos hi)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have H : Summable g := (summable_prod_of_nonneg h0).2 ⟨fun s => (hfin s).summable, by
    refine (summable_finsetProd_of_summable_nonneg (fun i => mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hn i))
      (ha.mul_left 2)).of_nonneg_of_le (fun s => tsum_nonneg fun i => h0 (s,i)) ?_
    intro s
    rw [hc, Finset.prod_mul_distrib, Finset.prod_const]
    apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _ => hn i)
    exact_mod_cast (Nat.lt_two_pow_self (n := s.card)).le⟩
  exact H.prod_symm

end YM.Integration.SelectedCofactorProductHaar
end
