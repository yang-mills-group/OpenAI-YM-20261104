import YM.WilsonMS.Stencil.MixedJets
/-!
# At the first disagreement only the Jacobian operates

Results with actual derivative factorials. At finite jets only. Use to update
connection integrands.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.TaylorRules
open Function Filter Set MeasureTheory
open Analysis Tensor
open scoped Topology ContDiff BigOperators Classical
variable {E X F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : E} {x : X} {k n : ℕ} {S : Set X}

section curve
variable [CompactSpace S] {f g : E × X → F}

lemma path_jet (h : ∀ v ∈ S, ContDiffAt ℝ (↑k) f (p, v)) (v : S) (u : Fin k → E) :
    iteratedFDeriv ℝ k (Curves.along S f) p u v = iteratedFDeriv ℝ k (fun x => f (x, v.val)) p u := by
  let L := ContinuousMap.evalCLM ℝ v (M := F)
  have ht : L ∘ Curves.along S f =ᶠ[𝓝 p] fun x => f (x, v.val) :=
    (Curves.remain_on h).mono fun _ hv => hv v
  have hp := (ht.iteratedFDeriv ℝ k).eq_of_nhds
  rw [L.iteratedFDeriv_comp_left (Curves.contDiff_along h) le_rfl] at hp
  exact congr_arg (fun W : Tensor.T E F k => W u) hp

lemma agree_path (h : ∀ v ∈ S, ContDiffAt ℝ (↑k) f (p, v)) (hf : ∀ v ∈ S, ContDiffAt ℝ (↑k) g (p, v))
    (he : ∀ v ∈ S, Agree k p (fun x => f (x, v)) (fun x => g (x, v))) :
    Agree k p (Curves.along S f) (Curves.along S g) := by
  refine ⟨Curves.contDiff_along h, Curves.contDiff_along hf, fun i hi => ?_⟩
  ext x v
  rw [path_jet (fun v hv => (h v hv).of_le (Nat.cast_le.mpr hi)),
    path_jet (fun v hv => (hf v hv).of_le (Nat.cast_le.mpr hi)), (he v.val v.property).same i hi]
end curve

section late
variable {f g : E → F} {u : F → X}

private lemma parts_small (c : OrderedFinpartition n) (h : 1 < c.length) (i) : c.partSize i < n := by
  letI : Nontrivial (Fin c.length) := Fintype.one_lt_card_iff_nontrivial.mp (by simpa using h)
  obtain ⟨j, hj⟩ := exists_ne i (α := Fin c.length)
  have he :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := c.partSize) (Finset.subset_univ { j, i })
      (by
        intros
        omega)
  have H : ∑ i, c.partSize i = n := by simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
  rw [H] at he
  apply lt_of_lt_of_le (lt_add_of_pos_left _ (c.partSize_pos j))
  simpa [hj] using he

lemma stationary {f g : E → F} (hf : ContDiffAt ℝ (↑(k + 1 : ℕ)) f p)
    (hg : ContDiffAt ℝ (↑(k + 1 : ℕ)) g p) (hu : ContDiffAt ℝ (↑(k + 1 : ℕ)) u (f p))
    (h0 : fderiv ℝ u (f p) = 0) (e : Agree k p f g) : Agree (k + 1) p (u ∘ f) (u ∘ g) := by
  have ht : ContDiffAt ℝ (↑(k + 1 : ℕ)) u (g p) := e.value ▸ hu
  refine ⟨hu.comp _ hf, ht.comp _ hg, fun n hn => ?_⟩
  rcases lt_or_eq_of_le hn with hi | rfl
  · exact (e.apply_smooth (ht.of_le (Nat.cast_le.mpr (Nat.le_succ k)))).same n (by omega)
  rw [iteratedFDeriv_comp hu hf le_rfl, iteratedFDeriv_comp ht hg le_rfl, e.value]
  refine
    Finset.sum_congr rfl fun c (_ : c ∈ (Finset.univ : Finset (OrderedFinpartition (k + 1)))) => ?_
  by_cases hc : c.length = 1
  · ext1 v
    have hp : iteratedFDeriv ℝ c.length u (g p) = 0 := by
      rw [hc]
      ext1 j
      rw [iteratedFDeriv_one_apply, ← e.value, h0]
      rfl
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, hp]
    rfl
  have hq := c.length_pos (by omega)
  have hi (j : Fin c.length) :
    ftaylorSeries ℝ f p (c.partSize j) = ftaylorSeries ℝ g p (c.partSize j) :=
    e.same _
      (by
        obtain hh := parts_small c (by omega) j
        omega)
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition, hi]

lemma top_motion (hf : ContDiffAt ℝ (↑(k + 1 : ℕ)) f p) (hg : ContDiffAt ℝ (↑(k + 1 : ℕ)) g p)
    (hu : ContDiffAt ℝ (↑(k + 1 : ℕ)) u (f p)) (e : Agree k p f g) (z : Fin (k + 1) → E) :
    iteratedFDeriv ℝ (k + 1) (u ∘ g) p z - iteratedFDeriv ℝ (k + 1) (u ∘ f) p z =
      fderiv ℝ u (f p) (iteratedFDeriv ℝ (k + 1) g p z - iteratedFDeriv ℝ (k + 1) f p z) := by
  let L := fderiv ℝ u (f p)
  let H := u - ⇑L
  have hh : ContDiffAt ℝ (↑(k + 1 : ℕ)) H (f p) := hu.sub L.contDiff.contDiffAt
  have ht : fderiv ℝ H (f p) = 0 := by
    rw [show H = u - ⇑L from rfl, fderiv_sub (hu.differentiableAt (by simp)) L.differentiableAt,
      L.fderiv]
    exact sub_self _
  have he := (stationary hf hg hh ht e).same (k + 1) le_rfl
  have hv : ContDiffAt ℝ (↑(k + 1 : ℕ)) u (g p) := e.value ▸ hu
  rw [show H ∘ g = u ∘ g - L ∘ g from rfl, show H ∘ f = u ∘ f - L ∘ f from rfl,
    iteratedFDeriv_sub_apply (hu.comp _ hf) (L.contDiff.contDiffAt.comp _ hf),
    iteratedFDeriv_sub_apply (hv.comp _ hg) (L.contDiff.contDiffAt.comp _ hg),
    L.iteratedFDeriv_comp_left hf le_rfl, L.iteratedFDeriv_comp_left hg le_rfl] at he
  have eq := congr_arg (fun V : Tensor.T E X (k + 1) => V z) he
  simp only [sub_apply] at eq
  rw [map_sub]
  exact
    sub_eq_sub_iff_add_eq_add.mpr
      (by exact ((sub_eq_sub_iff_add_eq_add.mp eq).symm.trans (add_comm ..)))
end late
variable {u v : ℝ → F}

lemma power_bill (h : ContDiffAt ℝ (↑k) u 0) :
    iteratedDeriv k (fun t : ℝ => t ^ n • u t) 0 =
      if n ≤ k then k.choose n • (n.factorial : ℝ) • iteratedDeriv (k - n) u 0 else 0 := by
  let A : ℝ → ℝ := (· ^ n)
  have he (e : ℕ) : iteratedDerivWithin e A univ 0 = ((if e = n then n.factorial else 0 : ℕ) : ℝ) := by
    rw [iteratedDerivWithin_univ]
    exact iteratedDeriv_fun_pow_zero (𝕜 := ℝ) (n := e) (m := n)
  change iteratedDeriv k (A • u) 0 = _
  have hp : ContDiff ℝ (↑k) A := by
    unfold A
    fun_prop
  rw [← iteratedDerivWithin_univ,
    iteratedDerivWithin_smul (mem_univ _) uniqueDiffOn_univ hp.contDiffAt.contDiffWithinAt
      h.contDiffWithinAt]
  split
  · rename_i hx
    rw [Finset.sum_eq_single_of_mem n
        (by
          simp only [Finset.mem_range]
          omega),
      he]
    simp only [if_true, iteratedDerivWithin_univ]
    intro a ha hu
    rw [he a, if_neg hu, Nat.cast_zero, zero_smul, smul_zero]
  rename_i ht
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [he i,
    if_neg
      (by
        obtain hv := Finset.mem_range.mp hi
        omega),
    Nat.cast_zero, zero_smul, smul_zero]

lemma power_top (h : ContDiffAt ℝ (↑n) u 0) :
    iteratedDeriv n (fun t : ℝ => t ^ n • u t) 0 = (n.factorial : ℝ) • u 0 := by simp [power_bill h]

lemma power_agree {m : ℕ} (h : ContDiffAt ℝ (↑m) u 0) (hp : ContDiffAt ℝ (↑m) v 0) (e : Agree k 0 u v)
    (he : m ≤ n + k) : Agree m 0 (fun t : ℝ => t ^ n • u t) (fun t : ℝ => t ^ n • v t) := by
  refine Agree.line ((contDiffAt_id.pow _).smul h) ((contDiffAt_id.pow _).smul hp) fun l hl => ?_
  rw [power_bill (h.of_le (Nat.cast_le.mpr hl)), power_bill (hp.of_le (Nat.cast_le.mpr hl)),
    e.along_line (k := l - n) (by omega)]
end YM.WilsonMS.TaylorRules
