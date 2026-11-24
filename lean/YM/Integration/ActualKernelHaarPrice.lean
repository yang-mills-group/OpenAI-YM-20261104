import YM.Integration.ActualKernelHaar
import YM.Push.STATIONARY_UNIFORM.Array
import YM.Push.STATIONARY_UNIFORM.Scatter

/-!
# A single-port tensor bill for the full logarithmic Haar factor

The coordinates are the original Array.paint coordinates: coarse physical
entries plus Precision.Key = free bond times orthonormal color. Fixing one
positive-order derivative port forces every nonzero local Haar contribution
onto that same free bond. The remaining sum therefore counts only colors,
never sites, periods or the number of free bonds.

The logarithm is the full local spin. The equality with a supplied chart is
a germ at zero; no global chart equality or scale/radius estimate is used.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualKernelHaarPrice
open Filter Function Finset Lattice RG Precision Tree
open Push.Uniform Comparison.RG02
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {p : Ratio c f} (B : Forest p)

def logSpin (G : Gauge) : G.Color → ℝ := Real.log ∘ LocalH.spin G

private theorem logSpin_smooth (G : Gauge) :
    ContDiffAt ℝ ω (logSpin G) 0 :=
  (LocalH.spin_deriv G 0).log (by
    rw [LocalH.spin_zero]
    exact one_ne_zero)

private def project (b : B.Free) :
    Positions (Push.Uniform.Joint B G) →L[ℝ] G.Color :=
  (ContinuousLinearMap.proj (φ := fun _ : B.Free => G.Color) b) ∘L
    ((ContinuousLinearMap.snd ℝ (Push.In G c) (AxisChart G B)) ∘L
      (paint B G).toContinuousLinearMap)

private theorem project_apply (b : B.Free)
    (z : Positions (Push.Uniform.Joint B G)) (j : G.ColorIndex) :
    project B b z j = z (Sum.inr (b, j)) := rfl

private theorem project_inl (b : B.Free) (q : Primary c G) :
    project B b (bolt (Sum.inl q)) = 0 := by
  ext j
  rw [project_apply]
  simp [bolt]

private theorem project_other (b : B.Free) (q : Precision.Key B G)
    (h : b ≠ q.1) :
    project B b (bolt (Sum.inr q)) = 0 := by
  ext j
  rw [project_apply]
  rcases q with ⟨q, t⟩
  dsimp only at h
  simp [bolt, h]

private theorem project_same (b : B.Free) (j : G.ColorIndex) :
    project B b (bolt (Sum.inr (b, j))) =
      EuclideanSpace.basisFun G.ColorIndex ℝ j := by
  ext k
  rw [project_apply]
  by_cases h : k = j <;>
    simp [h, bolt, Pi.single_apply, EuclideanSpace.basisFun_apply, eq_comm]
  exact Ne.symm h

private theorem project_norm (b : B.Free)
    (q : Push.Uniform.Joint B G) :
    ‖project B b (bolt q)‖ ≤ 1 := by
  rcases q with q | ⟨q, j⟩
  · rw [project_inl, norm_zero]
    exact zero_le_one
  by_cases h : b = q
  · subst q
    simpa only [project_same, OrthonormalBasis.norm_eq_one] using (le_refl (1 : ℝ))
  rw [project_other B b (q, j) h, norm_zero]
  exact zero_le_one

private theorem project_port (b : B.Free)
    (q : Push.Uniform.Joint B G)
    (h : project B b (bolt q) ≠ 0) :
    ∃ j : G.ColorIndex, q = Sum.inr (b, j) := by
  rcases q with q | ⟨q, j⟩
  · exact False.elim (h (project_inl B b q))
  have he : b = q := by
    by_contra hn
    exact h (project_other B b (q, j) hn)
  subst q
  exact ⟨j, rfl⟩

def sumLog (z : Positions (Push.Uniform.Joint B G)) : ℝ :=
  ∑ b : B.Free, (logSpin G ∘ project B b) z

def spinLog (z : Positions (Push.Uniform.Joint B G)) : ℝ :=
  Real.log (∏ b : B.Free, LocalH.spin G ((paint B G z).2 b))

/-- The bill for derivative order k+1 after fixing its first port. -/
def onePortCost (G : Gauge) (k : ℕ) : ℝ :=
  (Fintype.card G.ColorIndex : ℝ) ^ k *
    ‖iteratedFDeriv ℝ (k + 1) (logSpin G) 0‖

theorem onePortCost_nonnegative (G : Gauge) (k : ℕ) :
    0 ≤ onePortCost G k :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) k) (norm_nonneg _)

private theorem local_smooth (b : B.Free) :
    ContDiffAt ℝ ω (logSpin G ∘ project B b) 0 := by
  have h : ContDiffAt ℝ ω (logSpin G) (project B b 0) := by
    simpa only [map_zero] using logSpin_smooth G
  exact h.comp 0 (project B b).contDiff.contDiffAt

/-- The finite product logarithm is the sum of full local logarithms near zero. -/
theorem log_product_germ :
    spinLog (G := G) B =ᶠ[𝓝 0] sumLog B := by
  have h0 : LocalH.spin G 0 ≠ 0 := by
    rw [LocalH.spin_zero]
    exact one_ne_zero
  have hn := (LocalH.spin_deriv G 0).continuousAt.eventually_ne h0
  have hp : ∀ᶠ z : Positions (Push.Uniform.Joint B G) in 𝓝 0,
      ∀ b : B.Free, LocalH.spin G (project B b z) ≠ 0 := by
    apply eventually_all.mpr
    intro b
    have ht : Tendsto (project (G := G) B b) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (project (G := G) B b).continuous.tendsto 0
    exact ht.eventually hn
  filter_upwards [hp] with z hz
  change Real.log (∏ b : B.Free, LocalH.spin G (project B b z)) =
    ∑ b : B.Free, Real.log (LocalH.spin G (project B b z))
  exact Real.log_prod (fun b _ => hz b)

private theorem local_entry (k : ℕ) (b : B.Free)
    (q : Fin k → Push.Uniform.Joint B G) :
    entry (logSpin G ∘ project B b) 0 q =
      iteratedFDeriv ℝ k (logSpin G) 0
        (fun j => project B b (bolt (q j))) := by
  unfold entry
  rw [Next.Foundations.jets_linear (project B b)
    ((logSpin_smooth G).of_le le_top)]
  rfl

private theorem entry_inl (k : ℕ) (q : Primary c G)
    (v : Fin k → Push.Uniform.Joint B G) :
    entry (sumLog B) 0 (Fin.cons (Sum.inl q) v) = 0 := by
  unfold sumLog
  rw [entries_finset (s := Finset.univ) (fun b _ => local_smooth B b)]
  simp_rw [local_entry]
  apply Finset.sum_eq_zero
  intro b _
  apply ContinuousMultilinearMap.map_coord_zero (i := 0)
  simpa only [Fin.cons_zero] using project_inl B b q

private theorem entry_inr (k : ℕ) (b : B.Free) (j : G.ColorIndex)
    (v : Fin k → Push.Uniform.Joint B G) :
    entry (sumLog B) 0 (Fin.cons (Sum.inr (b, j)) v) =
      iteratedFDeriv ℝ (k + 1) (logSpin G) 0
        (fun t => project B b (bolt ((Fin.cons (Sum.inr (b, j)) v : Fin (k + 1) → Push.Uniform.Joint B G) t))) := by
  unfold sumLog
  rw [entries_finset (s := Finset.univ) (fun a _ => local_smooth B a)]
  simp_rw [local_entry]
  apply Finset.sum_eq_single_of_mem b (Finset.mem_univ _)
  intro a _ ha
  apply ContinuousMultilinearMap.map_coord_zero (i := 0)
  simpa only [Fin.cons_zero] using project_other B a (b, j) ha

/-- The positive-order tensor has a color-only sum after one coordinate is fixed.
This is a nonfactorial derivative bill in the original physical coordinates. -/
theorem one_port_l1 (k : ℕ) (q : Push.Uniform.Joint B G) :
    (∑ v : Fin k → Push.Uniform.Joint B G,
      ‖entry (sumLog B) 0 (Fin.cons q v)‖) ≤ onePortCost G k := by
  rcases q with q | ⟨b, j⟩
  · simp only [entry_inl, norm_zero, Finset.sum_const_zero]
    exact onePortCost_nonnegative G k
  let T := iteratedFDeriv ℝ (k + 1) (logSpin G) 0
  let E (v : Fin k → Push.Uniform.Joint B G) :=
    entry (sumLog B) 0 (Fin.cons (Sum.inr (b, j)) v)
  let lift (v : Fin k → G.ColorIndex) (t : Fin k) :
      Push.Uniform.Joint B G := Sum.inr (b, v t)
  have hinj : Function.Injective lift := by
    intro v w h
    funext t
    exact congrArg Prod.snd (Sum.inr.inj (congrFun h t))
  have hout (v : Fin k → Push.Uniform.Joint B G)
      (hv : v ∉ Finset.univ.image lift) : E v = 0 := by
    by_contra he
    have hn (t : Fin k) : project B b (bolt (v t)) ≠ 0 := by
      intro hz
      apply he
      dsimp only [E]
      rw [entry_inr]
      apply ContinuousMultilinearMap.map_coord_zero (i := t.succ)
      simpa only [Fin.cons_succ] using hz
    choose u hu using fun t => project_port B b (v t) (hn t)
    apply hv
    refine Finset.mem_image.mpr ⟨u, Finset.mem_univ _, ?_⟩
    funext t
    exact (hu t).symm
  have hbound (v : Fin k → Push.Uniform.Joint B G) : ‖E v‖ ≤ ‖T‖ := by
    dsimp only [E]
    rw [entry_inr]
    apply (T.le_opNorm _).trans
    have hp : (∏ t : Fin (k + 1),
        ‖project B b (bolt ((Fin.cons (Sum.inr (b, j)) v : Fin (k + 1) → Push.Uniform.Joint B G) t))‖) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => project_norm B b _)
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg T)).trans_eq (mul_one _)
  change (∑ v, ‖E v‖) ≤ _
  calc
    _ = ∑ v ∈ Finset.univ.image lift, ‖E v‖ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      rw [hout v hv, norm_zero]
    _ = ∑ u : Fin k → G.ColorIndex, ‖E (lift u)‖ :=
      Finset.sum_image hinj.injOn
    _ ≤ ∑ _u : Fin k → G.ColorIndex, ‖T‖ :=
      Finset.sum_le_sum (fun _ _ => hbound _)
    _ = onePortCost G k := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, onePortCost, T]

section Kernel
variable {S : StepData c f} {q : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S q P O) (F : Forest S.ratio)

private theorem array_tendsto :
    Tendsto (fun z : Positions (Push.Uniform.Joint F G) =>
      ((0 : ℝ), paint F G z)) (𝓝 0) (𝓝 0) := by
  have h : Continuous (fun z : Positions (Push.Uniform.Joint F G) =>
      ((0 : ℝ), paint F G z)) := by fun_prop
  simpa only [map_zero, Prod.mk_zero_zero] using h.tendsto 0

include K in
/-- The supplied kernel uses the same local logarithms in the original Array.paint chart. -/
theorem kernel_log_germ :
    (fun z : Positions (Push.Uniform.Joint F G) =>
      Real.log (∏ b : F.Free, O.J ((paint F G z).2 b))) =ᶠ[𝓝 0] sumLog F := by
  have h := (ActualKernelHaar.normalized_haar_germ K F).comp_tendsto
    (array_tendsto F)
  have hlog : (fun z : Positions (Push.Uniform.Joint F G) =>
      Real.log (∏ b : F.Free, O.J ((paint F G z).2 b))) =ᶠ[𝓝 0]
      spinLog F := by
    filter_upwards [h] with z hz
    exact congrArg Real.log hz
  exact hlog.trans (log_product_germ F)

include K in
/-- A single constant fixed by G and k pays every original period and forest.
The full chart logarithm remains inside the derivative. -/
theorem kernel_one_port_l1 (k : ℕ) (a : Push.Uniform.Joint F G) :
    (∑ v : Fin k → Push.Uniform.Joint F G,
      ‖entry (fun z => Real.log (∏ b : F.Free, O.J ((paint F G z).2 b)))
        0 (Fin.cons a v)‖) ≤ onePortCost G k := by
  have h := ((kernel_log_germ K F).iteratedFDeriv ℝ (k + 1)).eq_of_nhds
  simpa only [entry, h] using one_port_l1 F k a

/-- Keep the original loop and the full negative local logarithmic sum.
The coupling-square factor in Fk is left to the actual vertex application. -/
theorem officer_array_germ :
    (fun z : Positions (Push.Uniform.Joint F G) =>
      Bulk.officer F K (0, paint F G z)) =ᶠ[𝓝 0]
    (fun z => loop P (Work.F03.live F (paint F G z)) - sumLog F z) := by
  have h := (ActualKernelHaar.officer_germ K F).comp_tendsto
    (array_tendsto F)
  exact h.trans ((log_product_germ F).mono fun z hz =>
    congrArg (fun x : ℝ => loop P (Work.F03.live F (paint F G z)) - x) hz)

end Kernel
end YM.Integration.ActualKernelHaarPrice
end
