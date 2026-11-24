import YM.RG3.Pan.Roll
import YM.Next.RANK.Ray
import YM.Extra.WILSON_STARTUP.Curvature

/-! # Germ prices on the true representation image, recovering
holonomy FROM projection curvature. Small chord on EACH letter required. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan
open Filter Function WilsonStartup Next.Rank
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
 {f : E→F} {x : E}
 {G : Gauge} {k : ℕ}

/-- Everything here is over the real scalar chart. -/
lemma eventually_charged (h : ContDiffAt ℝ ω f x) (k : ℕ):∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ y in 𝓝 x, Bill k C 1 f y := by
  let C (i : ℕ):=‖iteratedFDeriv ℝ i f x‖
  have he (i : ℕ): ∀ᶠ y in 𝓝 x, ‖iteratedFDeriv ℝ i f y‖ ≤ 1+C i :=
    ((h.continuousAt_iteratedFDeriv (k:=i) le_top).norm).eventually (ge_mem_nhds (lt_one_add _))
  let M:= ∑ i∈Finset.range (k+1), C i
  refine ⟨1+M,le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=> norm_nonneg _)),?_⟩
  filter_upwards [eventually_all.mpr (fun i:Fin (k+1) => he i), h.eventually (by simp)] with y hy hx
  refine ⟨hx.of_le le_top,fun j hj => ?_⟩
  rw [one_pow,mul_one]
  have hp: j<k+1:= by omega
  exact (hy ⟨j,hp⟩).trans (add_le_add_right (Finset.single_le_sum (f:=C) (fun _ _=>norm_nonneg _) (Finset.mem_range.mpr hp)) 1)

structure Bath (G : Gauge) (k : ℕ) where
  price : ℝ
  tile : ℝ
  extra : 1 ≤ price
  positive : 0 < tile
  bowl : tile ≤ 1
  spin (v : G.Color) : ‖v‖ ≤ tile → Bill k price 1 (G.mat ∘ recover G) v
  turn (u : G.El) : G.chord u ≤ tile → Bill k price 1 G.plog (G.mat u)
  south (v : G.Color) : ‖v‖ ≤ tile → G.curvature (recover G v) = v
  north (u : G.El) : G.chord u ≤ tile → recover G (G.curvature u)=u
  bill (v : G.Color) : ‖v‖ ≤ tile → G.chord (recover G v) ≤ price*‖v‖
  true (u : G.El) : G.chord u ≤ tile → G.lieExp (G.plog (G.mat u))=u
  shear (u : G.El) : G.chord u ≤ tile → ‖G.plog (G.mat u)‖ ≤ price * G.chord u

lemma draw (G : Gauge) (k : ℕ) : Nonempty (Bath G k):= by
  obtain ⟨C,hC,h⟩:=eventually_charged (G.plog_diff) k
  let R:=G.mat∘recover G
  obtain ⟨D,hD,h'⟩:=eventually_charged (show ContDiffAt ℝ ω R 0 from recover_analytic G) (k+1)
  have hg:=G.colorScale_pos; have hc:=zero_le_one.trans hC; have hd:=zero_lt_one.trans_le hD
  obtain ⟨s,hs,H⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp (h'.and (recover_right G))
  obtain ⟨V⟩:=Spindle.charts G
  obtain ⟨r,hr,P⟩:=surrounds G _ ((recover_left G).and ((show Tendsto G.mat (𝓝 1) (𝓝 1) from G.continuous_mat.tendsto _).eventually h))
  let M:=max 2 (C+D+D/G.colorScale)
  have hM : C+D+D/G.colorScale ≤ M:=le_max_right ..
  have hW : 2 ≤ M:=le_max_left ..
  have hD' : D/G.colorScale ≥0:= by positivity
  let b:=min (1:ℝ) (min (min r s) V.c)
  have he (v : G.Color) (hy : ‖v‖ ≤ b): Bill (k+1) D 1 R v ∧ G.curvature (recover G v)=v := H (Metric.mem_closedBall.mpr (show dist v 0 ≤ s by rw [dist_zero_right]; exact hy.trans ((min_le_right 1 _).trans ((min_le_left _ _).trans (min_le_right ..)))))
  have hf (v : G.El) (hy : G.chord v ≤ b): recover G (G.curvature v)=v ∧ Bill k C 1 G.plog (G.mat v) := P (show v∈G.shell r from hy.trans ((min_le_right 1 _).trans ((min_le_left _ _).trans (min_le_left ..))))
  have ht : 0 < b:=by unfold b; rw [lt_min_iff,lt_min_iff,lt_min_iff]; exact ⟨zero_lt_one,⟨hr,hs⟩,V.radius⟩
  have hL : b ≤ V.c:=le_trans (min_le_right 1 _) (min_le_right ..)
  refine ⟨⟨M,b,by linarith,ht,min_le_left ..,fun v hv=> ((he v hv).1.down (Nat.le_succ k)).up zero_le_one (by linarith),fun i hi=> ((hf i hi).2).up zero_le_one (by linarith),fun i hi=> (he i hi).2,fun i hi=>(hf i hi).1,fun i hi=>?_,fun i hi=>V.records i (hi.trans hL),fun i hi=>(V.sleeve i (hi.trans hL)).trans (mul_le_mul_of_nonneg_right hW (G.chord_nonneg _))⟩⟩
  let L:= Metric.closedBall (0:G.Color) b
  have hL' (v) (hv : v∈L) := (he v (by rwa [← dist_zero_right])).1
  have hy:= (convex_closedBall (0:G.Color) b).norm_image_sub_le_of_norm_fderiv_le (C:=D) (fun y h=> (hL' y h).smooth.differentiableAt (by simp)) (by intro v hv; rw [←norm_iteratedFDeriv_one]; simpa using (hL' v hv).B 1 (by omega)) (Metric.mem_closedBall_self ht.le) (Metric.mem_closedBall.mpr (show dist i 0 ≤ b by rwa [dist_zero_right]))
  rw [sub_zero, show R 0=1 by simp [R]] at hy
  change ‖R i-1‖/G.colorScale ≤ _
  refine (div_le_div_of_nonneg_right hy hg.le).trans ?_
  rw [mul_comm D,mul_div_assoc,mul_comm M]; exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)

/-- Real linear curvature read (with zeroth signed normalization built in). -/
def tint (G : Gauge) : G.Mat→L[ℝ] G.Color:=
  let L : G.Mat→L[ℝ] G.Mat:= ContinuousLinearMap.id ℝ _
  let U : G.Mat→L[ℝ] G.Mat:= (starL' ℝ : G.Mat≃L[ℝ] G.Mat).toContinuousLinearMap
  G.projectColor.toContinuousLinearMap.comp ((1/2:ℝ) • (L-U))

@[simp] lemma tinted (G : Gauge) (v : G.El): tint G (G.mat v)=G.curvature v:= rfl
lemma tint_norm (G : Gauge) (v : G.Mat) : ‖tint G v‖ ≤ G.colorScale⁻¹*‖v‖ := by
  change ‖G.projectColor ((1/2:ℝ) • (v-star v))‖ ≤ _
  apply (G.project_norm _).trans
  calc
    _ ≤ (1/2:ℝ)*(‖v‖+‖star v‖)/G.colorScale:=by
      apply div_le_div_of_nonneg_right _ G.colorScale_pos.le
      rw [norm_smul_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left (norm_sub_le ..) (by norm_num)
    _ = _ := by rw [Matrix.star_eq_conjTranspose,Matrix.frobenius_norm_conjTranspose, inv_mul_eq_div]; ring

end YM.RG3.Pan
