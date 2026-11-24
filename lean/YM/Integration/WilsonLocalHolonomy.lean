import YM.Integration.WilsonLocalPlaquetteWindow

/-! The group-valued plaquette holonomy follows its original branch prediction. -/
noncomputable section
namespace YM.Integration.WilsonLocalHolonomy
open YM RG Lattice Wilson MeasureTheory Filter Set
open WilsonLocalKernelConcentration WilsonLocalKernelWindow WilsonLocalPlaquetteWindow
open PertExtension.Series PertExtension.Series.Tested
open scoped BigOperators Topology Classical
variable {c f : Side} {G : Gauge} (S : StepData c f)

theorem relative (Q V : Config G c) (x : Site c) (q : PlaqAxes) :
    G.chord (faceValue V (x,q) * (faceValue Q (x,q))⁻¹) ≤ Pressure.fuel Q V x q := by
  have mul_bound (x y a b : G.El) :
      G.chord ((x*y)*(a*b)⁻¹) ≤ G.chord (x*a⁻¹)+G.chord (y*b⁻¹) := by
    rw [show x*y*(a*b)⁻¹ = (x*a⁻¹)*(a*(y*b⁻¹)*a⁻¹) by group]
    exact (G.chord_triangle _ _).trans_eq (by rw [G.chord_conj])
  have inv_bound (x y : G.El) : G.chord (x⁻¹*y) = G.chord (x*y⁻¹) := by
    rw [Pressure.chord_cyc, ← G.chord_inv (x*y⁻¹)]
    simp only [mul_inv_rev,inv_inv]
  unfold Pressure.fuel Pressure.wire
  rw [Pressure.corners,Pressure.corners]
  apply (mul_bound ..).trans
  apply add_le_add
  · apply (mul_bound ..).trans
    apply add_le_add (mul_bound ..)
    rw [inv_inv,inv_bound]
  rw [inv_inv,inv_bound]

def outside (x : Site c) (q : PlaqAxes) (Q : Config G c) (u : ℝ) : Set (Config G c) :=
  {V | 4*Real.sqrt (2*u/S.kernel.penalty) < G.chord (faceValue V (x,q)*(faceValue Q (x,q))⁻¹)}

theorem support (x : Site c) (q : PlaqAxes) (Q : Config G c) {u : ℝ} (hu : 0 ≤ u) :
    outside S x q Q u ⊆ {V | u ≤ score S (bonds x q) Q V} := by
  intro V hv
  change u ≤ score S (bonds x q) Q V
  by_contra! h
  have hp (e : Edge (Site c)) (he : e ∈ bonds x q) := wire S (bonds x q) Q V hu h.le ⟨e,he⟩
  have hf : Pressure.fuel Q V x q ≤ 4*Real.sqrt (2*u/S.kernel.penalty) := by
    unfold Pressure.fuel
    linarith only [hp (x,q.val.1) (by simp [bonds]), hp (x+step q.val.1,q.val.2) (by simp [bonds]),
      hp (x+step q.val.2,q.val.1) (by simp [bonds]), hp (x,q.val.2) (by simp [bonds])]
  exact (not_lt_of_ge ((relative Q V x q).trans hf)) hv

def measured (x : Site c) (q : PlaqAxes) (b u : ℝ) (U : Config G f) : ℝ :=
  ∑ z, S.likelihood U z * ∫ V in outside S x q (S.prediction U z) u,
    S.noise b (S.prediction U z) V ∂prior G c

theorem comparison (x : Site c) (q : PlaqAxes) (b : ℝ) {u : ℝ} (hu : 0 ≤ u) (U : Config G f) :
    measured S x q b u U ≤ probability S (bonds x q) b u U := by
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (S.likelihood_pos U z)
  apply setIntegral_mono_set (S.noise_integrable b (S.prediction U z)).integrableOn _ (ae_of_all _ (fun V =>
    support S x q (S.prediction U z) hu (a:=V)))
  exact ae_of_all _ fun V => Finset.prod_nonneg fun i _ =>
    mul_nonneg (inv_pos.mpr (S.penaltyZ_pos b)).le (Real.exp_pos _).le

theorem bounded_links {G : Gauge} (D : Calendar G) (K : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ᶠ (t : ℝ) in Tested.germ, ∀ m p : ℕ, (D.op m p).patch.Branches D.kernel G →
    ∀ (A : Finset (Edge (Site (D.schedule.side m p)))), A.card ≤ K →
    ∀ U : Config G (D.schedule.side (m+1) p),
      probability (D.op m p) A (t^2)⁻¹ (t^2*(Real.log t)^2) U ≤ C*t^n := by
  choose C hC H using fun k => WilsonLocalKernelWindow.logarithmic D k
  let B := ∑ j ∈ Finset.range (K+1), C j
  refine ⟨B, Finset.sum_nonneg (fun j _ => (hC j).le),fun n => ?_⟩
  have hall := (Filter.eventually_all_finset (Finset.range (K+1))).mpr (fun i _ => H i n)
  filter_upwards [hall,Tested.eventually_pos] with t ht hp m p hB A hA U
  have hk : A.card ∈ Finset.range (K+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hA)
  exact (ht A.card hk m p hB A rfl U).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => (hC j).le) hk) (pow_nonneg hp.le _))

theorem logarithmic {G : Gauge} (D : Calendar G) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ᶠ (t : ℝ) in Tested.germ, ∀ m p : ℕ, (D.op m p).patch.Branches D.kernel G →
    ∀ (x : Site (D.schedule.side m p)) (q : PlaqAxes) (U : Config G (D.schedule.side (m+1) p)),
      measured (D.op m p) x q (t^2)⁻¹ (t^2*(Real.log t)^2) U ≤ C*t^n := by
  obtain ⟨C,hC,H⟩ := bounded_links D 4
  refine ⟨C,hC,fun n => ?_⟩
  filter_upwards [H n] with t ht m p hB x q U
  exact (comparison (D.op m p) x q _ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) U).trans
    (ht m p hB (bonds x q) (bond_count x q) U)

end YM.Integration.WilsonLocalHolonomy
