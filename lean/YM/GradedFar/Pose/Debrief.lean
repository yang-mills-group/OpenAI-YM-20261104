import YM.GradedFar.Pose.Forecast

/-!
# The lower bound of line 1385, and the software forecast
-/
namespace YM.FVA2.GradedFar.Pose
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m d : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1

-- actual predictors and crop on t, real times
def foresee (d p : ℕ) (t : ℝ) : Prediction G d :=
  ∑ i∈Finset.range (p+1), t^i • reports N M d i
abbrev line (x : Points n) (u : Fin n→Sec G d) : PowerSeries ℂ :=
  mk fun i=> fxt (Bbook N d) x i u
private lemma foresee_report (n d p : ℕ) (t : ℝ) (z : Test n) (u : Fin n→Sec G d) :
    foresee N M d p t n z u = ∑ i∈Finset.range (p+1), t^i • reports N M d i n z u := by
  let A : Prediction G d →ₗ[ℝ] ℂ := watch ⟨n,z,u⟩
  change A (∑ i∈Finset.range (p+1), t^i • reports N M d i) = ∑ i∈Finset.range (p+1), t^i • A (reports N M d i)
  simp only [map_sum,_root_.map_smul]
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
lemma weighted (u : Fin n → Sec G d) (t : ℝ) (p : ℕ) (z : Test n) :
    foresee N M d p t n z u=z.applyTo fun x=> crop p t (line N x u) := by
  rw [foresee_report]
  unfold line; simp only [crop_eq]; simp_rw [coeff_mk, Complex.real_smul, Complex.ofReal_pow]
  rw [Read.smear_sum]
  · refine Finset.sum_congr rfl fun i _=> ?_
    rw [Read.smear_one,(birth N M H d).exact n i]
  intro i _
  exact ((birth N M H d).light _ i u).const_mul _ |>.mono z.tsupport_subset
lemma presumes (d p : ℕ) (t : ℝ) : (N.store.measure d).D (foresee N M d p t)=
    (N.store.measure d).D (reference G d) := by
  unfold foresee; simp_rw [map_sum,_root_.map_smul,geared N M H]
  rw [Finset.sum_eq_single 0]; · simp
  · intro b hb h; rw [if_neg h, smul_zero]
  simp
lemma expect (d p : ℕ) : foresee N M d p 0=reference G d := by
  unfold foresee; rw [Finset.sum_eq_single 0]; · simp [ground N M H]
  · intro b hb h; rw [zero_pow h]; exact (zero_smul ℝ (reports N M d b)) --]
  simp

abbrev Plans (G : Gauge) (d : ℕ) := ℝ → (n : ℕ) → (x : Points n) →
  MultilinearMap ℂ (fun _ : Fin n=> Sec G d) ℂ

variable (D : Fray (N.store.measure d)) {I : Type} {f : Filter I}
lemma pass (p : ℕ) {t : I → ℝ} (ht : Tendsto t f (𝓝 0)) :
    Tendsto (fun i=> D.purse (foresee N M d p (t i))) f (𝓝 D.opening.1) := by
  change Tendsto ((fun t' => D.purse (foresee N M d p t'))∘ t) f (𝓝 (D.purse (reference G d)))
  rw [← expect N M H d p]
  refine ContinuousAt.tendsto (f:=fun t'=> D.purse (foresee N M d p t')) ?_ |>.comp ht
  apply Continuous.continuousAt
  apply continuous_pi; intro i; apply continuous_pi; intro l
  unfold Fray.purse; simp_rw [foresee_report]
  exact continuous_finsetSum _ (fun _ _ => Continuous.smul (continuous_id.pow _) continuous_const)

include D
lemma itinerary_fare (p : ℕ) {t : I → ℝ} (ht : Tendsto t f (𝓝 0)) (D' : I → Normalize.Change G d)
    (H' : Tendsto (fun i=> guide G d (D' i)) f (𝓝 0)) :
    ∀ᶠ i in f, ‖guide G d (D' i)‖ ≤ 2 * ‖guide G d ((N.store.measure d).D (recruit (stand (D' i))
      (foresee N M d p (t i))) - (N.store.measure d).D (reference G d))‖ := by
  let v i:= guide G d (D' i); let P i:= foresee N M d p (t i); let Z i:= D.purse (P i)
  have hc : HasStrictFDerivAt D.itinerary (fderiv ℝ D.itinerary D.opening) D.opening := D.fair.contDiffAt.hasStrictFDerivAt (by simp)
  obtain hh:=(hasStrictFDerivAt_iff_isLittleO.mp hc).def' (by norm_num : (0:ℝ)<1/2)
  have hp := pass N M H D p ht
  have a : Tendsto (fun i=> (Z i,v i)) f (𝓝 D.opening) := hp.prodMk_nhds H'
  have b : Tendsto (fun i=> (Z i,(0:MoveSpace G d))) f (𝓝 D.opening) := hp.prodMk_nhds tendsto_const_nhds
  filter_upwards [(a.prodMk_nhds b).eventually hh.bound] with i hi
  let A := D.itinerary (Z i,v i); let B := D.itinerary (Z i,0)
  let L := fderiv ℝ D.itinerary D.opening
  change ‖A-B-L ((Z i,v i)-(Z i,0))‖ ≤ _*‖(Z i,v i)-(Z i,0)‖ at hi
  have hf (x : MoveSpace G d) : L (0,x)=x := show D.delta D.opening x=x from by rw [D.unpin (N.store.prepared d)]; rfl
  rw [show (Z i,v i)-(Z i,0)=(0,v i) from Prod.ext (by exact sub_self _) (by exact sub_zero _), hf, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at hi
  rw [map_sub]
  have he : A=guide G d ((N.store.measure d).D (recruit (stand (D' i)) (P i))) := by
    unfold A Z v; rw [D.way,Fray.box,LinearEquiv.symm_apply_apply]
  have hu : B=guide G d ((N.store.measure d).D (reference G d)) := by
    unfold B Z; rw [D.way, Fray.box,map_zero,stand0,Screen.recruit_one, presumes N M H]
  change ‖v i‖ ≤ _ * ‖guide G d ((N.store.measure d).D (recruit _ (P i)))-guide G d _‖; rw [← he,← hu]
  have hV:=norm_add_le (v i-(A-B)) (A-B)
  rw [sub_add_cancel, norm_sub_rev] at hV
  linarith only [hi,hV]
end
end YM.FVA2.GradedFar.Pose
