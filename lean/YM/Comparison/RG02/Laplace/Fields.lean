import YM.Comparison.RG02.Laplace.Inside
/-!
# Fixed-aperture tail cost

 Taylor tail on tangent fields exterior to growing scaled aperture.
 Keep scope requiring true mouth annulus & access; this exterior cost concerns
 the Gaussian **polynomial**, not the true measure weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (g c₀:ℝ)
  (W : Bulk.Colors R G f) (x : fieldDir G c 1)
local notation "L"=> Precision.Key F G → ℝ
local notation "μ"=> Gaussian.cloud (K.covariance F t)
local notation "ζ"=> Bulk.translated K F x
local notation "T"=> Bulk.Joint S F (G:=G)

-- outside membership imposes this geometry at the step
variable (A : ℝ → Set (F.Slice G)) (r : ℕ) (s : R.Mode)
def Earned := ∃ ε:ℝ, 0 < ε ∧ ∀ᶠ g in along, ∀ v : Precision.Key F G→ℝ, v∉ scope K F g x (A g) → ε≤g*room K F x v

variable (hW : Bulk.Well W)
include hW
lemma promoted : ∃ p : ℕ, ∃ C:ℝ, 0 ≤ C ∧ ∀ g:ℝ, |g|≤1 → ∀ v : Precision.Key F G→ℝ, ‖(desired K F t g x W r v).part s‖ ≤ C*room K F x v^p := by
  let f := Assembly.rows (Assembly.expansions W.power (Bulk.markFn S F W) (Bulk.geometric K F t W)) s
  let q := Radial.zone (E:=T)
  have hu n : q.Invoice (fun x=> ‖f n x‖):= ((Assembly.radial_comparison W.power (Bulk.markFn S F W) (Bulk.geometric K F t W) (Bulk.geometric_ready K F t W hW) zero_lt_one s).invoice n).norm
  obtain ⟨C,p,hC,H⟩:= Zone.Invoice.fin_sum (range (r+1)) (fun n x=> ‖f n x‖) (fun n _=> hu n)
  refine ⟨p,C,hC,fun g h v=>?_⟩
  have hv : (desired K F t g x W r v).part s=Zone.eval f r g (ζ v) := Assembly.Zonal.zone_eval ..
  have he i : ‖(g^i • f i (ζ v))‖ ≤ ‖f i (ζ v)‖:= by rw [norm_smul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) h)
  rw [hv]; refine (norm_sum_le ..).trans ((sum_le_sum fun i _=> he i).trans ?_)
  have hz:= H (ζ v); simp_rw [Finset.sum_apply,Real.norm_eq_abs, abs_of_nonneg (show 0≤∑ i∈ Finset.range (r+1), ‖f i (ζ v)‖ from by positivity)] at hz; exact hz
lemma outpayment (h : Earned K F x A) (k : ℕ) : Bill k (fun g=> (charge μ (removed K F t g x W (A g) r)).part s) := by
  obtain ⟨C,hC,H⟩:= gauss_translated K F t x
  obtain ⟨p,m,hm,Hm⟩:= promoted K F t W x r s hW
  obtain ⟨ε,hε,Hε⟩:=h
  let B y:=room K F x y^(p+k)*Radial.shade C (ζ y)
  have hb (y : L) : 0≤ B y := mul_nonneg (pow_nonneg (room_pos ..).le _) (Real.exp_pos _).le
  apply volume_bill k s hb (H (p+k)) (m/ε^k) (by positivity)
  filter_upwards [Tested.eventually_small (show 0<(1:ℝ) from zero_lt_one), Hε] with g hg he v
  have hp:= hg.1
  let w := room K F x v; have hw : 0<w := room_pos K F x v
  by_cases h : v∈ scope K F g x (A g)
  · unfold removed; rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h),Poly.part_nil, norm_zero]; exact mul_nonneg (by positivity) (hb _)
  have he := he v h
  have hy : 1 ≤ Radial.shade C (ζ v):= Real.one_le_exp (by positivity)
  unfold removed; rw [Set.indicator_of_mem (Set.mem_compl h)]
  calc
    _ ≤ m*w^p := Hm g (by rw [abs_of_nonneg hp.le]; exact hg.2.le) v
    _ ≤ (m*w^p) * (g*w/ε)^k := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by rw [one_le_div hε]; exact he))
    _ ≤ _ := by
       apply le_trans (b:=(m*w^p)*(g*w/ε)^k*Radial.shade C (ζ v))
       · exact le_mul_of_one_le_right (by positivity) hy
       unfold B w; rw [pow_add]; simp_rw [div_pow,mul_pow,div_eq_mul_inv]; exact Eq.le (by ring)

-- actual aperture-supported model integral, keeping the leading scalar outside extraction
local notation "Φ"=> Actual.stack t (sample g x) (temperature g)
-- note `g` bound below expansion

def portal (g : ℝ): Poly R:= ((wage K F t g c₀ x:ℂ))⁻¹ •
   charge (F.order G) ((A g).indicator (Actual.stack t (sample g x) (temperature g) (model g c₀ W K)∘ F.drape))

lemma denote : ∃ δ:ℝ, 0<δ ∧ ∀ A, Small K F x A δ → Earned K F x A → (∀ᶠ g in along, Trust K F t g x (A g)) →
    Trial (detail (Bulk.Fk K F t W x r) s) (fun g=> (portal K F t c₀ W x A g).part s) r := by
   obtain ⟨δ,hδ,Hδ⟩:= park K F t W x r s hW; refine ⟨δ,hδ,fun A h H ha=>?_⟩
   refine bill_congr ?_ (bill_add (Hδ A h) (bill_neg (outpayment K F t W x A r s hW H (r+1))))
   filter_upwards [ha, eventually_pos] with g ha ht
   unfold portal; dsimp only [Pi.add_apply,Pi.neg_apply,Pi.sub_apply]; rw [one_thermal K F t g c₀ x W (A g) r ha ht hW, smul_smul, inv_mul_cancel₀ (show _ from Complex.ofReal_ne_zero.mpr (wage_pos K F t g c₀ x ht).ne'), one_smul, Extra.Trajectories.part_sub, Poly.part_plus, tests]; abel
end YM.Comparison.RG02.Laplace
