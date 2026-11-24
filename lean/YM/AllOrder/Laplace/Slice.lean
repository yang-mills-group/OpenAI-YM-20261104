import YM.PertExtension.Interior
import YM.PertExtension.Aspiration
/-!
# Exact fixed-period half-line test of a formal conditional integral

Independent Taylor coefficients all orders of an unmasked, unnormalized integral in
curved (or flat) shifted coordinates, only TWO-type finite-dimensional space here. One
free scalar represents coupling, vertical Gaussian variables not required Euclidean.
Norm is max-product. Cut applied in the JOINT ball. This is **not** an exact-theory
comparison on shrinking schedule. It will be used for uniqueness of coefficients while
transporting charts and gauges (in particular costs in this file need **not** be
pre-L or uniform in finite period).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Filter Metric
open scoped Topology ENNReal ContDiff
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y][BorelSpace Y]
-- Note forward arguments in the affine plane always. Can translate in the function, not measure.
local notation "Ω" => ℝ×Y
variable {F K: ℝ×Y→ℝ}

def onLane (u:Y): ℝ×Y := (1,u)
omit [FiniteDimensional ℝ Y] [BorelSpace Y] [NormedSpace ℝ Y] [MeasurableSpace Y] in
lemma lane_closed : Topology.IsClosedEmbedding (onLane (Y:=Y)) :=
  ⟨isEmbedding_prodMkRight _, (show IsClosed (range _) from by rw [show range (onLane (Y:=Y))={1} ×ˢ univ from Set.ext fun ⟨_,_⟩=>by simp [onLane,eq_comm]]; exact isClosed_singleton.prod isClosed_univ)⟩
variable (μ: Measure Y) [μ.HasTemperateGrowth]
def view := Measure.map (onLane (Y:=Y)) μ
instance : (view μ).HasTemperateGrowth := by
  obtain ⟨n,H⟩:= Measure.HasTemperateGrowth.exists_integrable (μ:=μ);
  refine ⟨n,(lane_closed.measurableEmbedding).integrable_map_iff.mpr ?_⟩
  apply H.mono' _ (Eventually.of_forall ?_)
  · apply Continuous.aestronglyMeasurable (Continuous.rpow_const (Continuous.add continuous_const (continuous_norm.comp lane_closed.continuous)) (fun x:Y=> Or.inl (show 1+‖onLane x‖≠0 by positivity)))
  intro x; change ‖ (1+‖onLane x‖)^ (-(n:ℝ))‖ ≤ _; rw [Real.norm_of_nonneg (by positivity)]; have ht : ‖x‖≤‖onLane x‖:= norm_snd_le (onLane x)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr (Nat.cast_nonneg _))

-- use local chart r; translated center choice in F, not in disc

def stick (μ:Measure Y)(F K:Ω→ℝ)(r t:ℝ):ℝ:= ∫ y in disc t r, K (t,t • y) * Real.exp (-F (t,t • y) / t^2) ∂μ
def part (μ:Measure Y)(F K:Ω→ℝ)(k:ℕ):= ∫ y, Radial.normTerm K F k (onLane y) ∂μ

omit [μ.HasTemperateGrowth] in
lemma part_view (n:ℕ) : part μ F K n = Radial.moment (view μ) K F n := (lane_closed.measurableEmbedding.integral_map _).symm
structure Cylinder (F K: Ω→ℝ) : Prop where
  revenue : Radial.Stationary F
  income : ContDiffAt ℝ ∞ K 0
  risen : ∃ a>0,∀ x : Ω, a*‖x‖^2 ≤ jet F 2 x

variable (h:Cylinder F K)
include h
lemma integrable_term (k:ℕ) : Integrable (fun y:Y=>normTerm K F k (onLane y)) μ :=
  (lane_closed.measurableEmbedding.integrable_map_iff).mp (h.revenue.integrableTerm (view μ) h.income h.risen)

omit h [μ.HasTemperateGrowth] in
lemma stick_view (K F : Ω→ℝ) {r t : ℝ} (hp : t<r) (ht : 0<t): stick μ F K r t= partialSum (view μ) K F r t := by
  unfold stick partialSum view; rw [lane_closed.measurableEmbedding.setIntegral_map (Y:=_) _ _]; simp_rw [projection_eq,onLane]; -- preimage
  congr! 1
  · have he:(disc t r: Set Y)=onLane ⁻¹' disc t r:= by ext x; simp [disc, onLane,norm_smul,Prod.norm_def,hp,abs_of_nonneg ht.le]
    rw [he]
  simp

-- initial version measurable only; later `Even Cut`. Purchase bill so all moments exist on THIS μ push.
lemma arced (n:ℕ) (hF:Measurable F) (hK:Measurable K) : ∀ᶠ δ in Tested.germ, Bill (n+1) (stick μ F K δ - peval (part μ F K) n):= by
  obtain ⟨d,hd,H⟩:= h.revenue.rescale_estimate (view μ) h.income hK hF h.risen n
  filter_upwards [Tested.eventually_small hd] with r hr
  obtain ⟨C,hC⟩:= H r hr
  refine ⟨max 0 C, le_max_left ..,?_⟩; filter_upwards [hC, Tested.eventually_small hr.1] with t ht hb
  change ‖stick μ F K r t - ∑ i∈Finset.range (n+1),t^i*part μ F K i‖≤ _
  simp_rw [stick_view μ K F hb.2 hb.1, part_view]; exact ht.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg hb.1.le _))
end YM.AllOrder.Laplace
