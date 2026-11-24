import YM.Integration.WilsonAxialWindow
import YM.Next.FLUCTUATIONS.Charts

/-! Borel logarithmic coordinates of the genuine local axial representative under the original Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAxialCoordinates

open Function Filter Set Metric MeasureTheory Lattice Wilson RG Axial Next.Fluctuations OPE.Therm
open WilsonAxialWindow
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

structure LocalLog (G : Gauge) where
  radius : ℝ
  cost : ℝ
  radius_pos : 0 < radius
  cost_pos : 0 < cost
  read : G.El → G.Color
  borel : Measurable read
  price : ∀ u, ‖read u‖ ≤ cost*G.chord u
  chart : ∀ u, G.chord u ≤ radius → read u = G.plog (G.mat u) ∧ G.lieExp (read u) = u

theorem purchase (G : Gauge) : Nonempty (LocalLog G) := by
  obtain ⟨C,δ,hC,hδ,chart⟩ := log_chart_cost G
  obtain ⟨s,hs,hone,hcont⟩ := G.plog_diff.contDiffOn' (m:=0) (by simp) (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ ..),Set.univ_inter] at hcont
  obtain ⟨a,ha,hinside⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 (hs.mem_nhds hone)
  let d := min δ (a/G.colorScale)
  let Q := {u : G.El | G.chord u ≤ d}
  let f := Q.piecewise (fun u => G.plog (G.mat u)) 0
  have hQ : MeasurableSet Q := (isClosed_le G.continuous_chord continuous_const).measurableSet
  have hmat : MapsTo G.mat Q s := by
    intro u hu
    apply hinside
    rw [Metric.mem_closedBall,dist_eq_norm,← chord_dist]
    have he : G.chord u ≤ a/G.colorScale := (show G.chord u ≤ d from hu).trans (min_le_right ..)
    simpa only [mul_comm] using (le_div_iff₀ G.colorScale_pos).mp he
  have hb : Measurable f := (hcont.continuousOn.comp G.continuous_mat.continuousOn hmat).measurable_piecewise continuousOn_const hQ
  refine ⟨⟨d,C,lt_min hδ (div_pos ha G.colorScale_pos),hC,f,hb,?_,?_⟩⟩
  · intro u
    by_cases hu : u ∈ Q
    · rw [show f u = G.plog (G.mat u) from Set.piecewise_eq_of_mem _ _ _ hu]
      exact (chart u ((show G.chord u ≤ d from hu).trans (min_le_left ..))).2
    · rw [show f u = 0 from Set.piecewise_eq_of_notMem _ _ _ hu,norm_zero]
      exact mul_nonneg hC.le (G.chord_nonneg _)
  · intro u hu
    have he : f u = G.plog (G.mat u) := Set.piecewise_eq_of_mem _ _ _ (show u∈Q from hu)
    exact ⟨he,he ▸ (chart u (hu.trans (min_le_left ..))).1⟩

theorem continuous_frame (k : Lattice.Order) (o y : Site n) :
    Continuous (fun U : Config G n => frame k o U y) := by
  change Continuous ((fun V : CoverConfig G => travel V 0 _) ∘ (fun U : Config G n => expandAt o U))
  exact (continuous_travel _ _).comp (continuous_pi fun e => continuous_apply _)

theorem continuous_link (k : Lattice.Order) (o : Site n) (e : Edge (Site n)) :
    Continuous (fun U : Config G n => Lattice.gauge (frame k o U) U e) :=
  ((continuous_frame k o e.1).mul (continuous_apply e)).mul (continuous_frame k o (e.1+step e.2)).inv

def coordinates (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (t : ℝ) (U : Config G n) :
    Next.Fluctuations.LogField G n :=
  fun j => let e := (Work.E03.poleEquiv n).symm j
    if separation o e.1 < r then t⁻¹ • L.read (Lattice.gauge (frame k o U) U e) else 0

theorem measurable (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (t : ℝ) :
    Measurable (coordinates L k o r t) := by
  apply measurable_pi_lambda
  intro j
  let e := (Work.E03.poleEquiv n).symm j
  by_cases h : separation o e.1 < r
  · simp only [coordinates,e,if_pos h]
    convert (L.borel.comp (continuous_link k o e).measurable).const_smul (t⁻¹) using 1
    ext U
    rfl
  · simpa only [coordinates,e,if_neg h] using
      (measurable_const : Measurable (fun _ : Config G n => (0:G.Color)))

theorem exact (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (hn : 2*r < n.val)
    (t : ℝ) (ht : 0 < t) (U : Config G n) {b : ℝ} (hb : 0 ≤ b)
    (hq : 4*(r:ℝ)*Fintype.card PlaqAxes*b ≤ L.radius)
    (h : ∀ z ∈ cells o r, G.chord (faceValue U z) ≤ b) (e : Edge (Site n)) (he : separation o e.1 < r) :
    t • coordinates L k o r t U (Work.E03.poleEquiv n e) = G.plog (G.mat (Lattice.gauge (frame k o U) U e)) ∧
    G.lieExp (t • coordinates L k o r t U (Work.E03.poleEquiv n e)) = Lattice.gauge (frame k o U) U e := by
  simp only [coordinates,Equiv.symm_apply_apply,if_pos he,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  exact L.chart _ ((bound k o U r hn e he hb h).trans hq)

theorem coefficient (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (U : Config G n) (e : Edge (Site n)) :
    ‖coordinates L k o r t U (Work.E03.poleEquiv n e)‖ ≤ t⁻¹*L.cost*G.chord (Lattice.gauge (frame k o U) U e) := by
  simp only [coordinates,Equiv.symm_apply_apply]
  split
  · rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr ht).le,mul_assoc]
    exact mul_le_mul_of_nonneg_left (L.price _) (inv_pos.mpr ht).le
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (inv_pos.mpr ht).le L.cost_pos.le) (G.chord_nonneg _)

def excluded (o : Site n) (r : ℕ) (b : ℝ) : Set (Config G n) :=
  ⋃ z ∈ cells o r, trigger z b

theorem excluded_measurable (o : Site n) (r : ℕ) (b : ℝ) :
    MeasurableSet (excluded (G:=G) o r b) :=
  MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _ => fire_meas z b

theorem outside {o : Site n} {r : ℕ} {b : ℝ} {U : Config G n} (h : U ∉ excluded o r b) :
    ∀ z ∈ cells o r, G.chord (faceValue U z) ≤ b := by
  intro z hz
  exact le_of_not_gt fun hg => h (Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,hg⟩⟩)

theorem omitted (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (o : Site n) (r : ℕ) (b δ : ℝ)
    (h : ∀ z ∈ cells o r, μ.real (trigger z b) ≤ δ) :
    μ.real (excluded (G:=G) o r b) ≤ (cells o r).card*δ := by
  apply (measureReal_biUnion_finset_le (μ:=μ) (cells o r) (fun z => trigger z b)).trans
  exact (Finset.sum_le_sum (fun z hz => h z hz)).trans_eq (by simp)

def restricted (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (t b : ℝ) :=
  (excluded (G:=G) o r b)ᶜ.indicator (coordinates L k o r t)

theorem restricted_measurable (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (t b : ℝ) :
    Measurable (restricted L k o r t b) := (measurable L k o r t).indicator (excluded_measurable o r b).compl

theorem uniform (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (hn : 2*r < n.val)
    (t b : ℝ) (ht : 0 < t) (hb : 0 ≤ b) (U : Config G n) :
    ‖restricted L k o r t b U‖ ≤ t⁻¹*L.cost*(4*(r:ℝ)*Fintype.card PlaqAxes*b) := by
  have hc : 0 ≤ t⁻¹*L.cost*(4*(r:ℝ)*Fintype.card PlaqAxes*b) :=
    mul_nonneg (mul_nonneg (inv_pos.mpr ht).le L.cost_pos.le) (by positivity)
  by_cases h : U ∈ excluded o r b
  · rw [restricted,Set.indicator_of_notMem (show U ∉ (excluded o r b)ᶜ from fun hu => hu h),norm_zero]
    exact hc
  rw [restricted,Set.indicator_of_mem (show U ∈ (excluded o r b)ᶜ from h)]
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro j
  obtain ⟨e,rfl⟩ := (Work.E03.poleEquiv n).surjective j
  by_cases he : separation o e.1 < r
  · exact (coefficient L k o r t ht U e).trans (mul_le_mul_of_nonneg_left
      (bound k o U r hn e he hb (outside h)) (mul_nonneg (inv_pos.mpr ht).le L.cost_pos.le))
  · simp only [coordinates, Equiv.symm_apply_apply,if_neg he,norm_zero]
    exact hc

theorem sampled (L : LocalLog G) (k : Lattice.Order) (o : Site n) (r : ℕ) (hn : 2*r < n.val)
    (t b : ℝ) (ht : 0 < t) (hb : 0 ≤ b) (hq : 4*(r:ℝ)*Fintype.card PlaqAxes*b ≤ L.radius)
    (U : Config G n) (h : U ∉ excluded o r b) (e : Edge (Site n)) (he : separation o e.1 < r) :
    G.lieExp (t • restricted L k o r t b U (Work.E03.poleEquiv n e)) = Lattice.gauge (frame k o U) U e := by
  rw [restricted,Set.indicator_of_mem (show U ∈ (excluded o r b)ᶜ from h)]
  exact (exact L k o r hn t ht U hb hq (outside h) e he).2

theorem original {H : History G} (Y : H.Selected) (P : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m ≤ N → ∀ p (o : Site (H.S.side m p)) (r : ℕ),
    (scene H N p m).real (excluded o r (cool H.levels m)) ≤ (cells o r).card*vanishP H.levels m := by
  filter_upwards [rare P hG Y] with m hm N hn p o r
  letI : IsProbabilityMeasure (scene H N p m) := probability (H:=H) (p:=p) Y hn
  exact omitted _ o r _ _ fun z _ => hm N hn p z

end YM.Integration.WilsonAxialCoordinates
end
