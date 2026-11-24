import YM.RG02.Flat.Coverage

/-!
Neighborhood costs fixed geometry. After projection, no cutting inside this
collar even using a common set W for tag/slice changes. The full-domain tails
or shrinking-window analytic `jm` costs are not bounded by this result!
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.RG02.Volume
open Filter Set Function MeasureTheory Metric Lattice Exterior Tree Wilson RG Precision
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical Pointwise
variable {G : Gauge}{c f : Side}{S : StepData c f}{g : Lattice.Ratio c f}
variable (F : Forest g)(η : ChartRatio G)

lemma jacob (F : Forest S.ratio){e : ℝ}(x : AxisChart G F) (hx : x∈Metric.ball 0 e)(h : LocalRatio η)(hp : e ≤ Chart.small G η) :
    Chart.jacobian η x=η.scale^(Fintype.card F.Free) * Fk.axisJ F η x ∧ 0< Fk.axisJ F η x := by
   have HE : e<η.radius := lt_of_le_of_lt (hp.trans (min_le_left ..)) (half_lt_self h.patch)
   have hv i : 0<η.J (x i) := h.pos _ (mem_ball_zero_iff.mpr <|
       lt_of_le_of_lt (norm_le_pi_norm x i) (mem_ball_zero_iff.mp hx|>.trans HE))
   constructor
   · unfold Chart.jacobian; rw [show η.scale^Fintype.card F.Free= ∏ _ : F.Free,η.scale by simp]
     unfold Fk.axisJ; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _
     exact max_eq_left (mul_pos h.scale (hv ..)).le
   exact Finset.prod_pos fun i _=> hv i

private lemma home (e : ℝ)(he : 0<e) : (1 : F.Slice G)∈ Chart.chamber G F.Free e := fun _ _=> ⟨0, mem_ball_self he,G.mat_lieExp_zero⟩

private lemma touches : coordinate F (1 : F.Slice G) 0=1 := by
   unfold coordinate; rw [mul_one]; funext i; exact G.mat_lieExp_zero

/-- Even parameter-dependent domains with suitable eventual guard are
allowed for the coefficient calculation. (No masks in this test.) -/
def Suitable (r : ℝ)(q : ℝ→ F.Slice G)(U : ℝ→Set (F.Slice G)) :=
    (∀ᶠ t in Tested.germ, MeasurableSet (U t) ∧ U t ⊆ block F r (q t)) ∧
      Therm.Collars r (fun t => Volume.inside F r (q t) (U t) t)

private lemma throats (r : ℝ)(h:0<r){q : ℝ→ F.Slice G}(hq : Tendsto q Tested.germ (𝓝 1)){V : Set (F.Slice G)}(hv : V∈𝓝 1)(hm : MeasurableSet V) : Therm.Collars r fun t=> Volume.inside F r (q t) V t := by
   have hk : Set.preimage (uncurry (coordinate F)) V ∈ 𝓝 ((1:F.Slice G), (0:AxisChart G F)) := (coordinate_cont F (G:=G)).continuousAt (by change V∈𝓝 (coordinate F 1 0); rw [touches F]; exact hv)
   obtain ⟨L,hL,D,hD,hI⟩ := mem_nhds_prod_iff.mp hk
   obtain ⟨ε,hε,hB⟩ := Metric.mem_nhds_iff.mp hD
   let u:= min ε r
   refine ⟨u,lt_min hε h,min_le_right ε r,?_⟩
   filter_upwards [hq hL] with t ht
   refine ⟨inside_meas F r t (q t) hm,?_,?_⟩
   · intro x hh
     change coordinate F (q t) (t • x)∈V ∧ t • x∈ ball 0 r
     change t • x∈ball (0:AxisChart G F) u at hh
     refine ⟨hI (a:=(q t,t • x)) ?_,ball_subset_ball (min_le_right ..) hh⟩
     exact ⟨ht,hB (ball_subset_ball (min_le_left ..) hh)⟩
   intro v hv; change (t • v) ∈ (coordinate F (q t) ⁻¹' V) ∩ ball 0 r at hv; exact hv.2

/-- For any supplied price radius, can follow even a translating chart by a
fixed collar in physical fields. -/
lemma coverage {q : ℝ→ F.Slice G}(hq : Tendsto q Tested.germ (𝓝 1))(hη : LocalRatio η){r : ℝ}(h : 0<r)(hp : r ≤ Chart.small G η) :
    ∃ W∈𝓝 (1 : F.Slice G), MeasurableSet W ∧ ∀ (w : Set (F.Slice G)), w∈𝓝 1→ MeasurableSet w → w⊆W →
      Suitable F r q (fun _=>w) := by
   let f (x : F.Slice G × F.Slice G) := x.1*x.2⁻¹
   have he := show Tendsto f (𝓝 (1,1)) (𝓝 1) from by
      simpa [f] using! (continuous_fst.mul continuous_snd.inv : Continuous f).tendsto (1,1)
   have ht := he (Chart.Ratio.chamber_open hη hp |>.mem_nhds (home F r h))
   obtain ⟨W,H,he⟩ := mem_nhds_prod_iff.mp ht
   obtain ⟨P,hP,hd⟩ := he
   -- open W thinner
   obtain ⟨w,hW,ho,hw⟩ := _root_.mem_nhds_iff.mp H
   refine ⟨w,ho.mem_nhds hw,ho.measurableSet,fun V hv hm hx => ⟨?_,?_⟩⟩
   · filter_upwards [hq hP] with t ht
     exact ⟨hm,fun y hy => hd (show (y,q t) ∈ W ×ˢ P from ⟨hW (hx hy),ht⟩)⟩
   exact throats F r h hq hv hm

end YM.RG02.Volume
