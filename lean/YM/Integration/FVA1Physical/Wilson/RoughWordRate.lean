import YM.Integration.FVA1Physical.Wilson.RoughWords
import YM.Integration.FVA1Physical.Wilson.ChartEnvelope

/-! The boundary estimate in the complete regular row, summed before
choosing independent probes. It costs an arbitrarily small inverse power
at an arbitrarily rough gauge background with the same physical collar. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset MvPolynomial Lattice RG YM.Wilson Exterior Precision
open MSbar MSbar.Whisk MSbar.Mosaic MSbar.Mosaic.Issue MSbar.Measuring MSbar.Lis MSbar.Cacao MSbar.Bakery
open Push Push.Uniform
open scoped Classical Topology

theorem exterior_word_toll (m : ℕ) (C b Q : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ y : ℝ in atTop, Real.exp (-(αm y/2*(spotN y:ℝ)))*
       (2*(C*y)*(y^b*(1+C*y)^(m+1))) ≤ y^(-Q) := by
  have unit : Mosaic.Run atTop id id 1 :=
    (Mosaic.Run.core (X:=id) tendsto_id 1).alter (Eventually.of_forall fun y=>Real.rpow_one y)
  have k:=unit.mulK tendsto_id C
  have growth:=(((Mosaic.Run.token (X:=id) tendsto_id 1).loosen (zero_le_one)).addR tendsto_id k).raise tendsto_id (m+1)
  have poly:=(k.mulK tendsto_id 2).mulR tendsto_id ((Mosaic.Run.core (X:=id) tendsto_id b).mulR tendsto_id growth)
  have decay:=(Mosaic.Issue.nearB (X:=id) tendsto_id 1 zero_lt_one 0 0).1
  have van:=Mosaic.Van.mulL tendsto_id poly decay
  filter_upwards [van (-Q-1) (-Q) (by linarith),eventually_ge_atTop (1:ℝ)] with y hy y1
  have y0 := zero_le_one.trans y1
  have a0 : 0 ≤ αm y := zpow_nonneg (sq_nonneg _) _
  have th : thorn y 0 ≤ αm y/2 := by
    change αm y/((0+10:ℕ):ℝ) ≤ αm y/2
    norm_num
    linarith
  have E : -(αm y/2*(spotN y:ℝ)) ≤ -thorn y 0*spotN y := by
    rw [neg_mul]
    exact neg_le_neg (mul_le_mul_of_nonneg_right th (Nat.cast_nonneg _))
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr E) (by positivity)).trans ((le_abs_self _).trans hy)

theorem rough_configuration_words (G : Gauge) (m s : ℕ) (b Q : ℝ) :
    ∀ᶠ y : ℝ in atTop, ∀ (n : Side) (z : Site n) (g : ℝ), lensT y g →
      ∀ f : Pot (Primary n G), f.totalDegree ≤ m →
      Vault (Measuring.chart n G) {z} (αm y) s m 0 f (y^b) → ∀ k : ℕ,
      ∀ U V : List (Primary n G)→ Config G n,
      (∀ L (e : Edge (Site n)), e.1∈boxX y z → U L e=V L e) →
      Yarn k (fun L=>spread (Measuring.chart n G) {z} (αm y/2) s L*
        |read (chartLog g (V L)) L f-read (chartLog g (U L)) L f|) ≤ y^(-Q) := by
  let C:=(LocalH.geom_patch G).choose
  have hC:0 ≤ C:=(LocalH.geom_patch G).choose_spec.1.le
  filter_upwards [exterior_word_toll m (2*C) b Q (by positivity), eventually_ge_atTop (1:ℝ)] with y toll y1
  intro n z g band f deg paid k U V same
  have cap(W:Config G n): ‖chartLog g W‖ ≤ (2*C)*y := (chartLog_norm_bound g W).trans
    ((mul_le_mul_of_nonneg_right (inverse_clock_le_linear y1 band).2 hC).trans_eq (by ring))
  have far (L:List (Primary n G)) (i:Primary n G) (hi:separation z (Measuring.chart n G i)<spotN y) :
      chartLog g (U L) i=chartLog g (V L) i := by
    change g⁻¹*(logWithin G (U L (rope i))) i.2=g⁻¹*(logWithin G (V L (rope i))) i.2
    rw [same L (rope i) (halo_spec.mpr ⟨_,mem_singleton_self z,hi.le⟩)]
  exact (rough_independent_words (Measuring.chart n G) z m s k (spotN y) (zpow_nonneg (sq_nonneg _) _)
    f deg paid (fun L=>chartLog g (U L)) (fun L=>chartLog g (V L)) (by positivity)
    (fun L=>cap _) (fun L=>cap _) far).trans toll

end YM.Integration.FVA1Physical.Wilson
