import YM.Integration.FVA1Physical.Wilson.BankOrbit
import YM.Integration.FVA1Physical.Wilson.RoughWordRate
import YM.Integration.FVA1Physical.Wilson.PhysicalFieldOrbit

/-! Exterior locality after *any fixed number of independent normalized RG
updates*. The truncation is kept as one complete represented polynomial,
including the whole sum of rooted spatial derivatives on independently
chosen rough exterior gauge fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset MvPolynomial Lattice RG YM.Wilson Precision
open MSbar MSbar.Cacao MSbar.Lis MSbar.Whisk MSbar.Mosaic MSbar.Measuring MSbar.Bakery MSbar.Rolling MSbar.Bulk
open Push Push.Uniform
open scoped Classical Topology
variable {G:Gauge}

theorem bank_exterior_words (G:Gauge) (m s p:ℕ) (b Q:ℝ) {C:ℝ} (hC:0 ≤ C) :
    ∀ᶠ y:ℝ in atTop,∀ (n:Side) (z:Site n) (T:Nesting G n),BankPaid z y s p m b T →
      ∀ i≤p,∀ (g:ℝ), |g⁻¹| ≤ C*y → ∀ (k:ℕ) (U V:List (Primary n G)→ Config G n),
      (∀ L (e:Edge (Site n)),e.1∈boxX y z → U L e=V L e) →
      let f:=PowerSeries.coeff i T
      Yarn k (fun L=>spread (Measuring.chart n G) {z} (αm y/2) s L *
        |read (chartLog g (V L)) L f-read (chartLog g (U L)) L f|) ≤ y^(-Q) := by
  let r:=(LocalH.geom_patch G).choose
  have r0:0 ≤ r := (LocalH.geom_patch G).choose_spec.1.le
  filter_upwards [exterior_word_toll m (C*r) b Q (mul_nonneg hC r0),eventually_ge_atTop (0:ℝ)] with y toll y0
  intro n z T bank i hi g hg k U V same f
  have cap (W:Config G n) : ‖chartLog g W‖ ≤ (C*r)*y := (chartLog_norm_bound g W).trans
    ((mul_le_mul_of_nonneg_right hg r0).trans_eq (by ring))
  have far (L:List (Primary n G)) (i:Primary n G) (hi:separation z (Measuring.chart n G i)<spotN y) :
      chartLog g (U L) i=chartLog g (V L) i := by
    change g⁻¹*(logWithin G (U L (rope i))) i.2=g⁻¹*(logWithin G (V L (rope i))) i.2
    rw [same L (rope i) (halo_spec.mpr ⟨_,mem_singleton_self z,hi.le⟩)]
  exact (rough_independent_words (Measuring.chart n G) z m s k (spotN y) (zpow_nonneg (sq_nonneg _) _)
    f (bank i hi).1 (bank i hi).2 (fun L=>chartLog g (U L)) (fun L=>chartLog g (V L))
    (by positivity) (fun L=>cap _) (fun L=>cap _) far).trans toll

end YM.Integration.FVA1Physical.Wilson
