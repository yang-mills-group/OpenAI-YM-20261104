import YM.Integration.WilsonCutoffDiscrepancyPrice
import YM.OPE.Prices.Stock

/-! Physical units, the marker bought on the same Wilson clock, and the
vacuum cost at the stock port. All three appear on the original signed bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSignedReportPrice

open Filter Set Lattice Wilson RG Source Push Push.RelayDifference MergeProof Accent
open PhysicalNext.Repeat.Legato Extraction Cells Extra.Histories Labels
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {d : ℕ}

def marker (C : Family G) (d k : ℕ) : ℝ :=
  (Bandage.fly C.path.levels d k / 4)⁻¹

theorem marker_pos (C : Family G) (d k : ℕ) : 0 < marker C d k :=
  inv_pos.mpr (div_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans (C.path.levels.fits.delayed k)) _)) (by norm_num))

theorem marker_paid (C : Family G) (hG : G.Simple) (d : ℕ) :
    FullVolume.Sluggish C (fun i => marker C d i.1) := by
  have hβ := (FullVolume.borrowed (C:=C) (W:=fun i => C.path.levels.clock.hatBeta i)
    (beta_slow hG)).pow (winter G d)
  apply ((FullVolume.Sluggish.const (C:=C) (4:ℝ)).mul hβ).reduce
  apply Eventually.of_forall
  intro i
  change ‖((C.path.levels.clock.hatBeta i.1 ^ winter G d)⁻¹ / 4)⁻¹‖ ≤ _
  rw [inv_div,div_inv_eq_mul]

def conversion (C : Family G) (d m k : ℕ) : ℝ :=
  stakes C m k * ((C.S.a k)^d)⁻¹ * marker C d k

theorem conversion_pos (C : Family G) (d m k : ℕ) : 0 < conversion C d m k :=
  mul_pos (mul_pos (Real.exp_pos _) (inv_pos.mpr (pow_pos (C.S.a_pos _) _)))
    (marker_pos C _ _)

theorem calendar (C : Family G) (hG : G.Simple) (B : Stock.Tabs C.path.levels)
    (d : ℕ) {δ : ℝ} (hd : 0 < δ) : ∀ᶠ m in atTop,
    let k := Stock.Tabs.chosen C.path.levels 1 B m
    (C.S.a k)^d * conversion C d m k ≤ Real.exp (δ*C.S.scale k) := by
  let k := Stock.Tabs.chosen C.path.levels 1 B
  have grow : Tendsto k atTop atTop :=
    tendsto_atTop_mono (fun m => (Stock.Tabs.opened C.path.levels 1 B m).1) tendsto_id
  have pos := C.S.divergent.eventually_gt_atTop (0:ℝ)
  have height : OPE.Height C.S atTop C.S.scale (fun m => m) 1 :=
    ⟨tendsto_id,tendsto_const_nhds.congr' (pos.mono fun m hm => (div_self hm.ne').symm)⟩
  have hx := OPE.stock_price B hG height C.S.divergent (δ/2) (half_pos hd)
  have hy := FullVolume.late.mp ((marker_paid C hG d).est (half_pos hd))
  filter_upwards [hx,grow.eventually hy] with m h₁ h₂
  have h₃ : stakes C m (k m) ≤ Real.exp ((δ/2)*C.S.scale (k m)) := by
    apply (Real.le_norm_self _).trans
    apply h₁.trans
    apply Real.exp_le_exp.mpr
    simpa only [zero_add] using mul_le_mul_of_nonneg_left
      ((OPE.scale_mono C.S).monotone (Stock.Tabs.opened C.path.levels 1 B m).1) (half_pos hd).le
  have hi : 0 < C.S.a (k m)^d := pow_pos (C.S.a_pos _) _
  change C.S.a (k m)^d * conversion C d m (k m) ≤ _
  calc
    _ = stakes C m (k m) * marker C d (k m) := by unfold conversion; field_simp
    _ ≤ Real.exp ((δ/2)*C.S.scale (k m))*Real.exp ((δ/2)*C.S.scale (k m)) :=
      mul_le_mul h₃ (h₂ 0) (marker_pos C d _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

variable {V : SectionData (C.labels.level d)} {E : ℕ → ℝ}
variable {P : ℕ → ℕ → (C.label d ≃ₗ[ℂ] C.label d)}
variable {U : ℕ → ℕ → (C.labels.level d).Index → C.label d}

def column (V : SectionData (C.labels.level d)) (N p : ℕ) (u : (C.labels.level d).Index → C.label d)
    (j : (C.labels.level d).Index) (a : Motion) : Config G (C.side N p) → ℂ :=
  Motion.dance a (initial V C.path N p (Size.axis _ j) 0 - initial (C.localSection d) C.path N p (u j) 0)

theorem receipt (h : Hearth V (Bandage.fly C.path.levels) E P U) :
    ∀ᶠ N : ℕ in atTop, ∀ p k m, C.ref d ≤ k → k < N →
      Stock.Tabs.opens C.path.levels 1 m k → ∀ j a (hm : m ≤ N),
      (center C.S p hm 0).rootTest (C.beta N p) (column V N p (U N p) j a) ≤
        conversion C d m k * WilsonCutoffDiscrepancyPrice.room C E k := by
  have he : FullVolume.Sluggish C (fun i => E i.1) :=
    FullVolume.borrowed (W:=E) (h.coined Order.full)
  filter_upwards [h.stamped] with N hN
  intro p k m hk hkn op j a hm
  have bound := (hN p).2.2 j k m hk hkn op a hm
  apply bound.trans
  have hs := (OPE.scale_mono C.S).monotone hkn.le
  have hE := (WilsonCutoffDiscrepancyPrice.heard C E he k).2 N
  rw [WilsonCutoffDiscrepancyPrice.price,max_eq_right (sub_nonneg.mpr hs)] at hE
  have hE' := (mul_le_mul_of_nonneg_right (le_abs_self (E N))
    (Real.exp_pos (-gamma*(C.S.scale N-C.S.scale k))).le).trans hE
  apply le_trans _ (mul_le_mul_of_nonneg_left hE' (conversion_pos C d m k).le)
  have exp_split : Real.exp (-gamma*(C.S.scale N-C.S.scale k)) =
      Real.exp (gamma*C.S.scale k) * Real.exp (-gamma*C.S.scale N) := by
    rw [← Real.exp_add]; congr 1; ring
  apply le_of_eq
  unfold cider conversion marker flight
  rw [alto_norm,exp_split,div_eq_mul_inv]
  ring

end YM.Integration.WilsonSignedReportPrice
