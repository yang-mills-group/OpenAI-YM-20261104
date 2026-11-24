import YM.Integration.QLocalInheritedCoverPurchase

/-! The original tired-forest support bill before its fixed-fraction
    weakening, including the change to the funded support collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalInheritedLargeCover
open Set Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Trees RG.Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped BigOperators Classical
variable {G : Gauge}

theorem collar (G : Gauge) (s : ℝ) (j n : ℕ) {i Y : ℝ}
    (hi : 0 < i) (hY : i ≤ Y) :
    collars G Y s j n ≤ Real.exp Y * collars G i s j n := by
  let c := Y⁻¹^(n*j) * ((n*j).factorial : ℝ)
  let r := i⁻¹^(n*j) * ((n*j).factorial : ℝ)
  have hc : 0 < c := by have := hi.trans_le hY; unfold c; positivity
  have hpos := hi.trans_le hY
  have hu : c ≤ r := by unfold c r; gcongr
  have hS : 0 ≤ shiftG s ^ (n*j) := pow_nonneg (by unfold shiftG; positivity) _
  unfold collars Reserves.polyPrice
  change _*(c*_) ≤ _*(_*(r*_))
  rw [mul_left_comm (Real.exp Y) (shiftG s ^ (n*j))]
  apply mul_le_mul_of_nonneg_left _ hS
  rw [mul_comm c]
  exact mul_le_mul_of_nonneg_left
    (hu.trans (le_mul_of_one_le_right (hc.le.trans hu) (Real.one_le_exp hi.le)))
    (Real.exp_pos _).le

theorem price {z u v t w φ : ℝ} (hz : 0 < z) (hw : 0 ≤ w)
    (hrow : v ≤ t*u) (hpay : u*w ≤ z^φ) (ht : 0 ≤ t) :
    ((z^(3/8 : ℝ))^3)⁻¹ * v * (z^(3/8 : ℝ)*w) ≤ t * z^(φ-3/4) := by
  let g := z ^ (3/8 : ℝ)
  have hg : 0 < g := Real.rpow_pos_of_pos hz _
  have hpow : (g^2)⁻¹ * z^φ = z^(φ-3/4) := by
    unfold g
    rw [← Real.rpow_natCast (z^(3/8 : ℝ)) 2,← Real.rpow_mul hz.le,← Real.rpow_neg hz.le,
      ← Real.rpow_add hz]
    congr 1
    norm_num
    ring
  calc (g^3)⁻¹ * v * (g*w) = (g^2)⁻¹ * (v*w) := by field_simp [hg.ne']
    _ ≤ (g^2)⁻¹ * ((t*u)*w) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hrow hw) (by positivity)
    _ = t * ((g^2)⁻¹*(u*w)) := by ring
    _ ≤ t * ((g^2)⁻¹*z^φ) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hpay (by positivity)) ht
    _ = t*z^(φ-3/4) := by rw [hpow]

theorem relative {z Y : ℝ} (hz : 0 < z) (paid : Real.exp Y ≤ z ^ (1/80 : ℝ)) :
    Real.exp Y * z^(-(7/16 : ℝ)-3/4) ≤ z^(-(3/40 : ℝ))*z^(-(11/10 : ℝ)) := by
  apply (mul_le_mul_of_nonneg_right paid (Real.rpow_nonneg hz.le _)).trans
  rw [← Real.rpow_add hz,← Real.rpow_add hz]
  norm_num

variable {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
  {Q : ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
  {R : Rep G f} {μ q C d v Y A b r B s α a i i₀ φ : ℝ} {k j n : ℕ}
  {χ : Chi} {H : Cash W s μ L Q o α T R}

/-- All tired original field rows, at every spatial test point, for the
    regular captain of the acquired Cash. -/
theorem hit (N : Captain H j C d v Y A b r B q k χ) (grow1 : 1 ≤ grow G L s)
    (heavy : Heavy N.conduit) (arm : Armada Q L μ a s i B j k)
    (mark : grow G L s^3 ≤ Real.exp (Q.mark L μ s))
    (depth : grow G L s^3 ≤ Real.exp (Q.ε*Pressure.Stores.till s))
    (small : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (fee : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2)
    (hb : 0 < betaF G s L) (hi₀ : 0 < i₀) (hi : i₀ ≤ i)
    (pay : collars G i₀ s j n*(salary Q L μ B s j k*(1-1/2)⁻¹) ≤ betaF G s L ^ φ) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z => if Height.tired H z then N.markΦ z n else 0) a
      (Real.exp i * betaF G s L ^ (φ-3/4)) := by
  have old := Height.completed N grow1 heavy n arm mark depth small fee
  have pos : 0 < salary Q L μ B s j k := by
    unfold salary
    have := arm.earned
    have := N.balance
    positivity
  have new := price hb (w:=salary Q L μ B s j k*(1-1/2)⁻¹) (by positivity)
    (collar G s j n hi₀ hi) pay (Real.exp_pos _).le
  intro x
  apply budget_loosen (old x)
  simpa only [Height.grow,mul_assoc] using new

end YM.Integration.QLocalInheritedLargeCover
end
