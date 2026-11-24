import YM.Integration.WilsonRootedOPEPointNormalizer
import YM.Integration.WilsonRootedGermSlabCurvature

/-! The inverse of every original normalized point mark can be restored at
its own dated regulator, and on the actual growing interval of an earlier one. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPointRestoration
open Function Filter MeasureTheory Finset Lattice Wilson RG Marker Source Labels
open PhysicalNext.Repeat.Legato LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ActualOriginalQInitialInput WilsonRootedOPEPointNormalizer Pert.Asymptotics
open private square from YM.Integration.WilsonRootedGermSparseQuota
open scoped BigOperators Classical Topology
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G} (R:Run G) (simple:G.Simple)
variable (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B) (μ:ℝ) (orders:V→ℕ)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "s" => WilsonRootedOPEPointNormalizer.degree R Q u orders

private theorem spend (n ℓ q:ℕ) {M C b g ε:ℝ} (mp:0≤M) (cp:0<C) (bp:0≤b) (gp:0≤g) (ep:0<ε)
    (fee:M≤C*b^n) (band:g^2*b≤2) :
    M^ℓ*(ε/(C^ℓ*2^(n*ℓ))*g^(q+2*(n*ℓ))) ≤ ε*g^q := by
  let δ:=ε/(C^ℓ*2^(n*ℓ))
  have dp:0<δ:=div_pos ep (mul_pos (pow_pos cp _) (pow_pos zero_lt_two _))
  have seen:(g^2*b)^(n*ℓ)≤(2:ℝ)^(n*ℓ):=pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) bp) band _
  calc
    _ ≤ (C*b^n)^ℓ*(δ*g^(q+2*(n*ℓ))) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ mp fee _) (mul_nonneg dp.le (pow_nonneg gp _))
    _ = δ*g^q*C^ℓ*(g^2*b)^(n*ℓ) := by simp only [pow_add,pow_mul,mul_pow];ring
    _ ≤ δ*g^q*C^ℓ*2^(n*ℓ) := mul_le_mul_of_nonneg_left seen (mul_nonneg (mul_nonneg dp.le (pow_nonneg gp _)) (pow_nonneg cp.le _))
    _ = _ := by dsimp only [δ];field_simp [(pow_ne_zero ℓ cp.ne'),(pow_ne_zero (n*ℓ) (by norm_num:(2:ℝ)≠0))]

include simple in
theorem dated (ℓ q:ℕ) {ε:ℝ} (ep:0<ε) : ∃δ>0,∀(J:Request V) (A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V)) (o:V→Site (R.family.side (d.level+1) d.period)),
    let M:=normalizer R simple u J A d Q o μ orders
    let g:=regulatorRun R.family d.cutoff d.period d.cutoff
    M^ℓ*(δ*g^(q+2*(s*ℓ))) ≤ ε*g^q := by
  obtain ⟨C,cp,fee⟩:=WilsonRootedOPEPointNormalizer.purchased R simple Q u μ orders
  refine ⟨ε/(C^ℓ*2^(s*ℓ)),div_pos ep (mul_pos (pow_pos cp _) (pow_pos zero_lt_two _)),?_⟩
  intro J A d o M g
  have pos:0≤M:=zero_le_one.trans (le_max_left _ _)
  exact spend s ℓ q pos cp (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) (inv_nonneg.mpr (Real.sqrt_nonneg _)) ep
    (fee J A d o) (square R (p:=d.period) (le_refl d.cutoff))

include simple in
theorem earlier (ℓ q:ℕ) {ε:ℝ} (ep:0<ε) : ∃δ>0,∀ᶠ k:ℕ in atTop,∀(J:Request V) (A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V)) (o:V→Site (R.family.side (d.level+1) d.period)),
    k≤d.cutoff → d.cutoff≤k+WilsonRootedGermSlabCurvature.span R simple k →
    let M:=normalizer R simple u J A d Q o μ orders
    let g:=regulatorRun R.family d.cutoff d.period k
    M^ℓ*(δ*g^(q+2*((2*s)*ℓ))) ≤ ε*g^q := by
  obtain ⟨C,cp,fee⟩:=WilsonRootedOPEPointNormalizer.purchased R simple Q u μ orders
  refine ⟨ε/(C^ℓ*2^((2*s)*ℓ)),div_pos ep (mul_pos (pow_pos cp _) (pow_pos zero_lt_two _)),?_⟩
  filter_upwards [(WilsonMatrixOriginalGermSlabCalendar.growing R simple).choose_spec.2] with k width
  intro J A d o live within M g
  have heat : β d.cutoff ≤ (β k)^2 := (width d.cutoff live within).2
  have pos : 0≤M := zero_le_one.trans (le_max_left _ _)
  have fine : β d.cutoff^s ≤ β k^(2*s) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) heat _
  exact spend (2*s) ℓ q pos cp (zero_le_one.trans (R.family.path.levels.fits.delayed _).le)
    (inv_nonneg.mpr (Real.sqrt_nonneg _)) ep ((fee J A d o).trans (mul_le_mul_of_nonneg_left fine cp.le)) (square R (p:=d.period) live)

end YM.Integration.WilsonRootedOPEPointRestoration
