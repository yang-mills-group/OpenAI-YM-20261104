import YM.Integration.WilsonThermometerSameWalkTransparent

/-! Original field restoration at the native reporting engineering weight. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkTester
open Function Filter MeasureTheory Lattice Wilson RG Source Labels RG.Shoot
open Extra.Histories Relay PhysicalNext Repeat Legato Graces Roost
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local MergeProof Accent
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG16.Guarding
open WilsonThermometerSameWalkMotion WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => R.family.labels.level d
local notation "S₀" => R.family.localSection d
local notation "A₀" => R.family.params
local notation "s" => R.family.S.scale
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "κ" i:max => LocalComparison.forcedDivisor R.family i

def engineering (base i:ℕ):ℝ:=((C₀).S.a base/(C₀).S.a i)^d

theorem positive (base i:ℕ):0<engineering R d base i:=pow_pos (div_pos ((C₀).S.a_pos _) ((C₀).S.a_pos _)) _

/-- The expense is weighted separately for each original arm. -/
def need (base i:ℕ) (ε:ℝ) (y:Palette (C₀) d):ℝ:=
  engineering R d base i*Real.exp (ε*(s i-s base))*(1+size y)

def radius (base i t:ℕ) (ε:ℝ) (y:Palette (C₀) d):ℝ:=(β i^t*need R d base i ε y)⁻¹

theorem charged (base i t:ℕ) (ε:ℝ) (y:Palette (C₀) d):0 < radius R d base i t ε y:=by
  have scale:=positive R d base i
  have clock:=zero_lt_one.trans ((C₀).path.levels.fits.delayed i)
  have mass:=size_ge y
  unfold radius need
  positivity

/-- Exact original numerator on every held group field, with the actual public
a_base^d at the source and its original engineering fee on the complete output. -/
theorem restored {base i N per:ℕ} (away:base ≤ i) (live:i ≤ N)
    (r:Emblems (C₀) d) (z:Site ((C₀).side N per)) (y:Palette (C₀) d) (x:(C₀).label d)
    (original:((C₀).factory d N per).terminal (finer r (away.trans live) y (primaryLetter d))=
      (((C₀).S.a base:ℂ)^d)⁻¹ • x)
    (P:Rep G ((C₀).side i per)) (o:Site ((C₀).side i per)) (W:Coefficient (F₀) ((C₀).side i per))
    (form:W.Format o A₀ P) {u:ℝ} (rent:W.remBound o P (κ i) u)
    (whole:W.density o S₀ P=WilsonThermometerSameWalkArm.enteredField R z r live (finer r away y)):
    let T:=stretch (engineering R d base i:ℂ) W
    T.Format o A₀ P ∧ T.remBound o P (κ i) (engineering R d base i*u) ∧
      T.density o S₀ P=dyes (C₀) i N per live ((C₀).O N per x z):=by
  intro T
  have scaled:=stretch_rem (engineering R d base i:ℂ) rent
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positive R d base i)] at scaled
  refine ⟨stretch_format _ form,scaled,?_⟩
  have hscale:(engineering R d base i:ℂ)*((C₀).S.a i:ℂ)^d*(((C₀).S.a base:ℂ)^d)⁻¹=1:=by
    unfold engineering
    push_cast
    rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero _ <| Complex.ofReal_ne_zero.mpr ((C₀).S.a_pos i).ne'),
      mul_inv_cancel₀ (pow_ne_zero _ <| Complex.ofReal_ne_zero.mpr ((C₀).S.a_pos base).ne')]
  rw [enrolled R z r away live y] at whole
  unfold WilsonThermometerSameWalkMotion.field at whole
  change W.density o S₀ P=dyes (C₀) i N per live (((C₀).S.a i:ℂ)^d • (C₀).O N per
    (((C₀).factory d N per).terminal (finer r (away.trans live) y (primaryLetter d))) z) at whole
  have originalO: (C₀).O N per ((((C₀).S.a base:ℂ)^d)⁻¹ • x) z=
    (((C₀).S.a base:ℂ)^d)⁻¹ • (C₀).O N per x z:=((C₀).linearO N per d z).map_smul _ _
  rw [original,originalO,dye_pitch,dye_pitch] at whole
  funext U
  change (stretch (engineering R d base i:ℂ) W).density o S₀ P U=_
  rw [stretch_density,congrFun whole U]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [←mul_assoc,←mul_assoc,hscale,one_mul]

/-- A single ordered fixed power before the UV and the period pays each named
regular and once-divided hard stock after its physical engineering restoration. -/
theorem paid (simple:G.Simple) (b q:ℕ) (A:ℝ) (hA:0 ≤ A):
    ∀ᶠ i:ℕ in atTop,∀ base ε (y:Palette (C₀) d),
      radius R d base i (b+q+1) ε y *
        (engineering R d base i*(A*WilsonThermometerSameWalkIncome.fee R base b ε (1+size y) i)) ≤
        ((β i)^q)⁻¹:=by
  filter_upwards [RG01.Physical.nextHat simple (C₀).path.levels,
    (RG01.Physical.hats simple (C₀).path.levels).eventually_ge_atTop (A*2^b)] with i adjacent place base ε y
  have hb:0<β i:=zero_lt_one.trans ((C₀).path.levels.fits.delayed i)
  have mass:0<1+size y:=by have:=size_ge y;linarith
  have scale:=positive R d base i
  have epos:=Real.exp_pos (ε*(s i-s base))
  have admit:0<β i^(b+q+1)*need R d base i ε y:=by unfold need;positivity
  have bill:A*(β (i+1))^b ≤ (β i)^(b+1):=calc
    _ ≤ A*(2*β i)^b:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_lt_one.trans ((C₀).path.levels.fits.delayed (i+1))).le adjacent _) hA
    _ = (A*2^b)*(β i)^b:=by rw [mul_pow];ring
    _ ≤ (β i)*(β i)^b:=mul_le_mul_of_nonneg_right place (pow_nonneg hb.le _)
    _ = (β i)^(b+1):=by rw [pow_succ];ring
  calc
    _ = A*(β (i+1))^b/(β i)^(b+q+1):=by
      unfold radius need WilsonThermometerSameWalkIncome.fee
      field_simp [scale.ne',mass.ne',hb.ne',epos.ne']
    _ ≤ _:=by
      apply (div_le_iff₀ (pow_pos hb _)).mpr
      apply bill.trans_eq
      rw [show b+q+1=q+(b+1) by omega,pow_add (β i) q (b+1),←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hb.ne'),one_mul]

end YM.Integration.WilsonThermometerSameWalkTester
end
