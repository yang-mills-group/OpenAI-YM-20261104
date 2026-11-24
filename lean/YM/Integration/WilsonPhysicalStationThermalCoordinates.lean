import YM.Integration.WilsonPhysicalStationThermalPair

/-! The inverse reporting coordinates of the whole submitted original field.
The leg price cancels on the same elected thermal table at every rank. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalCoordinates
open Function Filter Finset Lattice RG Wilson Cells Labels Source Next.Rank Next.Rank.East Next.Rank.Price
open MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationTableJump (table)
open WilsonPhysicalStationThermalPair (raw)
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) {N p:ℕ}
    (checked:A.checked f H D) (top:A.k<N)
local notation "F₀" => R.family.labels.level d
local notation "τ" => shrink R.family A.k N p
local notation "M₀" => Station.mag R.family.path.levels A.b A.k

def filed (N p:ℕ) : R.family.label d →ₗ[ℂ] R.family.label d :=
  (weightTag R.family d (M₀)⁻¹).comp (((F₀).scaled (shrink R.family A.k N p)).comp (A.R N p d))

def word : R.family.label d →ₗ[ℂ] R.family.label d :=
  (table R A d (p:=p) checked top).symm.toLinearMap.comp
    (((F₀).scaled (τ)⁻¹).comp (weightTag R.family d (M₀)))

theorem restored (x:R.family.label d) :
    raw R A d (p:=p) checked top (filed R A d N p x)=x := by
  apply (table R A d (p:=p) checked top).injective
  rw [WilsonPhysicalStationThermalPair.raw, LinearEquiv.apply_symm_apply]
  let u:= (A.R N p d) x
  have hp:= (shrink_pos R.family R.makes top.le p).ne'
  have hm:= (Station.mag_pos R.family.path.levels A.b A.k).ne'
  have invTag (v:R.family.label d) :
      weightTag R.family d (M₀) (weightTag R.family d (M₀)⁻¹ v)=v := by
    ext i
    change ((M₀:ℝ):ℂ)^((F₀).grades i).1 * (((((M₀)⁻¹:ℝ):ℂ)^((F₀).grades i).1) * v i)=v i
    rw [Complex.ofReal_inv,inv_pow,← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hm)),one_mul]
  change (F₀).scaled (τ)⁻¹ (weightTag R.family d M₀ (weightTag R.family d (M₀)⁻¹ ((F₀).scaled τ u)))=u
  rw [invTag]
  simpa only [inv_inv] using (F₀).scaled_inv (t:=(τ)⁻¹) (inv_ne_zero hp) u

theorem expands (x:R.family.label d) :
    x=∑ b, (filed R A d N p x b) • raw R A d (p:=p) checked top (Pi.single b 1) := by
  let c:=filed R A d N p x
  have expand : (∑ b,c b • (Pi.single b 1:R.family.label d))=c := by
    ext a
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  calc
    x=word R A d (p:=p) checked top c := (restored R A d checked top x).symm
    _=word R A d (p:=p) checked top (∑ b,c b • Pi.single b 1) := congrArg _ expand.symm
    _=_ := by rw [map_sum]; simp only [map_smul]; rfl

include top in
theorem original (x:R.family.label d) :
    (∑ a,‖filed R A d N p x a‖*(τ)⁻¹^((F₀).grades a).2) =
      ∑ a,(M₀)⁻¹^((F₀).grades a).1 * ‖(A.R N p d x) a‖ := by
  have hp:=shrink_pos R.family R.makes top.le p
  have hm:=Station.mag_pos R.family.path.levels A.b A.k
  apply Finset.sum_congr rfl; intro a _
  let m:ℝ:=M₀
  let t:ℝ:=τ
  let w:=((F₀).grades a).1
  let z:=((F₀).grades a).2
  let u:ℂ:=(A.R N p d x) a
  change ‖(↑(m⁻¹):ℂ)^w * ((↑(t^z):ℂ)*u)‖ * (t⁻¹)^z = (m⁻¹)^w*‖u‖
  have h₁:0<t:=hp
  have h₂:0 < m:=hm
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr h₂.le),
    norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg h₁.le _),inv_pow t z]
  field_simp [h₁.ne']


end YM.Integration.WilsonPhysicalStationThermalCoordinates
end
