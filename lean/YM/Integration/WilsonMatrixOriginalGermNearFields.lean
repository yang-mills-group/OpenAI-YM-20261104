import YM.Integration.WilsonMatrixOriginalGermSlab

/-! Before choosing a period, the actual reporting quota controls the
raw labels of the original UV observation throughout the physical mesh
slab. This includes two labels inserted at the same lattice site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermNearFields
open MeasureTheory Filter Lattice Wilson RG RG17 RG12 Spec Table OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox FVA2
open Extra.Multi.BasisCost WilsonMatrixOriginalGermConditionalMask
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Spec.Final R.family f S) (L:Layout F)
local notation:max "β" i:arg => R.family.path.levels.clock.hatBeta i

def exponent (e:ℕ):ℕ:=5+2*slots (R.family.labels.level 4)+e

def cap (m e:ℕ) (M:ℝ):ℝ:=price (R.family.localSection 4)*β m^(exponent R e)*M

theorem cutoff (r:ℝ) {N p e:ℕ} {M:ℝ} (w:R.family.label 4)
    (age:R.family.ref 4≤L.level r) (live:L.level r≤N)
    (gap:R.family.S.a (L.level r)/R.family.S.a N≤β (L.level r)) (heat:β N≤β (L.level r)^2)
    (paid:Next.UVStress.quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) w) ≤
      R.family.S.a (L.level r)^4*(β (L.level r)^e*M)) (o:Site (R.family.side N p)) (U:Config G (R.family.side N p)):
    ‖R.family.O N p (atRef L 4 r (N,p) w) o U‖ ≤ cap R (L.level r) e M:=by
  rw [WilsonMatrixTicketLanesReportedAdmission.quota R F L 4 r w age N p live] at paid
  have mass:RG12.mass R.family 4 (L.shift 4 r w)≤β (L.level r)^e*M:=
    (mul_le_mul_iff_right₀ (pow_pos (R.family.S.a_pos _) 4)).mp paid
  rw [atRef,(R.family.linearO N p 4 o).map_smul,Pi.smul_apply,smul_eq_mul,Complex.ofReal_pow]
  apply (WilsonReportingTopEnvelope.field F.room.cutoff age live (L.shift 4 r w) o U).trans
  have b (k:ℕ):0≤β k:=zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have cp:0≤price (R.family.localSection 4):=zero_le_one.trans (price_pos _)
  have sz:0≤RG12.mass R.family 4 (L.shift 4 r w):=coeff_nonneg _
  have ratio:0≤R.family.S.a (L.level r)/R.family.S.a N:=(div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)).le
  calc
    _ ≤ price (R.family.localSection 4)*β (L.level r)^5*(β (L.level r)^2)^slots (R.family.labels.level 4)*
      (β (L.level r)^e*M) := by gcongr <;> positivity [b N,b (L.level r)]
    _ = _ := by unfold cap exponent;rw [←pow_mul,pow_add,pow_add];ring

theorem joint (r:ℝ) {k N p e:ℕ} {M:Fin 2→ℝ} (mp:∀i,0≤M i) (w:Fin 2→R.family.label 4)
    (age:R.family.ref 4≤L.level r) (lower:L.level r≤k) (upper:k≤N)
    (gap:R.family.S.a (L.level r)/R.family.S.a N≤β (L.level r)) (heat:β N≤β (L.level r)^2)
    (paid:∀i,Next.UVStress.quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) (w i)) ≤
      R.family.S.a (L.level r)^4*(β (L.level r)^e*M i)) (φ:Test 2):
    cost R (p:=p) lower upper (fun i=>atRef L 4 r (N,p) (w i)) φ ≤
      (∑x:Fin 2→Site (R.family.side N p),‖WilsonExternalMeshMass.charge R.family φ x‖)*
        (6*(cap R (L.level r) e (M 0)*cap R (L.level r) e (M 1))):=by
  have pos(i):0≤cap R (L.level r) e (M i):=mul_nonneg (mul_nonneg
    (zero_le_one.trans (price_pos _)) (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) _)) (mp i)
  exact WilsonMatrixOriginalGermSlab.capped R lower upper _ φ _ pos (fun i=>cutoff R F L r (w i) age
    (lower.trans upper) gap heat (paid i))

end YM.Integration.WilsonMatrixOriginalGermNearFields
