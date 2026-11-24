import YM.Integration.WilsonThermometerInversionFaces
import YM.Integration.WilsonThermometerNumericalStation
import YM.Integration.WilsonThermometerFrozenRevaluation

/-! At the deployed top coupling the finite inversion expansion uses
exactly the original cutoff observables, including the unit coordinate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionBirth
open Function Finset Lattice Wilson RG Source Labels Marker Next.Rank
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneRead ActualRunPhysicalPages
open WilsonThermometerInversionFaces
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {V T:Type} [Fintype V] [DecidableEq V] (d:V→ℕ)
def rawWord {n:Side} (g τ:ℝ) (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ)
    (j:V) (u:ℝ) (x:T) (y:Site n) (U:Config G n) :=
    ∑ a:Choice R d j,WilsonThermometerFrozenCopies.word R d g τ v t (entry R d j a) u x y U

variable (N per:ℕ) (o:V→Site (R.family.side N per)) (w:(j:V)→R.family.book.Ref (d j))
    (t:V→T→ℂ) (x:T) (U:Config G (R.family.side N per))
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per N
local notation "τ" => (R.family.path.rep N per N).p.threshold
local notation "v" => fun j=>Price.awake R.family (d j) N N per (w j)
private theorem read (i:Entry R d) :
    (((g)^(d (root R d i)+1):ℝ):ℂ)⁻¹*
      WilsonThermometerFrozenCopies.word R d (g) (τ) (v) t i (g) x (o (root R d i)) U =
    (rows R d o 1 (g) (τ) (v) t i).nominal (g) x U := by
  have live: (g)≠0 := (IterationFour.Currency.g_pos R.makes N per N le_rfl).ne'
  rw [WilsonThermometerFrozenRevaluation.at_birth R d (g) (τ) (v) t i x (o (root R d i)) U live,
    nominal,WilsonThermometerFrozenSockets.separated R d (g) (τ) (v) i]
  have e (a:ℕ) : (g)^(-(a:ℤ)) * ((g)/(τ))^a = (τ)⁻¹^a := by
    rw [zpow_neg,zpow_natCast,←inv_pow,←mul_pow,div_eq_mul_inv,←mul_assoc,inv_mul_cancel₀ live,one_mul]
  have eq := congrArg Complex.ofReal (e (pole R d i))
  simp only [Complex.ofReal_mul,Complex.ofReal_zpow] at eq
  linear_combination -(t (root R d i) x * scalar R d 1 1 (v) i * ↑((raw R d i).unmasked U (o (root R d i)))) * eq

theorem one (j:V) (ref:R.family.ref (d j)≤N) :
    (((g)^(d j+1):ℝ):ℂ)⁻¹ * rawWord R d (g) (τ) (v) t j (g) x (o j) U =
      t j x * R.family.O N per (w j) (o j) U := by
  unfold rawWord
  rw [mul_sum]
  have clip (a:Choice R d j) : (((g)^(d j+1):ℝ):ℂ)⁻¹ *
      WilsonThermometerFrozenCopies.word R d (g) (τ) (v) t (entry R d j a) (g) x (o j) U =
      (rows R d o 1 (g) (τ) (v) t (entry R d j a)).nominal (g) x U := by
    simpa only [site] using read R d N per o w t x U (entry R d j a)
  simp_rw [clip]
  rw [Fintype.sum_sum_type,Fintype.sum_unique]
  change (rows R d o 1 (g) (τ) (v) t (.inl j)).nominal (g) x U+
      ∑s:WilsonOriginalStarLaurentWallet.Socket R (d j),
        (rows R d o 1 (g) (τ) (v) t (.inr ⟨j,s⟩)).nominal (g) x U=_
  rw [scalar_read,monomials R d 1 (v) t N per N le_rfl o j x U,←mul_add]
  have unit : ((v) j) 0 + kernel R N per N (d j) ((R.family.labels.level (d j)).core ((v) j)) (o j) U =
      kernel R N per N (d j) ((v) j) (o j) U :=
    (WardBin.write_unitpart (R.family.localSection (d j)) (R.makes.sections (d j)) (τ)
    ((v) j) (expandAt (o j) U)).symm
  rw [unit,WilsonPositionThermometerStationBirth.kernel R N per (d j) ref (w j) (o j)]

theorem exact (L:ℂ→L[ℝ]ℝ) (refs:∀j,R.family.ref (d j)≤N) :
    WilsonThermometerInversionFaces.face R d o (g) (τ) (v) t x L (g) U =
        L (∏j:V,t j x * R.family.O N per (w j) (o j) U) := by
  let c (j:V) := ((g)^(d j+1))⁻¹
  let z (j:V) := rawWord R d (g) (τ) (v) t j (g) x (o j) U
  change (∏j,c j)*L (∏j,z j)=_
  rw [←smul_eq_mul,←map_smul,Complex.real_smul,Complex.ofReal_prod,←prod_mul_distrib]
  apply congrArg L
  exact prod_congr rfl fun j _=>by simpa only [c,z,Complex.ofReal_inv] using one R d N per o w t x U j (refs j)

end YM.Integration.WilsonThermometerInversionBirth
