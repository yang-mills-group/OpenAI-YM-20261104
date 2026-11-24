import YM.Integration.WilsonOriginalTwoFlatRoseNominated

/-! Recenter every occupied subset of the original three named cutoff fields together.
The held scalar uses the original signed test with its common translation integrated once. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseCentered
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato Labels Extra.Histories RG16.Literal
open OPE OPE.Orbits XSpace XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonNeutralOffsetCutoff (named)
open WilsonThermometerAlignedCells (offsets atOrigin placedAt)
open WilsonOriginalTwoFlatRoseNominated (face)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(A:WilsonPositionThermometerCapStation.Group R.family 6)(N per:ℕ)
local notation "T" => Site (R.family.side N per)
local notation "E" => Finset (Fin 3)
local notation "d" => fun i:Fin 3=>(WilsonPositionThermometerGradedSource.grade i).val

def ordinary (o:Fin 3→T)(s:E):ℂ:=
  R.family.omega N per fun U=>∏i∈s,R.family.O N per (named R A N per i) (o i) U

/-- The physical product on a proper face uses only the actually occupied labels. -/
theorem translated (ready:∀i,R.family.ref (d i)≤N)(o:Fin 3→T)(t:T)(s:E):
    ordinary R A N per (fun i=>o i+t) s=ordinary R A N per o s:=by
  let e:Fin (Fintype.card (↥s))≃s:=(Fintype.equivFin s).symm
  let labels(j):R.family.book.Token:=⟨d (e j).val,named R A N per (e j).val⟩
  have eqn(pos:Fin 3→T):ordinary R A N per pos s=
      R.family.numeric N per labels (fun j=>pos (e j).val):=by
    unfold ordinary
    change R.family.omega N per _=R.family.omega N per _
    congr 1; funext U
    let f(i:Fin 3):ℂ:=R.family.O N per (named R A N per i) (pos i) U
    change ∏i∈s,f i=∏j,f (e j).val
    rw [←Finset.prod_coe_sort s f]
    apply Fintype.prod_equiv e.symm
    intro i; rw [e.apply_symm_apply]
  rw [eqn,eqn]
  apply R.family.anchored R.makes labels (fun i=>ready (e i).val) t (fun i=>o (e i).val)

/-- Test any function of the whole ordinary table at the same placement. -/
theorem tested (r:ℝ)(ready:∀i,R.family.ref (d i)≤N)(φ:Test 3)(read:T×T→(E→ℂ)→ℂ):
    let χ:=WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per)
    φ.applyTo (fun x=>read (offsets (χ x)) (ordinary R A N per (χ x)))=
      ∑y:T×T,WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y*
        read y (fun s=>R.family.omega N per (face R A y s)):=by
  intro χ
  have centered (o:Fin 3→T):ordinary R A N per o=
      fun s=>R.family.omega N per (face R A (offsets o) s):=by
    have pos:(fun i=>atOrigin (offsets o) i+o 0)=o:=by
      funext i; fin_cases i <;> simp [offsets,atOrigin]
    funext s
    have chosen:=translated R A N per ready (atOrigin (offsets o)) (o 0) s
    rw [pos] at chosen
    exact chosen
  simp_rw [centered]
  exact WilsonThermometerAlignedCells.tested A r (N,per) ready φ
    (fun y _=>read y fun s=>R.family.omega N per (face R A y s))

/-- The centered cofactor heard by the two-stop estimate is precisely the physical
signed Rose at the original rounded microscopic positions, including every proper face. -/
theorem connected (r:ℝ)(ready:∀i,R.family.ref (d i)≤N)(φ:Test 3)(Q:T×T→E→ℂ):
    let χ:=WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per)
    φ.applyTo (fun x=>WilsonPositionThermometerConnected.value (ordinary R A N per (χ x))-
      WilsonPositionThermometerConnected.value (Q (offsets (χ x))))=
      ∑y:T×T,WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y*
        (WilsonMaxwellThermometerNominatedCofactor.reading R A N per y
          (WilsonMaxwellThermometerNominatedCofactor.native R A N per y 0)-
          WilsonPositionThermometerConnected.value (Q y)):=by
  simp_rw [WilsonMaxwellThermometerNominatedCofactor.original]
  exact tested R A N per r ready φ (fun y X=>WilsonPositionThermometerConnected.value X-
    WilsonPositionThermometerConnected.value (Q y))

end YM.Integration.WilsonOriginalTwoFlatRoseCentered
end
