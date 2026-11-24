import YM.Integration.WilsonRootedGermSparseCorrelation

/-! Finite positive one-mark income holds all the way to the genuine bare endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermDose
open Function MeasureTheory Lattice Wilson RG Source MergeProof PhysicalNext.Repeat.Legato OPE.Therm Push.Local
open SectorNext.Vacuum WilsonMatrixOriginalGermForeground WilsonMatrixOriginalGermOccupancy
open WilsonInheritedRegisteredField Trace.Physical.GermGraph Next.Rank.Price
open private weights from YM.Integration.WilsonMatrixOriginalGermOccupancy
open private marked from YM.Integration.WilsonMatrixOriginalGermGram
open private tested from YM.Integration.WilsonMatrixOriginalGermHeldTest
open scoped BigOperators Classical Topology
variable {G : Gauge} (R : Run G) {i N p : ℕ}

/-- The bound at the bare endpoint may depend on the finite regulator. -/
theorem bounded (live : i≤N) (o : Site (R.family.side i p)) : Envelope (rent R i N p o) := by
  rcases live.lt_or_eq with earlier | done
  · exact WilsonMatrixOriginalGermOccupancy.bounded R earlier o
  subst N
  let W := R.family.path.rep i p i
  let β := R.family.path.β i p i
  have law := (R.makes.wilson.represents i p i le_rfl).good
  have cost : Envelope (fun U : Config G (R.family.side i p) => (bare β U)⁻¹) :=
    Push.SectorMeasure.Env.compact ((bare_cont β).inv₀ (fun U=>(bare_pos β U).ne'))
  have num : Envelope (fun U=>WilsonMatrixOriginalGermForeground.weight R i i p o U * Real.exp (W.exponent U)) :=
    (weights R).mul (W.exponentEnv law).exp
  have eqn : rent R i i p o = fun U=>(WilsonMatrixOriginalGermForeground.weight R i i p o U * Real.exp (W.exponent U)) * (bare β U)⁻¹ := by
    funext U
    have endpoint : W.eval U=bare β U := congrFun (R.makes.wilson.starts i p).2 U
    rw [←endpoint,WilsonMatrixOriginalGermOccupancy.factor R le_rfl o U]
    unfold rent
    field_simp [(solvent R (N:=i) le_rfl o U).ne',(Real.exp_pos (W.exponent U)).ne']
    rfl
  rw [eqn]
  exact num.mul cost

/-- The Haar payment directly controls the entire original old insertion at every visible date. -/
theorem held (age : R.family.ref 4 ≤ i) (live : i≤N) (w : R.family.label 4) (o : Site (R.family.side i p))
    {B : ℝ} (cap : Next.UVStress.quota R.family 4 i N p w≤R.family.S.a i^4*B)
    (D : Config G (R.family.side i p) → ℂ) (hd : Envelope D) :
    (∫ U,‖forced R.makes live w o U*D U‖ ∂scene R.family.path N p i) ≤ WilsonMatrixOriginalGermHeldTest.fare R i N p o D*(safety R.family i*stock R.family i*B) := by
  let μ : Measure (Config G (R.family.side i p)) := scene R.family.path N p i
  letI : IsProbabilityMeasure μ := OPE.Therm.probability R.makes.wilson live
  have sale := tested μ (marked R age live w o) hd (bounded R live o) (on_run R age live w B cap o)
  exact sale.trans_eq (congrArg (fun v=>v*(safety R.family i*stock R.family i*B)) (WilsonMatrixOriginalGermHeldTest.factor R live o D))

end YM.Integration.WilsonRootedGermDose
