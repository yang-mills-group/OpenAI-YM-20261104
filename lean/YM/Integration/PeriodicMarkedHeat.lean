import YM.Integration.RunFormalChain
import YM.Integration.LocalFormalCoefficients
import YM.WilsonCoeffUV.Series.Caloric

/-! The finite marked Wilson table as a heat polynomial, before coupling evaluation.
Each monomial of the actual affine generator has its own multiplicities and its
complex coefficient. The heat operator uses the inverse Hessian of that very
forest at the specified period. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.PeriodicMarkedHeat
open Finset MvPolynomial Lattice Wilson RG Marker Exterior Precision Tree
open Comparison.RG02 Cumulants Next.Rank PhysicalNext.WeightedGaussianMarginal45C.Issue
open scoped BigOperators Classical

variable {I : Type} [Fintype I] [DecidableEq I]

private theorem direction (w : I → ℂ) (p : MvPolynomial I ℂ) :
    Normal.slit w p = ∑ i, w i • pderiv i p := by
  let f (i : I) : Derivation ℂ (MvPolynomial I ℂ) (MvPolynomial I ℂ) := w i • pderiv i
  have evaluate (s : Finset I) (q : MvPolynomial I ℂ) :
      (∑ i ∈ s, f i) q = ∑ i ∈ s, w i • pderiv i q := by
    induction s using Finset.induction with
    | empty => simp
    | insert i s hi ih => rw [sum_insert hi, sum_insert hi, Derivation.add_apply, ih]; rfl
  have same : Normal.slit w = ∑ i, f i := by
    apply derivation_ext
    intro j
    rw [evaluate, Normal.slit_X, sum_eq_single j]
    · rw [pderiv_X_self]; exact (mul_one _).symm.trans (C_mul' ..)
    · intro i _ hij; rw [pderiv_X_of_ne hij.symm, smul_zero]
    · simp
  rw [same, evaluate]

/-- The cover program's finite polynomial heat operator retains all free external
variables before taking its constant coefficient. The identity also holds for
singular real symmetric covariances. -/
theorem heat_real (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (p : MvPolynomial I ℝ) :
    Normal.milk (realRank Q hQ) (MvPolynomial.map Complex.ofRealHom p) =
      MvPolynomial.map Complex.ofRealHom (WilsonCoeffUV.Blue.glaze Q p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [WilsonCoeffUV.Blue.glaze_constant]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [_root_.map_mul, MvPolynomial.map_X, mul_comm _ (X i), Normal.feeds, hp,
      WilsonCoeffUV.Blue.wick_poly Q hQ, _root_.map_add, _root_.map_mul,
      MvPolynomial.map_X, _root_.map_sum, mul_comm (X i), direction]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pderiv_map, ← WilsonCoeffUV.Blue.glaze_deriv]
    change (Q i j : ℂ) • _ = _
    rw [← C_mul', ← C_mul', _root_.map_mul, MvPolynomial.map_C]
    rfl

/-- A complex polynomial in the actual free keys is heated monomial by monomial.
The integral over real free keys acts only on its real monomial and retains the
full complex marked coefficient. -/
def centered (Q : Matrix I I ℝ) (p : MvPolynomial I ℂ) : ℂ :=
  ∑ a ∈ p.support, coeff a p *
    ((constantCoeff (WilsonCoeffUV.Blue.glaze Q (monomial a (1 : ℝ))) : ℝ) : ℂ)

theorem centered_eq (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (p : MvPolynomial I ℂ) :
    Cloud.wick Q hQ 0 p = centered Q p := by
  rw [centered]
  conv_lhs => rw [p.as_sum, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hmono : monomial a (coeff a p) =
      (coeff a p) • MvPolynomial.map Complex.ofRealHom (monomial a (1 : ℝ)) := by
    rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
  rw [hmono, _root_.map_smul, smul_eq_mul]
  change _ * aeval (0 : I → ℂ) (Normal.milk (realRank Q hQ) _) = _
  rw [heat_real Q hQ, aeval_zero, constantCoeff_map]; rfl

omit [DecidableEq I] in
theorem centered_mass (Q : Matrix I I ℝ) (p : MvPolynomial I ℂ) :
    ‖centered Q p‖ ≤ ∑ a ∈ p.support, ‖coeff a p‖ *
      ‖((constantCoeff (WilsonCoeffUV.Blue.glaze Q (monomial a (1 : ℝ))) : ℝ) : ℂ)‖ := by
  simpa only [centered, norm_mul] using norm_sum_le p.support
    (fun a => coeff a p * ((constantCoeff (WilsonCoeffUV.Blue.glaze Q (monomial a (1 : ℝ))) : ℝ) : ℂ))

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
  {P : PathData G} {O : ChartRatio G} {V : Type} [DecidableEq V] [Fintype V]
  {R : Census V}

/-- One polynomial per complete finite marker/coupling mode. The exact marked
germs, action, Haar and chart are expanded in the prescribed affine coordinates. -/
def polynomial (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors R G f) (x : fieldDir G c 1) (r : ℕ) (s : (Order.Board R r).Mode) :
    MvPolynomial (Key F G) ℂ :=
  Cloud.integrand (Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) W.power
    (Bulk.markFn S F W) (Bulk.geometric K F t W) r) s

def table (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors R G f) (x : fieldDir G c 1) (r : ℕ) : Order.Grade R r :=
  Poly.inject fun s => centered (K.covariance F t) (polynomial K F t W x r s)

private theorem prescription {T : Type} [DecidableEq T] {D : Census T}
    (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (b : YM.Multi.Hot D → Normal.poly I) :
    Cloud.prescription Q hQ 0 b =
      YM.Marker.Poly.inject (fun t:D.Mode => centered Q (Cloud.integrand b t)) := by
  apply YM.Marker.Poly.ext
  intro t
  exact centered_eq Q hQ (Cloud.integrand b t)

/-- This identity compares the complete two independently defined finite Gaussian
algorithms. It holds for each forest, field, tag and marked source. -/
theorem actual (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors R G f) (x : fieldDir G c 1) (r : ℕ) :
    Bulk.Fk K F t W x r = table K F t W x r := by
  unfold Bulk.Fk Assembly.prescription table polynomial
  exact prescription (K.covariance F t) (K.symm F t) _

/-- The vacuum denominator stays inside the finite connected logarithm, before
any coupling valuation or physical test estimate. -/
theorem marked (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors R G f) (x : fieldDir G c 1) (r : ℕ) :
    Order.logMarked (Bulk.Fk K F t W x r) = Order.logMarked (table K F t W x r) :=
  congrArg Order.logMarked (actual K F t W x r)

/-- Exact bridge at every finite physical request, including the complete
marker assignment. The covariance and the affine jets come from the same Run. -/
theorem fromRun (U : PhysicalNext.Repeat.Legato.Run G) (d : LocalFormal.Datum U.family R)
    (r k : ℕ) (v : R.Mode) :
    d.markedLogCoefficient (RunFormalChain.fromRun U) r k v =
      (Order.observe R r (Order.logMarked (table (d.kernel (RunFormalChain.fromRun U))
        d.forest d.tag d.colors d.field r)) k).part v := by
  unfold LocalFormal.Datum.markedLogCoefficient LocalFormal.Datum.markedLog LocalFormal.Datum.raw
  rw [actual]

end YM.Integration.PeriodicMarkedHeat
end
