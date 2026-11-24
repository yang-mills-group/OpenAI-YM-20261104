import YM.Integration.WilsonPhysicalHistoryMixedDegree

/-! Exact fixed-order polynomial capacity of the fully prescribed original
signed cofactor, uniformly on a growing physical conditional history. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryMixedCofactorCapacity
open Function Filter Finset Lattice RG Wilson Precision Tree Exterior Push.Uniform
open Source Labels Next.Foundations Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open FormalBulk08 Flat Reef Orb Next.Free Jets MSbar.Rolling MSbar.Cacao PowerSeries
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier WilsonRunFormalMarkedStep
open Source.Drops RG16.Literal RG16.Guarding MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Mosaic
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature WilsonConditionalTaylorLabels
open WilsonMovingPolynomialPull WilsonMovingGaussianCoordinates WilsonPhysicalHistoryMixedChain
open WilsonPhysicalHistoryMixedCofactor WilsonOffsetPhysicalPair
open scoped Classical BigOperators
variable {G : Gauge} {a b : ℕ}

/-- Finite linear combinations of the actual UV stencil inlets retain the
original order-e degree bound, including the complex label coefficients. -/
theorem born (R : Run G) (N per : ℕ) (v : R.family.label a) (w : R.family.label b)
    (x y : Site (R.family.side N per)) (part : Bool) (e : ℕ) :
    (PowerSeries.coeff e (terminal R N per v w x y part)).totalDegree ≤ e := by
  rw [terminal,place,PowerSeries.coeff_map]
  apply (MvPolynomial.totalDegree_rename_le ..).trans
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  let Z : Bool → Nesting G (R.family.side N per) := stencilInlet (lamps (two i j)) (seats i j x y)
  let c := atom R N per v i*atom R N per w j
  have out (part : Bool) : (PowerSeries.coeff e (Z part)).totalDegree ≤ e :=
    inlet_degree (lamps (two i j)) (seats i j x y) part e
  cases part
  · change (PowerSeries.coeff e (c.re • Z false-c.im • Z true)).totalDegree ≤ e
    rw [map_sub,PowerSeries.coeff_smul,PowerSeries.coeff_smul]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le ((MvPolynomial.totalDegree_smul_le ..).trans (out false))
      ((MvPolynomial.totalDegree_smul_le ..).trans (out true)))
  · change (PowerSeries.coeff e (c.im • Z false+c.re • Z true)).totalDegree ≤ e
    rw [map_add,PowerSeries.coeff_smul,PowerSeries.coeff_smul]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le ((MvPolynomial.totalDegree_smul_le ..).trans (out false))
      ((MvPolynomial.totalDegree_smul_le ..).trans (out true)))

private theorem young {I : Type} [Fintype I] (Z : Pap I)
    (h : ∀ e, (PowerSeries.coeff e Z).totalDegree ≤ e) : Young (rancho Z) 0 := by
  intro e r live
  change r ≤ 0+e
  rw [zero_add]
  by_contra hle
  apply live
  change marble r (PowerSeries.coeff e Z)=0
  rw [marble_eq_zero_iff]
  exact MvPolynomial.homogeneousComponent_eq_zero r _ (lt_of_le_of_lt (h e) (lt_of_not_ge hle))

private theorem height {I : Type} [Fintype I] (Z : Pap I) {l : ℕ} (h : Young (rancho Z) l) (e : ℕ) :
    (PowerSeries.coeff e Z).totalDegree ≤ l+e := by
  let P := PowerSeries.coeff e Z
  have finish := cemento P (P.totalDegree+1) (Nat.lt_succ_self _)
  change P.totalDegree ≤ _
  rw [← finish]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r _
  by_cases hr : r ≤ l+e
  · exact (MvPolynomial.homogeneousComponent_isHomogeneous r P).totalDegree_le.trans hr
  · have van : rancho Z e r=0 := by by_contra q; exact hr (h e r q)
    have zero : MvPolynomial.homogeneousComponent r P=0 := (marble_eq_zero_iff r P).mp van
    rw [zero,MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

/-- Uniform true chart rank and zero-field head from the actual independent
mixed history, at every date and period of the very same funded run. The
capacity p is fixed before choosing the cutoff or the growing stopping depth. -/
theorem preset (R : Run G) (simple : G.Simple) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
    (color : hue G) (p : ℕ) {N per j : ℕ} (hj : j ≤ N) (tag : Tags R N per)
    (v : R.family.label a) (w : R.family.label b) (x y : Site (R.family.side N per)) (part : Bool) :
    let T := recorded R L color N per tag (terminal R N per v w x y) j part
    (∃ c : ℝ, PowerSeries.coeff 0 T=MvPolynomial.C c) ∧
      ∀ e, e ≤ p → (PowerSeries.coeff e T).totalDegree ≤ p := by
  let Z := terminal R N per v w x y part
  let T := recorded R L color N per tag (terminal R N per v w x y) j part
  have hand := WilsonPhysicalHistoryMixedDegree.stable R L color simple hj (le_refl N) tag Z
    (young Z (born R N per v w x y part))
  have rank (e : ℕ) : (PowerSeries.coeff e T).totalDegree ≤ e := by
    change (PowerSeries.coeff e (recorded R L color N per tag (terminal R N per v w x y) j part)).totalDegree ≤ _
    rw [recorded,dif_pos hj,place,PowerSeries.coeff_map]
    exact (MvPolynomial.totalDegree_rename_le ..).trans (by simpa only [zero_add] using height _ hand e)
  exact ⟨⟨(PowerSeries.coeff 0 T).coeff 0,MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (rank 0))⟩,
    fun e he=>(rank e).trans he⟩

end YM.Integration.WilsonPhysicalHistoryMixedCofactorCapacity

