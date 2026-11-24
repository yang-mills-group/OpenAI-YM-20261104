import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNumericalAdjustment
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedAdjustmentColumns
open YangMills YangMills.Wilson YM YM.Integration YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick WilsonLimitConstruction
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale WilsonPositionHomogeneousCoefficients
open PostedBilateralAdjustment
open scoped BigOperators Classical
private theorem bound {G : Gauge} {e : ℕ} {v : WickPol G} (h : v ∈ shellSector G e) :
    ∀ m ∈ v.support, Finsupp.weight scaleW m ≤ e := by
  have f := (sector.mp h).1
  rw [lowerCap,MvPolynomial.mem_restrictSupport_iff] at f
  exact fun _ hm => f hm

/-- A filtered correction whose projection on its own weight vanishes. -/
theorem lowering {g : GaugeGroup} {d e : ℕ} (A : Change g.core d) (zero : Level.diag A.val = 0)
    (v : (maxwellReference g).sector d) (hv : Matching.Homogeneous (maxwellReference g) e v.val) :
    ∀ m ∈ (A.val v).val.support,
      Finsupp.weight (fun i : (maxwellReference g).toCoordinates.Key => i.1 + 2) m < e := by
  let T := A.val
  intro m hm
  change Finsupp.weight scaleW m < e
  by_cases he : e ≤ d
  · have pure : MvPolynomial.IsWeightedHomogeneous scaleW v.val e :=
      fun m h => hv m (MvPolynomial.mem_support_iff.mpr h)
    let i : Fin (d+1) := ⟨e,by omega⟩
    have same : Level.proj i v = v := Subtype.ext pure.weightedHomogeneousComponent_same
    have ve : v.val ∈ shellSector g.core e := by
      rw [← pure.weightedHomogeneousComponent_same]
      exact (en (le_refl e) (part d e v)).property
    have le := bound (A.property.2.1 e he v ve) m hm
    apply lt_of_le_of_ne le
    intro eq
    have row := Level.diagonals v i T
    have diag : Level.diag T = 0 := zero
    rw [diag,same] at row
    have no : (engineering e g.core (T v).val).coeff m = 0 := by
      exact congrArg (fun x : Sec g.core d => x.val.coeff m) row.symm
    have at_weight (p : WickPol g.core) (j : Maxwell.Slot g.core →₀ ℕ) (hj : Finsupp.weight scaleW j = e) :
        (engineering e g.core p).coeff j = p.coeff j := by
      rw [engineering,MvPolynomial.coeff_weightedHomogeneousComponent,if_pos hj]
    exact MvPolynomial.mem_support_iff.mp hm ((at_weight (T v).val m eq).symm.trans no)
  · exact lt_of_le_of_lt (bound (T v).property m hm) (by omega)

theorem original {g : GaugeGroup} (Z : WilsonPrescription g.core) (law : Warrant Z)
    (d e k : ℕ) (v : (maxwellReference g).sector d) (hv : Matching.Homogeneous (maxwellReference g) e v.val) :
    ∀ m ∈ ((PowerSeries.coeff (k+1) (Measure.adjust Z.scheme Z.criterion d)) v).val.support,
      Finsupp.weight (fun i : (maxwellReference g).toCoordinates.Key => i.1 + 2) m < e := by
  have eq := WilsonPositionHomogeneousCoefficients.positive Z law d (Nat.succ_ne_zero k)
  rw [← eq]
  exact lowering (letter Z d (k+1)) (absent Z law d (k+1)) v hv

theorem atZero {g : GaugeGroup} (Z : WilsonPrescription g.core) (law : Warrant Z) (d : ℕ) :
    PowerSeries.coeff 0 (Measure.adjust Z.scheme Z.criterion d) = LinearMap.id :=
  (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (law.scheme d).scale.lead
end IssuedBridge.PostedAdjustmentColumns
