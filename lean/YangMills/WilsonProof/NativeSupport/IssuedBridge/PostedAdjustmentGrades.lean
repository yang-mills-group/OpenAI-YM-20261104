import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAdjustmentFields
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedAdjustmentGrades
open YangMills YangMills.Wilson YM YM.Integration YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick WilsonLimitConstruction
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale WilsonPositionHomogeneousCoefficients
open PostedBilateralAdjustment
open scoped BigOperators Classical
private theorem bound {G : Gauge} {e : ℕ} {v : WickPol G} (h : v ∈ shellSector G e) :
    ∀ m ∈ v.support, Finsupp.weight scaleW m ≤ e := by
  have f := (sector.mp h).1
  rw [lowerCap,MvPolynomial.mem_restrictSupport_iff] at f
  exact fun _ hm => f hm

theorem original {g : GaugeGroup} (Z : WilsonPrescription g.core) (law : Warrant Z)
    {t : ℝ} (ht : 0 < t) (d e : ℕ) (v : (maxwellReference g).sector d)
    (hv : Matching.Homogeneous (maxwellReference g) e v.val) :
    ∀ m ∈ ((value Z d t v).val - v.val).support,
      Finsupp.weight (fun i : (maxwellReference g).toCoordinates.Key => i.1 + 2) m < e := by
  let T := (limb Z d t).val
  have diff : (value Z d t v).val - v.val = (T v).val := by
    have cancel (a b : WickPol g.core) : a + b - a = b := by abel
    exact cancel v.val (T v).val
  rw [diff]
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
    have le := bound ((limb Z d t).property.2.1 e he v ve) m hm
    apply lt_of_le_of_ne le
    intro eq
    have unit := WilsonPositionHomogeneousRealization.diagonal Z law d ht
    rw [← positive Z d ht,stand,map_add,Level.diagonal_one] at unit
    have zero : Level.diag T = 0 := by
      apply LinearMap.ext
      intro z
      have h := congrArg (fun A : Module.End ℂ (Sec g.core d) => A z) unit
      change z + Level.diag T z = z at h
      exact add_left_cancel (h.trans (add_zero z).symm)
    have row := Level.diagonals v i T
    rw [zero,same] at row
    have no : (engineering e g.core (T v).val).coeff m = 0 := by
      exact congrArg (fun x : Sec g.core d => x.val.coeff m) row.symm
    have at_weight (p : WickPol g.core) (j : Maxwell.Slot g.core →₀ ℕ) (hj : Finsupp.weight scaleW j = e) :
        (engineering e g.core p).coeff j = p.coeff j := by
      rw [engineering,MvPolynomial.coeff_weightedHomogeneousComponent,if_pos hj]
    exact MvPolynomial.mem_support_iff.mp hm ((at_weight (T v).val m eq).symm.trans no)
  · exact lt_of_le_of_lt (bound (T v).property m hm) (by omega)
end IssuedBridge.PostedAdjustmentGrades
