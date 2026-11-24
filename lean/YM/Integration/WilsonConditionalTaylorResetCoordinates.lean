import YM.Integration.WilsonConditionalTaylorReclockRows
import YM.Integration.WilsonMovingPolynomialPull

/-! The two physical coordinate conventions preserve the entire coupling
reset, with the factors for both perturbative order and field degree. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorResetCoordinates
open PowerSeries MvPolynomial FormalBulk08 Orb Reef Jets Lava Shore Wine MSbar.Wave
open WilsonMovingPolynomialPull
open scoped Classical BigOperators
variable {V I : Type} [Fintype V] [Fintype I]

theorem components {f g : MvPolynomial V ℝ} (h : ∀ r,homogeneousComponent r f=homogeneousComponent r g) :
    f=g := by
  let M:=max f.totalDegree g.totalDegree
  rw [←buys M f (le_max_left ..),←buys M g (le_max_right ..)]
  exact Finset.sum_congr rfl (fun r _=>h r)

theorem homogeneous (A B : PowerSeries ℝ) (U : Pap V) (e r : ℕ) :
    homogeneousComponent r (coeff e (canter A B V U))=
      ∑ j∈Finset.range (e+1),Wine.bill A B e j r • homogeneousComponent r (coeff j U):=by
  have h := congrArg (facade r) (congrFun (congrFun (stamp_book A B U) e) r)
  change facade r (marble r _) = facade r (Wine.stamp A B (rancho U) e r) at h
  simpa only [marble_grade,Wine.stamp,map_sum,map_smul,rancho] using h

theorem permuted (A B : PowerSeries ℝ) (s : V → I) (T : Pap V) :
    place s (canter A B V T)=canter A B I (place s T):=by
  apply PowerSeries.ext
  intro e
  apply components
  intro r
  rw [place,PowerSeries.coeff_map,homogeneous]
  change homogeneousComponent r (MvPolynomial.rename s (PowerSeries.coeff e (canter A B V T)))=_
  rw [←rename_homogeneousComponent,homogeneous,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,rename_homogeneousComponent]
  rfl

end YM.Integration.WilsonConditionalTaylorResetCoordinates

