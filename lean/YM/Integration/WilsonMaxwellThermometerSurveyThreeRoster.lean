import YM.Integration.WilsonMaxwellThermometerSurveyThreeDraw
import YM.Integration.WilsonThermometerPositionTunedPublicCharge

/-! Use a common finite roster of placed W survey words, with separate
horizons for every Wick coordinate and a vacant slot for a deleted face. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonMaxwellThermometerSurveyThreeRoster
open Function Finset Lattice Wilson XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open XSpace.Structure1 PhysicalNext.Repeat.Legato
open WilsonThermometerPositionTunedPublicCharge (Picked axisFee row charge)
open WilsonOriginalThermometerPalette (levels)
open WilsonPositionProgramInversionMaterial (Axes axis)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)
abbrev Pin := Fin 3 → Option (WilsonThermometerPositionTunedPublicCharge.Axis R 6)

def rowAt (t:Sample 3)(j:Fin 3)(u:Option (WilsonThermometerPositionTunedPublicCharge.Axis R 6)):
    Bare.Series (W.tree t.F.p) G := u.elim 1 (row R W 6 t j)

def read (t:Sample 3)(u:Pin R):PowerSeries ℂ:=
  Bare.normalized (W.tree t.F.p) G (∏j:Fin 3,rowAt R W t j (u j))

def printedPin (S:Finset (Fin 3))(a:Picked R 6 S):Pin R:=
  fun j=>if hj:j∈S then some (a ⟨j,hj⟩) else none

private theorem printed (t:Sample 3)(S:Finset (Fin 3))(a:Picked R 6 S):
    read R W t (printedPin R S a)=Bare.normalized (W.tree t.F.p) G (∏j:S,row R W 6 t j.val (a j)):=by
  unfold read
  apply congrArg ((Bare.normalized (W.tree t.F.p) G) ·)
  calc
    _ = ∏j∈S,rowAt R W t j (printedPin R S a j):=(Finset.prod_subset (Finset.subset_univ _) (by
      intro j _ hj
      simp [printedPin,rowAt,hj])).symm
    _ = _:=by
      rw [← Finset.prod_coe_sort S]
      exact Finset.prod_congr rfl (fun j _=>by simp [printedPin,rowAt])

def paid (t:Sample 3)(p:Tags G 6 3)(S:Finset (Fin 3)):Pin R →₀ PowerSeries ℂ:=
  ∑a:Picked R 6 S,Finsupp.single (printedPin R S a) (PowerSeries.C (charge R W 6 t p S a))

def hear (t:Sample 3):(Pin R →₀ PowerSeries ℂ)→ₗ[PowerSeries ℂ] PowerSeries ℂ:=
  Finsupp.linearCombination (PowerSeries ℂ) (read R W t)

theorem deposited (t:Sample 3)(p:Tags G 6 3)(S:Finset (Fin 3)):
    hear R W t (paid R W t p S)=numberA W 6 t p S:=by
  rw [WilsonThermometerPositionTunedObserved.ordinary R W t 6 p S,paid,map_sum]
  rw [← Finset.prod_coe_sort S]
  simp_rw [WilsonThermometerPositionTunedPublicCharge.enrolled R W 6 t p,Fintype.prod_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hear,Finsupp.linearCombination_single,printed R W t]
  rw [smul_eq_mul]
  change _ = Bare.normalized (W.tree t.F.p) G (∏ j:S,axisFee R W 6 t p j.val (a j) • row R W 6 t j.val (a j))
  rw [show (∏ j:S,axisFee R W 6 t p j.val (a j) • row R W 6 t j.val (a j))=
     (charge R W 6 t p S a) • ∏ j:S,row R W 6 t j.val (a j) by
       simp only [charge,Algebra.smul_def,Finset.prod_mul_distrib,map_prod],map_smul]
  rw [PowerSeries.smul_eq_C_mul]

private theorem accommodated (i:Fin 3):levels i<7:=by fin_cases i <;> decide

def commissioned (a:Axes R levels):Pin R:=
  fun j=>some ⟨⟨levels j,accommodated j⟩,axis R levels a j⟩

def wallet (ζ:Axes R levels→PowerSeries ℂ):Pin R →₀ PowerSeries ℂ:=
  ∑ a:Axes R levels,Finsupp.single (commissioned R a) (ζ a)

/-- The meromorphic inverse may have several angular/test entries on the
same true survey basis word. Their signed prices add on that very word. -/
theorem measured (t:Sample 3)(ζ:Axes R levels→PowerSeries ℂ):
    hear R W t (wallet R ζ)=WilsonMaxwellThermometerSurveyThreeInversion.surveyed R W
      t.F.p t.layout ζ:=by
  rw [wallet,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hear,Finsupp.linearCombination_single,smul_eq_mul]
  rfl

end YM.Integration.WilsonMaxwellThermometerSurveyThreeRoster
end
