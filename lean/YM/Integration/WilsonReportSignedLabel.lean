import YM.Integration.WilsonReportWindowCombination
import YM.Integration.WilsonOrdinarySignedWindow

/-! The true single cutoff label in the mixed ordinary Gram aperture, its
finite source and monetary bound before all periods, locations and fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportSignedLabel
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryWindowBuyer WilsonOrdinaryFourGram
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep
open Cells Push.GridApprox WilsonOrdinarySignedWindow WilsonReportWindowSource
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable {F : Final R.family f S} {J : ℝ→tower S} {L : Layout F} {g : ℝ→ℝ} {d : ℕ}
variable {A B : Module.End ℂ ((Bel R.family.book).Field d)} {e : ℕ} {r : ℝ}
variable (P : WindowRows F J L g d A B e r)
set_option quotPrecheck false
local notation "k!" => berth R 28 (L.level r)
local notation "b!" => WilsonOrdinaryHomogeneousDetectors.basis F d
local notation "t!" => (Real.exp (1:ℝ))⁻¹


def input (i : Handle F d) : R.family.label d :=
  ∑h : Fin 4,(weight (g r) h:ℂ) • P.left h i

/-- The measured master of the signed label is the literal four prescribed
compensated columns before finite cutoff transport. -/
theorem registered_master (i : Handle F d) :
    master L d r (input P i) =
      ∑h : Fin 4,(weight (g r) h:ℂ) • J (radii r t! h) d (columns d t! A B (b! i) h) := by
  simp only [input,map_sum,map_smul,P.first]

private theorem size (v : Fin 4 → R.family.label d) (c : Fin 4→ℂ) :
    mass R.family d (∑h,c h • v h)≤∑h,‖c h‖*mass R.family d (v h) := by
  unfold mass Labels.Frame.coeffSize
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sum]
  calc
    _ ≤ ∑ j,∑ h,‖c h*(v h j)‖ := sum_le_sum fun j _=>norm_sum_le _ _
    _ = _ := by rw [sum_comm]; simp only [norm_mul]

/-- No new independent denominator or entering-state estimate is needed to
register the physical cancellation: the same mass costs at most four old columns. -/
theorem mass_paid (small : |g r|≤1) (i : Handle F d) :
    mass R.family d (L.shift d r (input P i)) ≤ 4*R.family.path.levels.clock.hatBeta (L.level r)^e := by
  let c (h : Fin 4) : ℂ := weight (g r) h
  have sq : (g r)^2≤1 := by
    calc
      _=|g r|^2 := (sq_abs _).symm
      _≤(1:ℝ)^2 := pow_le_pow_left₀ (abs_nonneg _) small 2
      _=1 := by norm_num
  have hc (h : Fin 4) : ‖c h‖≤1 := by
    fin_cases h
    · norm_num [c,WilsonOrdinarySignedWindow.weight]
    · norm_num [c,WilsonOrdinarySignedWindow.weight]
    · simpa [c,WilsonOrdinarySignedWindow.weight] using small
    · simpa [c,WilsonOrdinarySignedWindow.weight,abs_of_nonneg (sq_nonneg (g r))] using sq
  have shifted : L.shift d r (input P i)=∑h,c h • L.shift d r (P.left h i) := by simp only [input,c,map_sum,map_smul]
  rw [shifted]
  apply (size (fun h=>L.shift d r (P.left h i)) c).trans
  calc
    _ ≤ ∑ _h : Fin 4, R.family.path.levels.clock.hatBeta (L.level r)^e := by
      apply sum_le_sum; intro h _
      have pos : (0:ℝ) ≤ RG12.mass R.family d (L.shift d r (P.left h i)) := by
        unfold RG12.mass Labels.Frame.coeffSize
        exact sum_nonneg fun _ _=>norm_nonneg _
      exact (mul_le_mul_of_nonneg_right (hc h) pos).trans (by simpa only [one_mul] using P.first_cost h i)
    _ = _ := by simp

private theorem transport (N p : ℕ) (i : Handle F d) :
    atRef L d r (N,p) (input P i) =
      ∑h : Fin 4,(weight (g r) h:ℂ) • atRef L d r (N,p) (P.left h i) := by
  unfold atRef input
  simp only [map_sum,map_smul,Finset.smul_sum]
  exact sum_congr rfl fun h _=>smul_comm _ _ _

/-- On the original measured finite history, the whole compensated left
field is a single physically registered polynomial, one entire signed
regular input and one forced input with a common, unchanged address array. -/
theorem original (N p : ℕ) (i : Handle F d) (grade : R.family.ref d≤k!) (cut : k!≤N) :
    let C := R.family
    let w := atRef L d r (N,p) (input P i)
    let v (h : Fin 4) := atRef L d r (N,p) (P.left h i)
    let c (h : Fin 4) : ℂ := weight (g r) h
    let b := (C.path.levels.budget k!).B
    let x := cells R k! p r detectors 0
    let Q := Next.Rank.Spindle.parcel C d k! N p
    (∀ h,(Q w).support=(Q (v h)).support) ∧
    (Q w).x=∑h,c h • (Q (v h)).x ∧
    (Q w).regular=∑h,c h • (Q (v h)).regular ∧
    (Q w).forced=∑h,c h • (Q (v h)).forced ∧
    (∀ U,net P N p i U=bead C d k! N p b w x U ∧
      net P N p i U=opened C (N:=N) w x U+alarm C (N:=N) w x U) ∧
    Interior (window x (omen C d k! b)) (opened C (N:=N) w x) ∧
    Interior (window x (omen C d k! b)) (alarm C (N:=N) w x) := by
  let c (h : Fin 4) : ℂ := weight (g r) h
  let v (h : Fin 4) := atRef L d r (N,p) (P.left h i)
  let b := (R.family.path.levels.budget k!).B
  let x := cells R k! p r detectors 0
  let w := atRef L d r (N,p) (input P i)
  have identity : w=∑h,c h • v h := transport P N p i
  obtain ⟨support,coords,regulars,forces,parts⟩ := WilsonReportWindowCombination.four
    (N:=N) (p:=p) R.family R.makes grade cut c v
  rw [←identity] at coords regulars forces
  dsimp only
  refine ⟨fun h=>(support w).trans (support (v h)).symm,coords,regulars,forces,?_,WilsonReportFittedSupport.original R.family R.makes w grade cut x⟩
  intro U
  have eq : net P N p i U=bead R.family d k! N p b w x U := by rw [identity]; exact (parts x U).2.2.symm
  exact ⟨eq,eq.trans ((WilsonReportWindowSource.actual R.family R.makes grade cut w).2.2.2 x U)⟩

/-- Transport of this particular signed aperture to the actual report scale. -/
theorem financed (services : OPE.Services R.family f S) (small : |g r|≤1) (N p : ℕ) (i : Handle F d)
    {t : ℕ} (grade : R.family.ref d≤L.level r) (past : L.level r≤k!) (cut : k!≤N)
    (zoom : R.family.S.a (L.level r)/R.family.S.a k!≤R.family.path.levels.clock.hatBeta k!^t) :
    Next.Rank.Spindle.paid R.family d k! N p (atRef L d r (N,p) (input P i)) ≤
      R.family.path.levels.clock.hatBeta k!^(t*(d+1))*(4*R.family.path.levels.clock.hatBeta (L.level r)^e) := by
  have H := WilsonReportRegularMoments.transported (N:=N) (p:=p) L services r (input P i) grade past cut zoom
  exact H.trans (mul_le_mul_of_nonneg_left (mass_paid P small i) (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed _).le) _))

end YM.Integration.WilsonReportSignedLabel
end

