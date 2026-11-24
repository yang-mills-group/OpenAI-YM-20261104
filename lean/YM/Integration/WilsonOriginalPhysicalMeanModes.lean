import YM.Integration.WilsonOriginalHomogeneousBoxContinuity
import YM.Integration.WilsonOriginalTorusAxisExpense
import YM.Integration.WilsonOriginalSmoothBoxSlice

/-! The actual Wilson mean in the appointed homogeneous frame supplies
the high-frequency estimate on a separated affine box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalMeanModes
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)



open UnitAddTorus AddCircle
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalPhysicalBoxSlices (positions)

theorem axis_member {m : ℕ} (i : Fin (m+1)) (rest : Fin m → UnitAddCircle)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (j : Fin (m+1)) :
    positions i 0 rest t j ∈ Icc (0:ℝ) 1 := by
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simpa [WilsonOriginalPhysicalBoxSlices.positions] using ht
  · have e := (AddCircle.equivIoc (1:ℝ) 0 (rest k)).property
    simpa [WilsonOriginalPhysicalBoxSlices.positions] using And.intro e.1.le e.2

include run in
theorem original {n m : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    {η : ℝ} (gap : 0 < η) {u : ℝ → ℝ} (clock : Coupling G u)
    (embed : (Fin (m+1) → ℝ) →L[ℝ] Points n)
    (direction : ∀ i, ‖embed (Pi.single i (1:ℝ))‖ ≤ 1) :
    ∃ B D : ℝ, 0 < B ∧ 0 ≤ D ∧ ∀ᶠ r in trail, 0 < r →
      ∀ (origin : Points n) (l h : Fin (m+1) → ℝ),
        (∀ i, 0 < l i) → (∀ i, h i < 1) →
        (∀ x : Fin (m+1) → ℝ, (∀ i, x i ∈ Icc (0:ℝ) 1) → ∀ j k : Fin n,
          j ≠ k → η ≤ dist ((origin+embed x) j) ((origin+embed x) k)) →
        ∀ (freq : Fin (m+1) → ℤ) (k : ℕ),
        ‖mFourierCoeff (localize 0 l h (fun x => S.classMoment S d (r • (origin+embed x))
          (fun j => homogeneous F J Z r (d j) (v j)))) freq‖ * (height freq:ℝ)^k ≤
        (u r)⁻¹^2*Real.exp (D*(u r)⁻¹^4)*((B/u r)^(2*k)*(k.factorial:ℝ)^2) := by
  obtain ⟨B,D,bpos,dpos,bill⟩ := WilsonOriginalHomogeneousBoxJets.original run Z d v gap clock embed.toLinearMap direction
  refine ⟨B,D,bpos,dpos,?_⟩
  filter_upwards [bill,WilsonOriginalHomogeneousRealGerm.original run Z d v gap clock,clock.positive]
    with r paid germs positive
  intro hr origin l h left right room freq k
  let field := fun x => S.classMoment S d (r • (origin+embed x)) (fun j => homogeneous F J Z r (d j) (v j))
  have clear (x : Fin (m+1) → ℝ) (hx : ∀ j, x j ∈ Icc (0:ℝ) 1) : origin+embed x ∈ conf n := by
    intro j q same
    by_contra different
    have gap' := room x hx j q different
    change (origin+embed x) j = (origin+embed x) q at same
    rw [same,dist_self] at gap'
    exact gap.not_ge gap'
  have cont := WilsonOriginalHomogeneousBoxContinuity.original (F:=F) (J:=J) Z d v r hr origin embed 0
    (fun x hx => clear x (by simpa using hx))
  let deposited : C(UnitAddTorus (Fin (m+1)),ℂ) := ⟨localize 0 l h field,
    WilsonOriginalCompactTorusChart.original 0 l h field (fun i => (left i).le)
      (fun i => by simpa using (right i).le) cont⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun j => (freq j).natAbs)
  apply WilsonOriginalTorusAxisExpense.original deposited freq i hi.symm k _ (by positivity)
  · intro rest j t ht
    apply WilsonOriginalHomogeneousRealGerm.derivative
    apply WilsonOriginalSmoothBoxSlice.original i 0 l h field rest t (left i) (by simpa using right i) (by simpa using ht)
    have raw := germs (origin+embed (positions i 0 rest t)) (room _ (axis_member i rest ht))
      (embed (Pi.single i (1:ℝ))) (direction i)
    simpa only [field,map_add,map_smul,add_assoc] using raw
  · intro rest t ht
    change ‖iteratedDeriv k (fun z : ℝ => localize 0 l h field (i.insertNth (z:UnitAddCircle) rest)) t‖ ≤ _
    have actual := paid origin i 0 l h rest t (left i) (by simpa using right i)
      (by simpa using ht) (room _ (axis_member i rest ht)) k
    exact actual

end YM.Integration.WilsonOriginalPhysicalMeanModes
