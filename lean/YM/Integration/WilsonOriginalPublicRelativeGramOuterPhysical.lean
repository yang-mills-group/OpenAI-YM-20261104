import YM.Integration.WilsonOriginalPublicRelativeGramOuterSelf
import YM.Integration.WilsonMacroscopicRichTwoDatePivot

/-! The genuine physical homogeneous self-Gram has an own-date coercive
direction on all public coordinates, including its unit and lower fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterPhysical
open Filter Set Function Lattice Wilson RG Source Extraction RG17 Table Spec Climb
open FVA2 FVA2.Register
open Trace.Pilot PhysMS Frame XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonOriginalPublicRelativeGramLeading (fields)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPositionProgramPublicContrast (assay)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonMacroscopicRichTwoDatePivot (active)
open WilsonOriginalBlissMixedGram (grades)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
    {Y:(Bel R.family.book).Hierarchy} (B:Deck G)(h:ℕ)(a:Axis)
local notation "I" => Glyph B h
local notation "D" => grades h h
local notation "B₀" => Bel R.family.book
local notation "E" => named R B h
local notation "dual" => (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) h a
local notation "goal" i:max j:max => fields R a (fun _:I=>h) (fun k=>E k) i j

def truePair (r:ℝ)(y:Points 2)(i j:I):ℂ:=
  S.classMoment S D (r • y) (Fin.cons (α:=fun k=>S.Field (D k))
    (S.adj F.room.kernel.spin h a (homogeneous F J Z r h (E i)))
    (fun _=>homogeneous F J Z r h (E j)))

/-- Uniform on any predeclared separated compact and on its authentic reflected leg. -/
theorem compact (simple:G.Simple)(lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (i j:I){K:Set (Points 2)}(paid:IsCompact K)(sep:K⊆conf 2){ε:ℝ}(ep:0<ε):
    ∀ᶠr in trail,∀y∈K,‖truePair R F J Z B h a r y i j - WickGoal (goal i j) y‖≤ε := by
  let u (r:ℝ) : (k:Fin 2)→(Bel R.family.book).Field (D k) := Fin.cons (α:=fun k=>(Bel R.family.book).Field (D k))
    (dual (active F J Z r h (E i))) (fun _=>active F J Z r h (E j))
  let reflecting : (Bel R.family.book).Field h →ₗ[ℝ] (Bel R.family.book).Field h :=
    { toFun := dual
      map_add' := map_add _
      map_smul' := fun s v=>by
        change dual (s • v)=s • dual v
        simp only [←Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal] }
  have axisMap : Continuous dual := reflecting.continuous_of_finiteDimensional
  have limit (s:Fin 2) : Tendsto (fun r=>u r s) trail (𝓝 ((goal i j) s)) := by
    fin_cases s
    · exact (axisMap.tendsto _).comp (WilsonMacroscopicRichTwoDatePivot.field F J Z lead earned simple h (E i))
    · exact WilsonMacroscopicRichTwoDatePivot.field F J Z lead earned simple h (E j)
  have bought := (WilsonReportingMeasuredAdmission.present F J lead earned).runs F J u (goal i j) limit K paid sep ε ep
  filter_upwards [bought,lead.equivariant h] with r price obeys
  intro y ys
  have price := price y ys
  convert price using 2
  congr 1
  apply congrArg (S.classMoment S D (r • y))
  funext k
  fin_cases k
  · change S.adj F.room.kernel.spin h a (homogeneous F J Z r h (E i)) =
      J r h (dual (active F J Z r h (E i)))
    change _=J r h ((Bel R.family.book).mirror (Maxwell.Free.spin_free R.family.labels) h (Signed.mirror a)
      ((Bel R.family.book).conj (Maxwell.Free.spin_free R.family.labels) h (active F J Z r h (E i))))
    rw [obeys.1,obeys.2]
    simp [Table.adj,active]
  · change _=J r h (active F J Z r h (E j))
    simp [active]

/-- The full uncentered genuine physical Gram is positive at the reference pose. -/
theorem original (simple:G.Simple)(lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d):
    ∃k:ℝ,0<k ∧ ∀ᶠr in trail,∀p:I→ℂ,
      k*‖p‖^2 ≤ ‖assay p p (truePair R F J Z B h a r (pointsAt a))‖ := by
  obtain ⟨k,δ,kp,dp,done⟩:=WilsonPositionProgramPublicWickGram.original a (id:I→I) injective_id
  have distinct := WilsonAddressedPublicWideMeasure.distinct a
  have safe : ({pointsAt a}:Set (Points 2))⊆conf 2 := by
    simpa only [Set.singleton_subset_iff,pointsAt] using Extra.FD.couple_ok (show -(WilsonPositionProgramPublicWickGram.vertex a) ≠ WilsonPositionProgramPublicWickGram.vertex a from distinct)
  have sale (i j:I) := compact R F J Z B h a simple lead earned i j isCompact_singleton safe dp
  have all := Filter.eventually_all.mpr fun i:I=>Filter.eventually_all.mpr fun j:I=>sale i j
  refine ⟨k,kp,?_⟩
  filter_upwards [all] with r fees
  apply done
  apply (pi_norm_le_iff_of_nonneg dp.le).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg dp.le).mpr
  intro j
  simpa only [Pi.sub_apply,←incidence R B h a i j] using fees i j (pointsAt a) (Set.mem_singleton _)

end YM.Integration.WilsonOriginalPublicRelativeGramOuterPhysical
