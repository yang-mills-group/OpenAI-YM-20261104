import YM.Integration.WilsonOriginalPublicRelativeGramOuterPhysical
import YM.Integration.WilsonOriginalPublicNodalQuadraticMirror

/-! Reflected compact self pair for an entire original homogeneous source. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalQuadraticSelf
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
    {Y:(Bel R.family.book).Hierarchy} (h:ℕ)(a:Axis)(x:RG17.Free R.family h)
local notation "D" => grades h h
local notation "dual" => (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) h a
local notation "fixed" => fields R a (fun _:Unit=>h) (fun _=>x) () ()
def self (r:ℝ)(y:Points 2):ℂ:=
  S.classMoment S D (r • y) (Fin.cons (α:=fun k=>S.Field (D k))
    (S.adj F.room.kernel.spin h a (homogeneous F J Z r h x))
    (fun _=>homogeneous F J Z r h x))

/-- Uniform on any predeclared separated compact and on its authentic reflected leg. -/
theorem compact (simple:G.Simple)(lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    {K:Set (Points 2)}(paid:IsCompact K)(sep:K⊆conf 2){ε:ℝ}(ep:0<ε):
    ∀ᶠr in trail,∀y∈K,‖self R F J Z h a x r y - WickGoal fixed y‖≤ε := by
  let u (r:ℝ) : (k:Fin 2)→(Bel R.family.book).Field (D k) := Fin.cons (α:=fun k=>(Bel R.family.book).Field (D k))
    (dual (active F J Z r h x)) (fun _=>active F J Z r h x)
  let reflecting : (Bel R.family.book).Field h →ₗ[ℝ] (Bel R.family.book).Field h :=
    { toFun := dual
      map_add' := map_add _
      map_smul' := fun s v=>by
        change dual (s • v)=s • dual v
        simp only [←Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal] }
  have axisMap : Continuous dual := reflecting.continuous_of_finiteDimensional
  have limit (s:Fin 2) : Tendsto (fun r=>u r s) trail (𝓝 (fixed s)) := by
    fin_cases s
    · exact (axisMap.tendsto _).comp (WilsonMacroscopicRichTwoDatePivot.field F J Z lead earned simple h x)
    · exact WilsonMacroscopicRichTwoDatePivot.field F J Z lead earned simple h x
  have bought := (WilsonReportingMeasuredAdmission.present F J lead earned).runs F J u fixed limit K paid sep ε ep
  filter_upwards [bought,lead.equivariant h] with r price obeys
  intro y ys
  have price := price y ys
  convert price using 2
  congr 1
  apply congrArg (S.classMoment S D (r • y))
  funext k
  fin_cases k
  · change S.adj F.room.kernel.spin h a (homogeneous F J Z r h x) =
      J r h (dual (active F J Z r h x))
    change _=J r h ((Bel R.family.book).mirror (Maxwell.Free.spin_free R.family.labels) h (Signed.mirror a)
      ((Bel R.family.book).conj (Maxwell.Free.spin_free R.family.labels) h (active F J Z r h x)))
    rw [obeys.1,obeys.2]
    simp [Table.adj,active]
  · change _=J r h (active F J Z r h x)
    simp [active]

theorem bounded (simple:G.Simple)(lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    {K:Set (Points 2)}(paid:IsCompact K)(sep:K⊆conf 2):
    ∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀y∈K,‖self R F J Z h a x r y‖≤A:=by
  have smooth:ContinuousOn (WickGoal fixed) (conf 2):=
    ((Bel R.family.book).class_smooth (Bel R.family.book) (Maxwell.table_smooth R.family.labels)
      (fun i=>⟨D i,fixed i⟩)).continuousOn
  obtain ⟨A,cap⟩:=(paid.image_of_continuousOn (smooth.mono sep)).isBounded.exists_norm_le
  refine ⟨1+max 0 A,by positivity,?_⟩
  filter_upwards [compact R F J Z h a x simple lead earned paid sep (show (0:ℝ)<1 from zero_lt_one)] with r bound
  intro y hy
  exact (norm_le_norm_sub_add _ _).trans (add_le_add (bound y hy) ((cap _ ⟨y,hy,rfl⟩).trans (le_max_right _ _)))

end YM.Integration.WilsonOriginalPublicNodalQuadraticSelf
