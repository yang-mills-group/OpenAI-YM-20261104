import YM.Integration.WilsonPhysicalPositiveHome

/-! On the actual homogeneous public frame the Born aperture is uniform in the positive mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositiveAperture
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
local notation "E" => named R B h
local notation "goal" i:max j:max => fields R a (fun _:I=>h) (fun k=>E k) i j

open WilsonOriginalPublicRelativeGramOuterPhysical (truePair)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
variable (avoid:Finset E4)

theorem original (simple:G.Simple)(lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (δ:ℝ)(dp:0<δ):
    ∃e:ℝ,0<e ∧ ∀ᶠr in trail,∀t:ℝ,0<t→t<e →
      ‖(fun i j=>truePair R F J Z B h a r (shape avoid (pointsAt a) t) i j)-reading a (nodes a) (id:I→I)‖≤δ:=by
  let Φ:=shape avoid (pointsAt a)
  let free:I→I→Points 2→ℂ:=fun i j=>WickGoal (goal i j)
  have good:pointsAt a∈conf 2:=Extra.FD.couple_ok (WilsonAddressedPublicWideMeasure.distinct a)
  have seats:Tendsto Φ trail (𝓝 (pointsAt a)):=
    WilsonOriginalPublicRelativeGramAddresses.limit avoid (pointsAt a) self_mem_nhdsWithin nhdsWithin_le_nhds
  have warm(i j:I):Tendsto (fun t=>free i j (Φ t)) trail (𝓝 (reading a (nodes a) (id:I→I) i j)):=by
    have smooth:ContinuousOn (WickGoal (goal i j)) (conf 2):=
      ((Bel R.family.book).class_smooth (Bel R.family.book) (Maxwell.Free.hierarchy R.family.book.grid).smooth
        (fun k:Fin 2=>⟨D k,(goal i j) k⟩)).continuousOn
    rw [←WilsonOriginalPublicRelativeGramFreePanel.incidence R B h a i j]
    exact (smooth.continuousAt ((conf_open _).mem_nhds good)).tendsto.comp seats
  have cv:Tendsto (fun t i j=>free i j (Φ t)) trail (𝓝 (reading a (nodes a) (id:I→I))):=
    tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>warm i j
  obtain ⟨t,tp,subset⟩:=Metric.isOpen_iff.mp (conf_open _) (pointsAt a) good
  let K:=Metric.closedBall (pointsAt a) (t/2)
  have legal:K⊆conf 2:=(Metric.closedBall_subset_ball (half_lt_self tp)).trans subset
  have inside:∀ᶠu in trail,Φ u∈K:=seats.eventually (Metric.closedBall_mem_nhds _ (half_pos tp))
  obtain ⟨e,ep,kept⟩:=Metric.mem_nhdsWithin_iff.mp (inside.and (Metric.tendsto_nhds.mp cv (δ/2) (half_pos dp)))
  have native:=eventually_all.mpr fun i:I=>eventually_all.mpr fun j:I=>
    WilsonOriginalPublicRelativeGramOuterPhysical.compact R F J Z B h a simple lead earned i j
      (isCompact_closedBall ..) legal (half_pos dp)
  refine ⟨e,ep,?_⟩
  filter_upwards [native] with r paid u up ue
  have room:=kept (show u∈Metric.ball (0:ℝ) e∩Set.Ioi 0 from
    ⟨by simpa [Metric.mem_ball,dist_zero_right,abs_of_pos up] using ue,up⟩)
  have physical:‖(fun i j=>truePair R F J Z B h a r (Φ u) i j)-(fun i j=>free i j (Φ u))‖≤δ/2:=by
    apply (pi_norm_le_iff_of_nonneg (half_pos dp).le).mpr
    intro i
    exact (pi_norm_le_iff_of_nonneg (half_pos dp).le).mpr (fun j=>paid i j _ room.1)
  apply (norm_sub_le_norm_sub_add_norm_sub _ (fun i j=>free i j (Φ u)) _).trans
  have predicted:=room.2.le
  rw [dist_eq_norm] at predicted
  linarith

end YM.Integration.WilsonPhysicalPositiveAperture
