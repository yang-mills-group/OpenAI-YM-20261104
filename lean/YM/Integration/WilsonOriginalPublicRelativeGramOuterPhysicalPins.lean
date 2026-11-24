import YM.Integration.WilsonOriginalPublicRelativeGramOuterPhysical
import YM.Integration.WilsonOriginalPublicRelativeGramOuterSelf
import YM.Integration.WilsonMacroscopicRichTwoDatePivot

/-! The genuine physical homogeneous self-Gram has an own-date coercive
direction on all public coordinates, including its unit and lower fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterPhysicalPins
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

open WilsonOriginalPublicRelativeGramOuterPhysical (truePair)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (readings matrix)
variable {g:ℝ→ℝ}(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4)(Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
local notation "ω" => (fun (r:ℝ) (_:Unit)=>ports R avoid (pointsAt a) (Γ.date r) r)
local notation "S₀" => (fun r:ℝ=>shape avoid (pointsAt a) (R.family.S.a (Γ.date r)/r))
local notation "real" => ordered trail (fun _:ℝ=>(ℓ:Filter (ℕ×ℕ)))

theorem shapeLimit (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(i j:I):
    Tendsto (fun r=>truePair R F J Z B h a r (S₀ r) i j) trail
      (𝓝 (reading a (nodes a) (id:I→I) i j)) := by
  have positive:∀ᶠ r in trail,0<r:=self_mem_nhdsWithin
  let δ:=fun r=>R.family.S.a (Γ.date r)/r
  have dp:∀ᶠr in trail,0<δ r:=positive.mono fun r rp=>div_pos (R.family.S.a_pos _) rp
  have fine:Tendsto δ trail (𝓝 0):=squeeze_zero' (dp.mono fun _ x=>x.le) Γ.upper
    (by simpa only [zero_pow (by decide:2≠0)] using (Coupling.conforms simple temperature).pow 2)
  have seats:=WilsonOriginalPublicRelativeGramAddresses.limit avoid (pointsAt a) dp fine
  have good : pointsAt a ∈ conf 2 := Extra.FD.couple_ok (WilsonAddressedPublicWideMeasure.distinct a)
  have smooth : ContinuousOn (WickGoal (goal i j)) (conf 2) :=
    ((Bel R.family.book).class_smooth (Bel R.family.book) (Maxwell.Free.hierarchy R.family.book.grid).smooth
      (fun k:Fin 2=>⟨D k,(goal i j) k⟩)).continuousOn
  have free := (smooth.continuousAt ((conf_open _).mem_nhds good)).tendsto.comp seats
  obtain ⟨t,tp,sub⟩ := Metric.isOpen_iff.mp (conf_open _) (pointsAt a) good
  let K:=Metric.closedBall (pointsAt a) (t/2)
  have legal : K⊆conf 2 := (Metric.closedBall_subset_ball (half_lt_self tp)).trans sub
  have inside:∀ᶠr in trail,S₀ r∈K := seats.eventually (Metric.closedBall_mem_nhds _ (half_pos tp))
  rw [←incidence R B h a i j]
  apply Metric.tendsto_nhds.mpr
  intro e ep
  have bought:=WilsonOriginalPublicRelativeGramOuterPhysical.compact R F J Z B h a simple lead earned i j
    (isCompact_closedBall ..) legal (half_pos ep)
  filter_upwards [inside,bought,Metric.tendsto_nhds.mp free _ (half_pos ep)] with r fit price tail
  calc
    _ ≤ dist _ (WickGoal (goal i j) (S₀ r)) + dist _ _ := dist_triangle .. 
    _ < _ := by
      have first : dist (truePair R F J Z B h a r (S₀ r) i j) (WickGoal (goal i j) (S₀ r)) ≤ e/2 := by
        rw [dist_eq_norm]
        exact price _ fit
      have last : dist (WickGoal (goal i j) (S₀ r)) (WickGoal (goal i j) (pointsAt a)) < e/2 := tail
      linarith only [first,last]

theorem original (simple:G.Simple)(temperature:Coupling G g)(lead:Leading F J)
    (earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (source:ℝ→(ℕ×ℕ)→I→R.family.label h)(name:ℝ→I→R.family.label h)
    (paid:∀ᶠr in trail,∀i,Tendsto (fun b=>source r b i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (name r i)))
    (same:∀ᶠr in trail,∀i,S.project h (name r i)=homogeneous F J Z r h (E i)):
    ∃k:ℝ,0<k ∧ ∀ᶠr in trail,∀ᶠb in (ℓ:Filter (ℕ×ℕ)),∀x:I→ℂ,
        k*‖x‖^2 ≤ ‖assay x x (entered B h a R F ℓ avoid Γ source (r,b))‖ := by
  have limb (i j:I) : Tendsto (fun s=>entered B h a R F ℓ avoid Γ source s i j) real
      (𝓝 (reading a (nodes a) (id:I→I) i j)) := by
    apply WilsonOriginalPublicRelativeGramReflectedLimit.passage (reported:=fun r=>truePair R F J Z B h a r (S₀ r) i j)
    · filter_upwards [paid,same,self_mem_nhdsWithin] with r cash filed rp
      have buys:=WilsonOriginalPublicRelativeGramPins.limit R F a (fun _:I=>h) J (fun k=>active F J Z r h (E k))
        r r (Γ.date r) (ω r) (fun _:Unit=>(1:ℂ)) (fun _=>source r) (fun _=>name r)
        (fun _=>cash) (fun b k=>by simpa [active] using filed k) below
        (fun _ _=>WilsonOriginalPublicRelativeGramAddresses.screened R avoid (pointsAt a) (Γ.date r) rp) false i j
      simpa [entered,WilsonOriginalPublicRelativeGramPins.matrix,WilsonOriginalPublicRelativeGramPins.readings,truePair,WilsonOriginalPublicRelativeGramAddresses.placed R avoid (pointsAt a) (Γ.date r) rp,active] using buys
    · exact shapeLimit R F J Z B h a ℓ avoid Γ simple temperature lead earned i j
  have target:=tendsto_pi_nhds.mpr (fun i:I=>tendsto_pi_nhds.mpr (fun j:I=>limb i j))
  obtain ⟨k,δ,kp,dp,done⟩:=WilsonPositionProgramPublicWickGram.original a (id:I→I) injective_id
  refine ⟨k,kp,?_⟩
  change ∀ᶠp in real,∀x:I→ℂ,k*‖x‖^2 ≤ ‖assay x x (entered B h a R F ℓ avoid Γ source p)‖
  filter_upwards [Metric.tendsto_nhds.mp target δ dp] with p close
  apply done
  simpa only [dist_eq_norm] using close.le

end YM.Integration.WilsonOriginalPublicRelativeGramOuterPhysicalPins
