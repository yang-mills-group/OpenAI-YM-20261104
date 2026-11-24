import YM.Integration.WilsonThermometerMarchTerminalWatch
import YM.Integration.WilsonThermometerCompactChambers

/-! At every occupied relative-test cell the nominated fields may be
replaced by their true projected fields on the original Wilson integral. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerMarchSupported
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open Labels Source Bid Cells Push FullVolume MergeProof Next.Extract Extra.Histories XSpace.Rose MeasureTheory
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap WilsonSeparatedOriginalThermometerCells
open PhysicalNext.Repeat Legato Bandage
open scoped Topology Classical BigOperators
variable {G : Gauge}
def read (C : Family G) (z:ℕ×ℕ) (x:∀ i:Fin 3,C.label (grade i)) (o:Fin 3→Site (C.side z.1 z.2)) : ℂ :=
  moment (C.beta z.1 z.2) (fun U=>∏ i,C.O z.1 z.2 (x i) (o i) U)

theorem translate (C : Family G) (z:ℕ×ℕ) (x:∀ i:Fin 3,C.label (grade i)) (o:Fin 3→Site (C.side z.1 z.2))
    (u:Site (C.side z.1 z.2)) : read C z x (fun i=>o i+u) = read C z x o := by
  let X : Config G (C.side z.1 z.2)→ℂ := fun U=>∏ i,C.O z.1 z.2 (x i) (o i) U
  have cont : Continuous X := continuous_finsetProd _ (fun i _=>C.continuousO ..)
  have shift : (fun U=>∏ i,C.O z.1 z.2 (x i) (o i+u) U) = X ∘ pull 1 u := by
    funext U
    simp only [X,Function.comp_apply,pull_one,C.translation]
  unfold read
  rw [shift,moment_pull _ _ _ _ (cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]

theorem period (f : Extraction.Order) : Tendsto Prod.snd f.fuse atTop :=
  tendsto_atTop.mpr fun n=> (f.fused _).2 ((f.per.cofinal.eventually_ge_atTop n).mono fun _ hp=>
    Eventually.of_forall fun _=>hp)

variable {R : Run G} {f : Extraction.Order} {T : Table R.family.book}
variable (F : Final R.family f T) (J : ℝ → tower T) (V : Store G)
    {H : (Bel R.family.book).Hierarchy} {l : Ultrafilter (ℕ × ℕ)} (A : ℝ → Group R.family 6)
open WilsonThermometerMarchProduct (field)
theorem supported (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (E : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d) (b : Presentation R.family)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (E d) (W d))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a))
    (φ : Test 3) (legal : tsupport φ⊆conf 3) :
    ∀ᶠ r in trail, let Z:=adjusted F J V A r
      ∃ M : Badge→ℝ, (∀ s,0≤M s) ∧ ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ s (o : Fin 3→Site (R.family.side z.1 z.2)),
        (∃ x∈tsupport φ,positions (R:=R) r z x=o) →
        ‖read R.family z (fun i=>b.step (grade i) z (field Z z.1 z.2 s i)) o -
            read R.family z (field Z z.1 z.2 s) o‖ ≤
          7*(Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*(M s)^3) := by
  obtain ⟨radius,ready⟩:= WilsonThermometerMarchTerminalWatch.original F J V A simple paid lead
    E W P b portfolio house
  obtain ⟨p₀,scope⟩:=WilsonThermometerCompactChambers.intersects R φ legal E radius (fun i=>(grade i).val)
  filter_upwards [ready,show ∀ᶠ r : ℝ in trail, 0<r from self_mem_nhdsWithin,
    show ∀ᶠ r:ℝ in trail,r<1 from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds zero_lt_one)] with r programs rp limit
  let Z:=adjusted F J V A r
  obtain ⟨m,fr⟩:=(scope r rp limit.le).exists
  obtain ⟨k,geom,registered⟩:=(fr.and programs).exists
  obtain ⟨early,fit⟩:=geom
  obtain ⟨M,positive,works⟩:=registered
  refine ⟨M,positive,?_⟩
  filter_upwards [works,(WilsonThermometerMarchTerminalWatch.upper f).eventually fit,
    (period f).eventually_ge_atTop p₀] with z authentic valid hp s o live
  obtain ⟨h,offer⟩:=authentic
  obtain ⟨u,v,hv,avoid,inside⟩:=valid.choose_spec z.2 hp o live
  let S:=center R.family.S z.2 (early.trans h) 0
  let w:Empty→S.Cell:=Empty.elim
  let exterior:Empty → Config G (R.family.side z.1 z.2)→ℂ:=Empty.elim
  have one : WilsonThermometerReflectedWatch.exterior S w exterior = (fun _=>1) := by
    funext; simp [WilsonThermometerReflectedWatch.exterior]
  have different : Function.Injective (Sum.elim v w) := by
    rintro (a|a) (c|c) h₁
    · exact congrArg Sum.inl (hv h₁)
    all_goals first | exact Empty.elim a | exact Empty.elim c
  have hearing := offer s m early v _ avoid inside Empty w exterior different (fun i=>Empty.elim i)
  rw [one] at hearing
  have got := hearing (fun _ _ _ _=>rfl) (Mark.cont_envelope continuous_const)
  rw [←translate R.family z (fun i=>b.step (grade i) z (field Z z.1 z.2 s i)) o u,
    ←translate R.family z (field Z z.1 z.2 s) o u]
  simpa [read] using! got

theorem original (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A J) (lead : Leading F J)
    (E : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d) (b : Presentation R.family)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (E d) (W d))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a))
    (φ : Test 3) (legal : tsupport φ⊆conf 3) :
    ∀ᶠ r in trail, let Z:=adjusted F J V A r
      ∃ M : Badge→ℝ, (∀ s,0≤M s) ∧ ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ s (o : Fin 3→Site (R.family.side z.1 z.2)),
        WilsonSeparatedOriginalThermometerCells.weight φ (positions (R:=R) r z) o≠0 →
        ‖read R.family z (fun i=>b.step (grade i) z (field Z z.1 z.2 s i)) o -
            read R.family z (field Z z.1 z.2 s) o‖ ≤
          7*(Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*(M s)^3) := by
  filter_upwards [supported F J V A simple paid lead E W P b portfolio house φ legal] with r ready
  obtain ⟨M,pos,all⟩:=ready
  refine ⟨M,pos,?_⟩
  filter_upwards [all] with z estimated s o live
  exact estimated s o (WilsonOriginalThermometerFineCells.occupied φ _ o live)

end YM.Integration.WilsonThermometerMarchSupported
