import YM.Integration.WilsonOrdinaryAllOrderPivot
import YM.Integration.WilsonFactoryGlyphEngineering
import YM.PhysMS.Frame.Repair
import YM.PhysMS.Frame.Tensor

/-! Repair the genuine independently calibrated MS field frames by the
original manuscript's engineering retraction.  The retraction kills the
highest-grade true glyph, so its *entire* purchased signed MS expansion is
unchanged.  All grade inclusions hold on the original physical continuum. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryPositionGrades
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set Finset PhysMS MeasureTheory Next.UVStress Maxwell
open RG12.Roof Extra.WeakScaling
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (B : Deck G) {O : Booked B} (M : MS_Data G O)
  (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S)
open WilsonMacroscopicRichMeasuredGram WilsonMacroscopicRichRegister

variable (g : ℕ→Test 2) (μ : ℕ→ℝ) (γ : ℝ→ℝ)
def fitted (r : ℝ) : PhysMS.tower S := fun d=>if d=0 then J r d else WilsonOrdinaryAllOrderPivot.field B M F J d (g d) (μ d) (γ:=γ) r
def positioned (r : ℝ) : PhysMS.tower S := PhysMS.Frame.compatible F (fitted B M F J g μ γ r)

theorem uncompromised (A : PhysMS.tower S) (d : ℕ) (v : (Bel C.book).Field d) (top : v∈Peak C.labels d) :
    PhysMS.Frame.compatible F A d v=A d v := by
  unfold PhysMS.Frame.compatible
  split
  · change adjusted F.sector.derivatives (Free.scheme C.labels) (PhysMS.Frame.peelDown C) A d v=A d v
    cases d with
    | zero=>rfl
    | succ e=>
      rw [adjusted_succ,PhysMS.Frame.section_same e v top]
      simp only [map_zero,sub_zero,zero_add]
  · rfl


private theorem fitted_relative (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : ∀ d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Trace.Pilot.Coupling G γ)
    (d : ℕ) (v : (Bel C.book).Field d) :
    Tendsto (fun r=>(J r d).symm (fitted B M F J g μ γ r d v)) Trace.Pilot.trail (𝓝 v) := by
  by_cases vacuum : d=0
  · simpa only [fitted,if_pos vacuum,LinearEquiv.symm_apply_apply] using (tendsto_const_nhds (f:=Trace.Pilot.trail) (x:=v))
  · simpa only [fitted,if_neg vacuum] using (WilsonOrdinaryAllOrderPivot.original B M F J d (g d) (μ d) hG leading (live d) hγ).1 v

theorem neighboring (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : ∀ d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Trace.Pilot.Coupling G γ) :
    PhysMS.Frame.Adjacent F (fitted B M F J g μ γ) Trace.Pilot.trail := by
  apply PhysMS.Frame.neighboring (X:=J) F
  · intro d v
    apply (tendsto_const_nhds (x:=(Free.scheme C.labels).rise (Nat.le_succ d) v)).congr'
    filter_upwards [leading.raised (Nat.le_succ d)] with r he
    rw [←he v,LinearEquiv.symm_apply_apply]
  · intro d v
    exact fitted_relative B M F J g μ γ hG leading live hγ d v

theorem included (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : ∀ d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Trace.Pilot.Coupling G γ)
    {d e : ℕ} (l : d≤e) : ∀ᶠ r in Trace.Pilot.trail,∀ v,
    positioned B M F J g μ γ r e ((Free.scheme C.labels).rise l v) = F.sector.derivatives.rise l (positioned B M F J g μ γ r d v) :=
  PhysMS.Frame.accounted F d e l (neighboring B M F J g μ γ hG leading live hγ)

theorem relative (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : ∀ d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Trace.Pilot.Coupling G γ)
    (d : ℕ) (v : (Bel C.book).Field d) :
    Tendsto (fun r=>(J r d).symm (positioned B M F J g μ γ r d v)) Trace.Pilot.trail (𝓝 v) := by
  let A := fitted B M F J g μ γ
  have first (x : (Bel C.book).Field d) : Tendsto (fun r=>(J r d).symm (A r d x)) Trace.Pilot.trail (𝓝 x) :=
    fitted_relative B M F J g μ γ hG leading live hγ d x
  have next := PhysMS.Frame.fitted_up F (neighboring B M F J g μ γ hG leading live hγ) d v
  let U (r : ℝ) := ((J r d).symm.toLinearMap.comp (A r d).toLinearMap)
  have strong := Dash.fit_plane U LinearMap.id first
  apply (Dash.arcing strong next).congr
  intro r
  change (J r d).symm ((A r d) ((A r d).symm (positioned B M F J g μ γ r d v))) = _
  rw [LinearEquiv.apply_symm_apply]

theorem own (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : ∀ d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Trace.Pilot.Coupling G γ)
    (d q : ℕ) (positive : 0<d) : ∀ᶠ r in Trace.Pilot.trail,∀ hr : 0<r,∀ v∈Peak C.labels d,∀ b,
      let c := (WilsonMacroscopicRichFree.basis C B d).equivFun v
      ‖(exterior B J (g d) hr b).charge F d (positioned B M F J g μ γ r d v) -
        (WilsonMacroscopicRichSignedMS.jet B M d (g d) (μ d) q (γ r)).vecMul c b‖ ≤
        (∑a,‖c a‖)*((‖WilsonOrdinaryAllOrderPivot.rows B M d (g d) (μ d) (q+1)‖+2)*(γ r)^(q+1)) := by
  filter_upwards [(WilsonOrdinaryAllOrderPivot.original B M F J d (g d) (μ d) hG leading (live d) hγ).2 q] with r paid
  intro hr v top b
  rw [positioned,uncompromised F _ d v top,fitted,if_neg (Nat.ne_of_gt positive)]
  exact paid hr v b

/-- The top vectors are genuinely present: each originally preassigned MS
glyph is in its own Maxwell engineering eigenspace on the real comparator. -/
theorem free_glyph (d : ℕ) (a : Glyph B d) :
    WilsonMacroscopicRichFree.basis C B d a=WilsonFactoryGlyphEngineering.column B C.labels d a := by
  apply Extra.FD.writes_inj C.labels d
  rw [WilsonMacroscopicRichFree.letters,WilsonFactoryGlyphEngineering.column,RG11.Fields.enroll_write]
  have certified := WilsonFactoryOnShellGlyphs.glyph B d a
  rw [MS.Theater.readHeight] at certified
  exact certified.symm

theorem named (d : ℕ) (a : Glyph B d) (own_grade : a.size=d) :
    WilsonMacroscopicRichFree.basis C B d a∈Peak C.labels d := by
  rw [free_glyph B d a]
  change gear C.labels d 2 _-(2:ℂ)^d • _=0
  rw [WilsonFactoryGlyphEngineering.height,show a.1.val=d from own_grade]
  norm_num


/-- Ground the vacuum in the original orientation before raising it into
the entire repaired physical tower. -/
theorem unit (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : ∀ d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Trace.Pilot.Coupling G γ)
    (d : ℕ) : ∀ᶠ r in Trace.Pilot.trail,positioned B M F J g μ γ r d ((Bel C.book).unit d)=S.unit d := by
  have base (r : ℝ) : positioned B M F J g μ γ r 0 ((Bel C.book).unit 0) = J r 0 ((Bel C.book).unit 0) := by
    unfold positioned PhysMS.Frame.compatible
    split <;> rfl
  filter_upwards [included B M F J g μ γ hG leading live hγ (Nat.zero_le d),leading.unit 0] with r inc vac
  have ground := (Free.scheme C.labels).fixs (Free.scheme_filters C.labels) (Free.hierarchy C.labels).laws (Nat.zero_le d)
  rw [←ground,inc,base,vac,F.sector.derivatives.fixs F.phase.transport.injection F.room.kernel.laws]

/-- In every arity and derivative order of the genuine full position-space
correlators the repaired fields retain the original free leading behavior. -/
theorem correlations (hG : G.Simple) (leading : PhysMS.Leading F J)
    (live : ∀ d,IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (g d))) (hγ : Trace.Pilot.Coupling G γ)
    {n : ℕ} (d : Caps n) (v : MaxwellSlots C d) (j : ℕ) (K : Set (Points n)) (hc : IsCompact K) (within : K⊆conf n) :
    TendstoUniformlyOn (fun r=>iteratedFDeriv ℝ j (PhysMS.measured F none (positioned B M F J g μ γ r) v r))
      (iteratedFDeriv ℝ j (WickGoal v)) Trace.Pilot.trail K := by
  let w : ℝ→MaxwellSlots C d := fun r i=>(J r (d i)).symm (positioned B M F J g μ γ r (d i) (v i))
  have small (i) : Tendsto (fun r=>w r i) Trace.Pilot.trail (𝓝 (v i)) :=
    relative B M F J g μ γ hG leading live hγ (d i) (v i)
  have pos : ∀ᶠ r : ℝ in Trace.Pilot.trail,0<r := self_mem_nhdsWithin
  have got := PhysMS.Frame.measured_tensor (v:=fun _=>none) (P:=J) (r:=fun r : ℝ=>r) F pos d j
    (fun i=>WilsonMacroscopicRichFree.basis C B (d i)) hc within
    (fun y=>leading.lead n d (fun i=>WilsonMacroscopicRichFree.basis C B (d i) (y i)) j K hc within) small
  have same (r : ℝ) : PhysMS.measured F none (J r) (w r) r = PhysMS.measured F none (positioned B M F J g μ γ r) v r := by
    funext x
    unfold PhysMS.measured w
    simp only [LinearEquiv.apply_symm_apply]
  simpa only [same] using got

end YM.Integration.WilsonOrdinaryPositionGrades
end


