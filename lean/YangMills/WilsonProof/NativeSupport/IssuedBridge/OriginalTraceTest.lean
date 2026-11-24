import YangMills.WilsonProof.NativeSupport.IssuedBridge.GroupSelectedJets

set_option autoImplicit false
noncomputable section
namespace YangMills.IssuedPhysical
open YM YM.Spec YM.OPE.Orbits YM.Nonperturbative YM.TraceExtension
open Function Set MeasureTheory Filter
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius NNReal
universe u v
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private def nativeMode (m : Hierarchy.Mode) : Wick.Mode :=
  ⟨m.mass,m.spatialOrder,m.timeOrder,m.numerator,m.continuous,m.homogeneous⟩
private def nativeTrack (t : Hierarchy.Track) : Wick.Track := ⟨t.n,nativeMode ∘ t.modes⟩
private def nativeTerms (t : List (ℂ × Hierarchy.Track)) : Wick.Collection :=
  t.map fun (c,q) => (c,nativeTrack q)
private theorem profile_eq (t : List (ℂ × Hierarchy.Track)) (r : ℝ) :
    Hierarchy.wickProfile t r = Wick.atPoint (nativeTerms t) r := by
  unfold Hierarchy.wickProfile Wick.atPoint nativeTerms
  rw [List.map_map]
  congr 1
private theorem award_eq (hg : g.IsSimple) :
    YM.Trace.Verse.award g.core = 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi^4 := by
  have h : g.core.lie = g.lieAlgebra := by ext v; exact (g.generates v).symm
  have dim : g.core.lieDim = Module.finrank ℝ g.lieAlgebra := congrArg (fun V : Submodule ℝ (Matrix (Fin (g.n+1)) (Fin (g.n+1)) ℂ) => Module.finrank ℝ V) h
  have hc := YM.Gauge.casimir_pos (G := g.core) (GaugeGroup.coreSimple hg)
  unfold YM.Trace.Verse.award
  rw [dim]
  unfold YM.Trace.Over.d2 YM.Trace.Over.b0 YM.Trace.Over.forceR YM.Gauge.slopeConstant
  field_simp [ne_of_gt hc, Real.pi_ne_zero]
  ring

/-- Transport the lattice unit through the quotient; each character table respects
the same null fields, so the same insertion deletes its slot in every phase. -/
private theorem unitInsertion (s : YM.OPE.Viewers F) {n : ℕ} (x : Points (n+1))
    (hx : x ∈ WilsonFamily.separated (n+1)) (v : Fin n → S.Tag) :
    S.useAt (YM.OPE.spectator F s) x (Fin.cons ⟨4, S.unit 4⟩ v) =
      S.useAt (YM.OPE.spectator F s) (YM.Points.tail x) v := by
  let A := YM.OPE.spectator F s
  let w : Fin n → C.book.Token := fun i => ⟨(v i).1, S.representative _ (v i).2⟩
  let row := Fin.cons (α := fun _ : Fin (n+1) => C.book.Token) (C.book.one 4) w
  have hw (i) : S.classTokens (w i) = v i := by
    change Sigma.mk (v i).1 (S.project _ (S.representative _ _)) = v i
    rw [S.rep]
  have hrow : Fin.cons (α := fun _ => S.Tag) ⟨4, S.unit 4⟩ v = S.classTokens ∘ row := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [row, Function.comp_apply, Fin.cons_succ, hw]
  change S.useAt A x (Fin.cons (α := fun _ => S.Tag) ⟨4, S.unit 4⟩ v) = S.useAt A (YM.Points.tail x) v
  rw [hrow, S.at_project A (YM.OPE.spectate F s).laws.toSymmetric
    (YM.OPE.spectate_respects F s) hx row, (YM.OPE.spectate F s).laws.unital hx 4 w]
  rfl

theorem publicTrace (hg : g.IsSimple) (H : Headline.TraceExclusions.{u,v} F) :
    (hierarchy F Q).TraceTest := by
  have ht : (hierarchy F Q).traceTwo = euclidean F := rfl
  refine ⟨fun s _ x _ v => YM.EveryPhase.Stress.one_variable v x 4 (YM.OPE.spectator F s),
    fun s _ x hx v => unitInsertion F s x hx v,
    fun f => YM.TraceExtension.Identity.op_unit F f 4,
    H.centered, (award_eq hg) ▸ H.positive, ?_, ?_⟩
  · rw [ht,← award_eq hg]
    exact H.shortDistance
  · intro terms e
    apply Wick.euclidean_excludes (F := F) H.shortDistance H.positive (nativeTerms terms)
    filter_upwards [e] with r hr
    exact (congrFun ht r).symm.trans (hr.trans (profile_eq terms r))
end YangMills.IssuedPhysical
end
