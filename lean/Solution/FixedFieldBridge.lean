import YangMills.WilsonProof.SampledCoordinates
import Solution.FixedColumns
import MaxwellBridge
import WardBridge

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YangMills.FixedFields
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open Function Filter Set
open scoped Topology BigOperators

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (X : Climb.Scaling S) (first : Pert.FirstExtension F X)
local notation "B" => maxwellReference g
local notation "T" => hierarchy F Q
local notation "scale" => publicScaling F Q X first
variable {n : ℕ}

private def publicTag (v : (freeTable C.labels).Tag) : Σ d, (B).sector d :=
  ⟨v.1, fields C.labels v.1 v.2⟩

private lemma freeRead (q : Fin n → (freeTable C.labels).Tag) (x : Points n) :
    YM.Ward.disc q x = (B).moment x (fun i => (publicTag (q i)).2.val) := by
  rw [YM.Ward.disc, display]; rfl

private lemma freeHead {d : ℕ} (v : (freeTable C.labels).Field d)
    (w : Fin n → (freeTable C.labels).Tag) (x : Points (n+1)) :
    YM.Ward.disc (Fin.cons (α := fun _ : Fin (n+1) => (freeTable C.labels).Tag) ⟨d,v⟩ w) x =
      (B).moment x (Fin.cons ((fields C.labels d v).val) (fun i => (publicTag (w i)).2.val)) := by
  rw [freeRead]
  exact congrArg ((B).moment x) (Fin.comp_cons (fun t : (freeTable C.labels).Tag => (publicTag t).2.val) ⟨d,v⟩ w)

private lemma column_iff (d : ℕ) (u : ℕ → S.Field d) (v : (B).sector d) :
    Aligned B T scale d u v ↔ Tendsto (fun k => (X.U k d).symm (u k)) atTop
      (𝓝 ((fields C.labels d).symm v)) := by
  have eqn (k : ℕ) : (scale).frame 0 d (((scale).frame k d).symm (u k)) =
      X.U 0 d ((X.U k d).symm (u k)) := by
    change X.U 0 d ((fields C.labels d).symm ((fields C.labels d) _)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  unfold Aligned
  simp_rw [eqn]
  constructor
  · intro h
    have hh := ((X.U 0 d).symm.toLinearMap.continuous_of_finiteDimensional.tendsto _).comp h
    change Tendsto (fun k => (X.U 0 d).symm (X.U 0 d ((X.U k d).symm (u k)))) atTop
      (𝓝 ((X.U 0 d).symm (X.U 0 d ((fields C.labels d).symm v)))) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · intro h
    exact ((X.U 0 d).toLinearMap.continuous_of_finiteDimensional.tendsto _).comp h

private def probeOf (e : Exterior (standard C.labels)) : Probe B where
  n := e.n
  point := e.point
  separated := e.clear
  spectators i := publicTag ((freeTable C.labels).classTokens (e.letter i))

private theorem detector : Detects B T scale := by
  classical
  intro d
  obtain ⟨D,hD,detect⟩ := FixedFieldMaxwell.finite_readings F d
  have freeSide (e : Exterior (standard C.labels)) (v : (B).sector d) : Work.A04.row (freeTable C.labels) d e ((fields C.labels d).symm v) =
      (B).moment e.point (Fin.cons v.val (fun i => ((probeOf e).spectators i).2.val)) := by
    rw [Work.A04.row_eq (table_sym _)]
    unfold Work.A04.tags
    rw [freeHead,LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨D.image (probeOf (C := C)),?_,fun u v read => (column_iff F Q X first d u v).mpr ?_⟩
  · intro v w he
    apply (fields C.labels d).symm.injective
    apply hD
    funext e
    change Work.A04.row _ d e.val _ = Work.A04.row _ d e.val _
    rw [freeSide,freeSide]
    exact he (probeOf e.val) (Finset.mem_image_of_mem _ e.property)
  apply detect first
  intro e he
  have h := read (probeOf e) (Finset.mem_image_of_mem _ he)
  have publicSide (k : ℕ) : (T).correlation none
      (Fin.cons (α := fun _ : Fin (e.n+1) => (T).Tag) ⟨d,u k⟩
        (fun i => ⟨((probeOf e).spectators i).1,(scale).frame k _ ((probeOf e).spectators i).2⟩))
      (X.r k • e.point) = FixedFieldMaxwell.mixedRow X d e k (u k) := by
    apply congrArg (fun w => S.useAt S (X.r k • e.point) w)
    apply congrArg (Fin.cons (α := fun _ : Fin (e.n+1) => S.Tag) ⟨d,u k⟩)
    funext i
    let t := (freeTable C.labels).classTokens (e.letter i)
    change (⟨t.1,X.U k t.1 ((fields C.labels t.1).symm (fields C.labels t.1 t.2))⟩ : S.Tag) = ⟨t.1,X.U k t.1 t.2⟩
    rw [LinearEquiv.symm_apply_apply]
  rw [freeSide]
  exact h.congr (fun k => publicSide k)

private lemma derivativeRead (d : ℕ) (j : Axis) (v : (freeTable C.labels).Field d) :
    WickDerivative B j (fields C.labels d v)
      (fields C.labels (d+1) ((Free.scheme C.labels).deriv d j v)) := by
  intro n q x hx
  let w (i : Fin n) : (freeTable C.labels).Tag := ⟨(q i).1,(fields C.labels _).symm (q i).2⟩
  have read {e : ℕ} (z : (freeTable C.labels).Field e) (y : Points (n+1)) :
      YM.Ward.disc (Fin.cons (α := fun _ : Fin (n+1) => (freeTable C.labels).Tag) ⟨e,z⟩ w) y =
        (B).moment y (Fin.cons ((fields C.labels e z).val) (fun i => (q i).2.val)) := by
    rw [freeHead]
    simp only [publicTag,w,LinearEquiv.apply_symm_apply]
  have h := (Free.scheme_derives C.labels).kernels d j v hx w
  change YM.Ward.disc _ x = Ward.firstDerivative j (fun y => YM.Ward.disc _ y) x at h
  simpa only [read] using h

theorem sampledEstimates (simple : g.core.Simple) (foundation : OPE.Orbits.Foundation F Q)
    (trace : Trace.Target.Result.{0} F simple) (H : Services C p S) : Laws B T scale where
  allJets := by
    intro n j q marked ab K hK hc ε he
    let v (i : Fin n) : (freeTable C.labels).Tag := ⟨(q i).1,(fields C.labels _).symm (q i).2⟩
    have h := YM.Existence.SelectedJets.ofTrace F X first simple Q foundation trace v marked ab j hK hc he
    have free (z : Points n) : YM.Ward.disc (Pert.freeWithStress C.labels v marked ab) z =
        Wick.moment g.core z (fun i => if marked i then -polStress g.core (ab i).1 (ab i).2 else (q i).2.val) := by
      rw [YM.Ward.disc,display]
      congr 1
      funext i
      change supply C.labels (Pert.freeWithStress C.labels v marked ab i) = _
      unfold Pert.freeWithStress
      split_ifs
      · change address C.labels 4 (-Free.original C.labels _ _) = _
        rw [map_neg,inertia]
      · exact congrArg Subtype.val ((fields C.labels _).apply_symm_apply _)
    rw [funext free] at h
    exact h
  phaseBound n a K hK hc δ hd := FixedFieldMaxwell.phase_bound F H (fun i => (a i).1) (fun i => (a i).2) hK hc hd
  phaseDerivatives n j a r hr hlim K hK hc ε he := FixedFieldMaxwell.phase_jets F H a hr hlim j hK hc he
  unit := by
    let v := (freeTable C.labels).unit 0
    refine ⟨S.unit 0,fields C.labels 0 v,F.sector.derivatives.unit_same F.room.kernel.laws.toSymmetric
      (spectate_ready F none) F.room.kernel.laws,Free.unit_address C.labels 0,?_⟩
    apply (column_iff F Q X first ..).mpr
    rw [LinearEquiv.symm_apply_apply]
    apply tendsto_const_nhds.congr'
    filter_upwards [first.fit.units 0] with k hk
    simp [engineering,ShortDistance.engineering,← hk,v]
  stress i j := by
    apply (column_iff F Q X first ..).mpr
    have eqn : (fields C.labels 4).symm ((B).stress i j) = Pert.freeStress C.labels i j := by
      apply (fields C.labels 4).injective
      rw [LinearEquiv.apply_symm_apply]; apply Subtype.ext
      change _ = address C.labels 4 (-Free.original C.labels i j)
      rw [map_neg,inertia]; rfl
    rw [eqn]
    exact FixedFieldMaxwell.stress_alignment F first i j
  derivatives := by
    refine ⟨publicWards F Q,fun d j a v ha => ?_⟩
    let z := (fields C.labels d).symm v
    refine ⟨fields C.labels _ ((Free.scheme C.labels).deriv d j z),?_,?_⟩
    · simpa only [z,LinearEquiv.apply_symm_apply] using derivativeRead d j z
    · apply (column_iff F Q X first ..).mpr
      rw [LinearEquiv.symm_apply_apply]
      exact FixedFieldMaxwell.derivative_alignment F first j a z ((column_iff F Q X first ..).mp ha)
  finiteReadings := detector F Q X first
  limit n d u v ha K hK hc ε he := by
    let z (i : Fin n) := (fields C.labels _).symm (v i)
    have free (x : Points n) : (freeTable C.labels).classMoment (freeTable C.labels) d x z =
        (B).moment x (fun i => (v i).val) := by
      have h := freeRead (C := C) (fun i => ⟨d i,z i⟩) x
      change YM.Ward.disc (fun i => ⟨d i,z i⟩) x = _
      simpa only [publicTag,z,LinearEquiv.apply_symm_apply] using h
    have bound (s : ℕ → Viewers F) := FixedFieldMaxwell.aligned_views F first simple Q foundation trace s d u z
      (fun i => (column_iff F Q X first ..).mp (ha i)) hK hc he
    have all := universalize (p := fun k (s : Viewers F) => ∀ x ∈ K,
      ‖S.classMoment (spectator F s) d (X.r k • x) (u k) - (freeTable C.labels).classMoment (freeTable C.labels) d x z‖ ≤ ε) bound
    filter_upwards [all] with k hk x hx s
    change ‖S.classMoment (spectator F s) d (X.r k • x) (u k) - _‖ ≤ ε
    simpa only [free] using hk s x hx

end YangMills.FixedFields
