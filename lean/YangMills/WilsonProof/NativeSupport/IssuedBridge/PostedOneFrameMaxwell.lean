import YM.Integration.WilsonOneFrameUnit
import YangMills.WilsonProof.NativeSupport.FrameNormalization
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YangMills.WilsonProof.NativeSupport.WardBridge
import YM.Integration.WilsonOneFrameOriginalPhases
import YM.Integration.WilsonOneFrameMixedMaxwell
import YM.Integration.WilsonOneFrameEngineering
import YM.Integration.WilsonOneFrameFixedReadings
import YM.Integration.WilsonOneFrameFieldDerivative

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
universe u
namespace YangMills.SelectedWilsonFrame
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {R : Run g.core}
variable {p : Extraction.Order} {S : Table R.family.book}
variable {F : Final R.family p S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
variable {L : EveryPhase.Almanac F} {J : ℝ → PhysMS.tower S}
variable {arch : Trace.Terrace.Arch R.family} {Y : (Bel R.family.book).Hierarchy}
variable {ℓ : Ultrafilter (ℕ × ℕ)} {simple : g.core.Simple} {cohort : Ultrafilter (ℕ × ℕ) → Prop}
variable {n : ℕ}
variable (run : WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y arch ℓ simple cohort)
variable (Z : WilsonPrescription g.core) (radii : Climb.Scaling S)
local notation "C" => R.family
local notation "B" => maxwellReference g
local notation "T" => hierarchy F Q
local notation "H" => homogeneous F J Z
local notation "X" => WilsonOneFrameFixedReadings.ruler F J Z radii

private def viewFrame (r : ℝ) : AllRadii.Frame B T :=
  fun d => (YM.Maxwell.Free.fields (C).labels d).symm.trans (H r d)

private lemma radii_tend : Tendsto radii.r atTop Trace.Pilot.trail :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ radii.drips (Eventually.of_forall radii.positive)
private def slots {n : ℕ} (q : Fin n → Σ d, (B).sector d)
    (marked : Fin n → Bool) (ab : Fin n → Axis × Axis) (i : Fin n) : Slot R.family :=
  if marked i then .inr (ab i) else .inl ⟨(q i).1, (YM.Maxwell.Free.fields (C).labels _).symm (q i).2⟩

include run in
private theorem mixed
    (n j : ℕ) (q : Fin n → Σ d, (B).sector d) (marked : Fin n → Bool)
    (ab : Fin n → Axis × Axis) (K : Set (Points n)) (compact : IsCompact K)
    (sep : K ⊆ YangMills.separated n) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s, AllRadii.JetBound B T r (viewFrame (F:=F) (Q:=Q) (J:=J) Z r) j q marked ab K ε s := by
  let v := slots (R := R) q marked ab
  let physicalTag (r : ℝ) (w : Slot R.family) : S.Tag := ⟨cap w, filed (F:=F) (J:=J) Z r w⟩
  let polynomial (w : Slot R.family) := supply (C).labels ⟨cap w, wick w⟩
  have physical (r : ℝ) (s : Viewers F) (y : Points n) :
      S.classMoment (spectator F s) (cap ∘ v) (r • y) (fun i => filed (F:=F) (J:=J) Z r (v i)) =
        (T).correlation s (fun i => if marked i then
          ⟨4, ((r^4 : ℝ) : ℂ) • (T).stress (ab i).1 (ab i).2⟩ else
          ⟨(q i).1, viewFrame (F:=F) (Q:=Q) (J:=J) Z r _ (q i).2⟩) (r • y) := by
    apply congrArg (S.useAt (spectator F s) (r • y))
      (a₁ := fun i => ⟨cap (v i), filed (F:=F) (J:=J) Z r (v i)⟩)
    funext i
    change physicalTag r (v i) = _
    unfold v slots
    split_ifs <;> rfl
  have free (y : Points n) :
      PhysMS.WickGoal (fun i => wick (v i)) y =
        (B).moment y (fun i => if marked i then ((B).stress (ab i).1 (ab i).2).val else (q i).2.val) := by
    change YM.Ward.disc (fun i => ⟨cap (v i), wick (v i)⟩) y = _
    rw [YM.Ward.disc, display]
    congr 1
    funext i
    change polynomial (v i) = _
    unfold v slots
    split_ifs
    · change address (C).labels 4 (-Free.original (C).labels _ _) = _
      rw [map_neg,inertia]
      rfl
    · exact congrArg Subtype.val ((YM.Maxwell.Free.fields (C).labels _).apply_symm_apply _)
  filter_upwards [WilsonOneFrameMixedMaxwell.original run Z v j K compact sep ε pos] with r bound s x hx
  have joint := bound x hx s
  rw [funext (physical r s), funext free] at joint
  exact joint.le


include run in
def scaling : (T).MaxwellScaling B where
  r := radii.r
  positive := radii.positive
  later := radii.later
  drips := radii.drips
  frame k := viewFrame (F:=F) (Q:=Q) (J:=J) Z (radii.r k)
  jets n j q marked ab K hK hc ε he := by
    filter_upwards [(radii_tend radii).eventually (mixed run Z n j q marked ab K hK hc ε he)] with k hk
    exact hk none

local notation "scale" => scaling run Z radii

private theorem stress_name (i j : Axis) :
    (YM.Maxwell.Free.fields (C).labels 4).symm ((B).stress i j) = Pert.freeStress (C).labels i j := by
  apply (YM.Maxwell.Free.fields (C).labels 4).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change _ = address (C).labels 4 (-Free.original (C).labels i j)
  rw [map_neg,inertia]
  rfl

theorem allRadii : AllRadii.Laws B T scale (viewFrame (F:=F) (Q:=Q) (J:=J) Z) := by
  constructor
  · intro k
    rfl
  · intro i j
    change Tendsto (fun r => (X).U 0 4 ((YM.Maxwell.Free.fields (C).labels 4).symm
      ((YM.Maxwell.Free.fields (C).labels 4) ((H r 4).symm (r^4 • F.sector.energy i j))))) _
      (𝓝 ((X).U 0 4 ((YM.Maxwell.Free.fields (C).labels 4).symm ((B).stress i j))))
    simp only [LinearEquiv.symm_apply_apply,stress_name (R:=R) i j]
    exact (((X).U 0 4).toLinearMap.continuous_of_finiteDimensional.tendsto _).comp
      (WilsonOneFrameMeasuredStress.original run Z i j)
  · exact mixed run Z
private def publicTag (v : (freeTable R.family.labels).Tag) : Σ d, (B).sector d :=
  ⟨v.1, YM.Maxwell.Free.fields (C).labels v.1 v.2⟩

private lemma freeRead (q : Fin n → (freeTable (C).labels).Tag) (x : Points n) :
    YM.Ward.disc q x = (B).moment x (fun i => (publicTag (q i)).2.val) := by
  rw [YM.Ward.disc, display]; rfl

private lemma freeHead {d : ℕ} (v : (freeTable (C).labels).Field d)
    (w : Fin n → (freeTable (C).labels).Tag) (x : Points (n+1)) :
    YM.Ward.disc (Fin.cons (α := fun _ : Fin (n+1) => (freeTable (C).labels).Tag) ⟨d,v⟩ w) x =
      (B).moment x (Fin.cons ((YM.Maxwell.Free.fields (C).labels d v).val) (fun i => (publicTag (w i)).2.val)) := by
  rw [freeRead]
  exact congrArg ((B).moment x) (Fin.comp_cons (fun t : (freeTable (C).labels).Tag => (publicTag t).2.val) ⟨d,v⟩ w)

private lemma column_iff (d : ℕ) (u : ℕ → S.Field d) (v : (B).sector d) :
    Aligned B T scale d u v ↔ Tendsto (fun k => ((X).U k d).symm (u k)) atTop
      (𝓝 ((YM.Maxwell.Free.fields (C).labels d).symm v)) := by
  have eqn (k : ℕ) : (scale).frame 0 d (((scale).frame k d).symm (u k)) =
      (X).U 0 d (((X).U k d).symm (u k)) := by
    change (X).U 0 d ((YM.Maxwell.Free.fields (C).labels d).symm ((YM.Maxwell.Free.fields (C).labels d) _)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  unfold Aligned
  simp_rw [eqn]
  constructor
  · intro h
    have hh := (((X).U 0 d).symm.toLinearMap.continuous_of_finiteDimensional.tendsto _).comp h
    change Tendsto (fun k => ((X).U 0 d).symm ((X).U 0 d (((X).U k d).symm (u k)))) atTop
      (𝓝 (((X).U 0 d).symm ((X).U 0 d ((YM.Maxwell.Free.fields (C).labels d).symm v)))) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  · intro h
    exact (((X).U 0 d).toLinearMap.continuous_of_finiteDimensional.tendsto _).comp h

private def probeOf (e : Exterior (standard (C).labels)) : Probe B where
  n := e.n
  point := e.point
  separated := e.clear
  spectators i := publicTag ((freeTable (C).labels).classTokens (e.letter i))

private theorem detector : Detects B T scale := by
  classical
  intro d
  obtain ⟨D,hD,detect⟩ := WilsonOneFrameFixedReadings.original F J Z run.leading run.obeys simple radii d
  have freeSide (e : Exterior (standard (C).labels)) (v : (B).sector d) : Work.A04.row (freeTable (C).labels) d e ((YM.Maxwell.Free.fields (C).labels d).symm v) =
      (B).moment e.point (Fin.cons v.val (fun i => ((probeOf e).spectators i).2.val)) := by
    rw [Work.A04.row_eq (table_sym _)]
    unfold Work.A04.tags
    rw [freeHead,LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨D.image (probeOf (R := R)),?_,fun u v read => (column_iff run Z radii d u v).mpr ?_⟩
  · intro v w he
    apply (YM.Maxwell.Free.fields (C).labels d).symm.injective
    apply hD
    funext e
    change Work.A04.row _ d e.val _ = Work.A04.row _ d e.val _
    rw [freeSide,freeSide]
    exact he (probeOf e.val) (Finset.mem_image_of_mem _ e.property)
  apply detect
  intro e he
  have h := read (probeOf e) (Finset.mem_image_of_mem _ he)
  have publicSide (k : ℕ) : (T).correlation none
      (Fin.cons (α := fun _ : Fin (e.n+1) => (T).Tag) ⟨d,u k⟩
        (fun i => ⟨((probeOf e).spectators i).1,(scale).frame k _ ((probeOf e).spectators i).2⟩))
      ((X).r k • e.point) = WilsonOneFrameFixedReadings.mixedRow F J Z radii d e k (u k) := by
    apply congrArg (fun w => S.useAt S ((X).r k • e.point) w)
    apply congrArg (Fin.cons (α := fun _ : Fin (e.n+1) => S.Tag) ⟨d,u k⟩)
    funext i
    let t := (freeTable (C).labels).classTokens (e.letter i)
    change (⟨t.1,(X).U k t.1 ((YM.Maxwell.Free.fields (C).labels t.1).symm (YM.Maxwell.Free.fields (C).labels t.1 t.2))⟩ : S.Tag) = ⟨t.1,(X).U k t.1 t.2⟩
    rw [LinearEquiv.symm_apply_apply]
  rw [freeSide]
  exact h.congr (fun k => publicSide k)

private lemma derivativeRead (d : ℕ) (j : Axis) (v : (freeTable (C).labels).Field d) :
    WickDerivative B j (YM.Maxwell.Free.fields (C).labels d v)
      (YM.Maxwell.Free.fields (C).labels (d+1) ((Free.scheme (C).labels).deriv d j v)) := by
  intro n q x hx
  let w (i : Fin n) : (freeTable (C).labels).Tag := ⟨(q i).1,(YM.Maxwell.Free.fields (C).labels _).symm (q i).2⟩
  have read {e : ℕ} (z : (freeTable (C).labels).Field e) (y : Points (n+1)) :
      YM.Ward.disc (Fin.cons (α := fun _ : Fin (n+1) => (freeTable (C).labels).Tag) ⟨e,z⟩ w) y =
        (B).moment y (Fin.cons ((YM.Maxwell.Free.fields (C).labels e z).val) (fun i => (q i).2.val)) := by
    rw [freeHead]
    simp only [publicTag,w,LinearEquiv.apply_symm_apply]
  have h := (Free.scheme_derives (C).labels).kernels d j v hx w
  change YM.Ward.disc _ x = Ward.firstDerivative j (fun y => YM.Ward.disc _ y) x at h
  simpa only [read] using h


private theorem appointedAllJets : PhaseJets B T scale := by
  intro n j q marked ab K hK hc ε he
  filter_upwards [(radii_tend radii).eventually (mixed run Z n j q marked ab K hK hc ε he)] with k hk x hx s
  exact hk s x hx

private theorem appointedUnit : ∃ (u : (T).Field 0) (v : (B).sector 0), (T).toLabel 0 u = (T).toLabel 4 (T).unitAtFour ∧
    v.val = 1 ∧ Aligned B T scale 0 (engineering B T scale 0 u) v := by
  let v := (Bel R.family.book).unit 0
  refine ⟨S.unit 0,YM.Maxwell.Free.fields (C).labels 0 v,F.sector.derivatives.unit_same F.room.kernel.laws.toSymmetric
    (spectate_ready F none) F.room.kernel.laws,Free.unit_address (C).labels 0,?_⟩
  apply (column_iff run Z radii ..).mpr
  rw [LinearEquiv.symm_apply_apply]
  simp only [FixedFields.engineering,pow_zero,Complex.ofReal_one,one_smul]
  change Tendsto ((fun r => (homogeneous F J Z r 0).symm (S.unit 0)) ∘ radii.r) atTop (𝓝 ((Bel R.family.book).unit 0))
  exact (WilsonOneFrameUnit.original F J Z run.leading run.obeys simple 0).comp (radii_tend radii)

private theorem appointedStress : ∀ (i j : Axis),
    Aligned B T scale 4 (engineering B T scale 4 ((T).stress i j)) ((B).stress i j) := by
  intro i j
  apply (column_iff run Z radii ..).mpr
  rw [stress_name]
  exact (WilsonOneFrameMeasuredStress.original run Z i j).comp (radii_tend radii)

private theorem appointedDerivatives : ∃ W : (T).StressWardLaws, ∀ (d : ℕ) (j : Axis) (a : (T).Field d) (v : (B).sector d),
    Aligned B T scale d (engineering B T scale d a) v →
    ∃ w : (B).sector (d+1), WickDerivative B j v w ∧
      Aligned B T scale (d+1) (engineering B T scale (d+1) (W.derivative d j a)) w := by
  refine ⟨publicWards F Q,fun d j a v ha => ?_⟩
  let z := (YM.Maxwell.Free.fields (C).labels d).symm v
  refine ⟨YM.Maxwell.Free.fields (C).labels _ ((Free.scheme (C).labels).deriv d j z),?_,?_⟩
  · simpa only [z,LinearEquiv.apply_symm_apply] using derivativeRead (R:=R) d j z
  · apply (column_iff run Z radii ..).mpr
    rw [LinearEquiv.symm_apply_apply]
    exact WilsonOneFrameFieldDerivative.original F J Z run.leading run.obeys simple radii j a z
      ((column_iff run Z radii ..).mp ha)


private lemma zeroDistance (f g : Points n → ℂ) (x : Points n) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g x‖ = ‖f x - g x‖ := by
  simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map]

include run in
private theorem physicalValue (d : Caps n) (u : ℕ → (i : Fin n) → S.Field (d i))
    (v : MaxwellSlots (C) d)
    (ha : ∀ i, Tendsto (fun k => ((X).U k (d i)).symm (u k i)) atTop (𝓝 (v i)))
    (K : Set (Points n)) (hK : IsCompact K) (hc : K ⊆ conf n) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s : Viewers F,
      ‖S.classMoment (spectator F s) d (radii.r k • x) (u k) - PhysMS.WickGoal v x‖ ≤ ε := by
  have bought := WilsonOneFrameMixedMaxwell.columns run Z radii.r (radii_tend radii) d u v ha 0 K hK hc ε he
  filter_upwards [bought] with k hk x hx s
  exact (zeroDistance _ _ _).ge.trans (hk x hx s).le

private theorem sectorMoment {d : Caps n} (v : (i : Fin n) → (B).sector (d i)) (x : Points n) :
    YM.Ward.disc (fun i => (⟨d i,(YM.Maxwell.Free.fields (C).labels (d i)).symm (v i)⟩ :
      (freeTable (C).labels).Tag)) x = (B).moment x (fun i => (v i).val) := by
  rw [YM.Ward.disc, display]
  congr 1
  funext i
  exact congrArg Subtype.val ((YM.Maxwell.Free.fields (C).labels (d i)).apply_symm_apply (v i))


private theorem appointedLimit : ∀ (n : ℕ) (d : Fin n → ℕ) (u : ℕ → (i : Fin n) → (T).Field (d i)) (v : (i : Fin n) → (B).sector (d i)),
    (∀ i, Aligned B T scale (d i) (fun k => u k i) (v i)) →
    ∀ (K : Set (Points n)), IsCompact K → K ⊆ separated n → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∀ x ∈ K, ∀ s : Option (T).Character,
        ‖(T).correlation s (fun i => ⟨d i,u k i⟩) ((scale).r k • x) - (B).moment x (fun i => (v i).val)‖ ≤ ε := by
  intro n d u v ha K hK hc ε he
  let z (i : Fin n) := (YM.Maxwell.Free.fields (C).labels (d i)).symm (v i)
  have earned := physicalValue run Z radii d u z
    (fun i => (column_iff run Z radii ..).mp (ha i)) K hK hc ε he
  filter_upwards [earned] with k hk x hx s
  rw [← sectorMoment (R:=R) v x]
  exact hk x hx s

theorem fixed : FixedFields.Laws B T scale where
  allJets := appointedAllJets run Z radii
  phaseBound _ a _ hK hc _ hd := WilsonOneFrameOriginalPhases.phase_bound F run.facilities.toServices
    (fun i => (a i).1) (fun i => (a i).2) hK hc hd
  phaseDerivatives _ j a _ hr hlim _ hK hc _ he :=
    WilsonOneFrameOriginalPhases.original F run.facilities.toServices a hr hlim j hK hc he
  unit := appointedUnit run Z radii
  stress := appointedStress run Z radii
  derivatives := appointedDerivatives run Z radii
  finiteReadings := detector run Z radii
  limit := appointedLimit run Z radii

theorem bounds : AllRadii.FrameBounds B T scale (viewFrame (F:=F) (Q:=Q) (J:=J) Z) := by
  constructor
  · intro d e he φ kill δ pos
    have annihilates : ∀ v ∈ OPE.Levy.planeAt (U := F.sector.derivatives) e he, φ v = 0 := by
      cases e with
      | zero =>
        intro v hv
        have hv0 : v = 0 := by simpa [OPE.Levy.planeAt] using hv
        rw [hv0]
        exact φ.map_zero
      | succ k =>
        rintro _ ⟨u, rfl⟩
        apply kill k (Nat.lt_succ_self k) u
        exact F.sector.derivatives.stays F.room.kernel.laws.toSymmetric (spectate_ready F none) _ u
    obtain ⟨A,hA,h⟩ := WilsonOneFrameEngineering.original F J Z run.leading run.obeys simple d e he φ annihilates δ pos
    let M := ((X).U 0 d).symm.toLinearMap.toContinuousLinearMap
    refine ⟨A * ‖M‖,mul_nonneg hA M.opNorm_nonneg,?_⟩
    filter_upwards [h,self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with r hr hp u
    change ‖φ (H r d ((YM.Maxwell.Free.fields (C).labels d).symm ((YM.Maxwell.Free.fields (C).labels d) (M u))))‖ ≤ _
    rw [LinearEquiv.symm_apply_apply]
    calc
      _ ≤ A*r^((e:ℝ)-δ)*‖M u‖ := hr.1 (M u)
      _ ≤ A*r^((e:ℝ)-δ)*(‖M‖*‖u‖) := mul_le_mul_of_nonneg_left (M.le_opNorm u)
        (mul_nonneg hA (Real.rpow_nonneg hp.le _))
      _ = _ := by ring
  · intro d δ pos
    obtain ⟨_,_,h⟩ := WilsonOneFrameEngineering.original F J Z run.leading run.obeys simple d 0
      (Nat.zero_le _) 0 (fun _ _ => rfl) δ pos
    let M := ((X).U 0 d).toLinearMap.toContinuousLinearMap
    refine ⟨2*‖M‖,by positivity,?_⟩
    filter_upwards [h] with r hr u
    change ‖M ((YM.Maxwell.Free.fields (C).labels d).symm ((YM.Maxwell.Free.fields (C).labels d) ((H r d).symm u)))‖ ≤ _
    rw [LinearEquiv.symm_apply_apply]
    calc
      _ ≤ ‖M‖ * ‖(H r d).symm u‖ := M.le_opNorm _
      _ ≤ ‖M‖ * (2*r^(-(d:ℝ)-δ)*‖u‖) := mul_le_mul_of_nonneg_left (hr.2 u) M.opNorm_nonneg
      _ = _ := by ring

include run radii in
theorem _root_.IssuedBridge.PostedOneFrameMaxwell.original :
    ∃ V : (T).MaxwellScaling B, FixedFields.Laws B T V ∧
      AllRadii.Laws B T V (fun r d => (YM.Maxwell.Free.fields (C).labels d).symm.trans (H r d)) ∧
      AllRadii.FrameBounds B T V (fun r d => (YM.Maxwell.Free.fields (C).labels d).symm.trans (H r d)) :=
  ⟨scale, fixed run Z radii, allRadii run Z radii, bounds run Z radii⟩

end YangMills.SelectedWilsonFrame
end
