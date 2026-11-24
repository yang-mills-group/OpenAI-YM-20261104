import YM.Integration.WilsonSeparatedContinuumRoster

/-! The actual moving joint signal is bounded over a full continuum compact,
with no near grid or finite stopping Plan. Real disjointness is also paid
there, which is needed for its Ward identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedContinuumAmplitude
open Filter Set Function Spec OPE OPE.Orbits PhysMS Trace.Pilot Pert Pert.Position RG17 Extraction Table Climb
open MS MS.Land MS.Menus MS.Local.Physical Next.UVStress OPE.Cards
open Frontier6.Road PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonSeparatedMovingRichGeometry WilsonSeparatedMovingRichVacuum
open scoped BigOperators Classical Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {V:Table R.family.book} {n:ℕ}

private lemma identify (F:Final R.family f V) {d:Caps n} {r:ℝ} (rp:0<r) {X:Points n} (sep:X∈conf n) (v:Labels V d) :
    Orbits.moment V (posed r X) v=V.classMoment V d (r • X) v := by
  change Orbits.moment V (r • X).ofLp v=_
  rw [Orbits.observed,named_fin V F.room.kernel.laws.toSymmetric _ (Work.A05.smul_conf rp sep)];rfl

theorem geometry (φ:Test 2) (K:Set (Points n)) (compact:IsCompact K) (safe:K⊆conf n) {a:ℝ} (top:a<1) :
    ∀ᶠ r in trail,∀ X∈K,∀ u∈tsupport φ,Injective (beside (posed r X) (far (r^a) u)) := by
  obtain ⟨M,η,_,_,near⟩:=RG17.roomCosts compact safe
  obtain ⟨N,δ,_,dp,farRoom⟩:=RG17.roomCosts (K:=tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  have zoom:Tendsto (fun r:ℝ=>r^(1-a)) trail (𝓝 0) := (PhysMS.length_rate.rpow (1-a)).tends (by linarith only [top]) PhysMS.to_log_zoom
  have flight:Tendsto (fun r:ℝ=>M*r^(1-a)) trail (𝓝 0) := by simpa only [mul_zero] using zoom.const_mul M
  filter_upwards [(tendsto_order.mp flight).2 _ dp,length_rate.pos] with r clear rp X hX u hu
  change 0<r at rp
  have τp:=Real.rpow_pos_of_pos rp a
  have normal:M*r<δ*r^a := by
    have h:=mul_lt_mul_of_pos_right clear τp
    rwa [mul_assoc,←Real.rpow_add rp,sub_add_cancel,Real.rpow_one] at h
  apply beside_distinct.mpr
  refine ⟨(Work.A05.smul_conf rp (safe hX)),fun i j _=>Subsingleton.elim i j,?_⟩
  intro i j eq
  have inner:‖(posed r X) i‖≤M*r := by simpa only [sub_zero] using (near r rp X hX).span i
  have outer:δ*r^a≤‖far (r^a) u j‖ := by
    simpa only [RG17.posed,far,smul_sub] using (farRoom (r^a) τp u hu).spaced j.succ 0 (Fin.succ_ne_zero j)
  exact (not_le_of_gt normal) (by rw [←eq] at outer;exact outer.trans inner)

theorem original (hG:G.Simple) (F:Final R.family f V) (fac:Facilities R.family f V)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower V) (lead:Leading F J)
    {A:(Bel R.family.book).Hierarchy} (obey:∀ h:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) h)
    (B:Deck G) (D:ℕ) (φ:Test 2) (d:Caps n) (K:Set (Points n)) (compact:IsCompact K) (sep:K⊆conf n)
    {a:ℝ} (ap:0<a) (top:a<1) {g:ℝ→ℝ} (hg:Coupling G g) :
    ∃ S:ℝ,0≤S ∧ ∀ᶠ r in trail,∀ X∈K,∀ u∈tsupport φ,∀ b:Glyph B D,∀ v:(i:Fin n)→Free R.family (d i),
    ‖whole V (posed r X) (Frame.born J r v) (far (r^a) u) (fields B D b J (r^a))‖≤S*∏ i,‖v i‖ := by
  obtain ⟨M,η,mp,ep,room⟩:=RG17.roomCosts compact sep
  obtain ⟨N,np,near⟩:=WilsonReportMomentEnvelope.purchased F J lead obey d K compact sep
  obtain ⟨H,hp,farBound⟩:=WilsonSeparatedMovingRichVacuum.original B F J lead D φ obey
  have p:=WilsonSeparatedContinuumRoster.original hG F fac Q J lead obey B D φ d ap top mp ep (sub_pos.mpr top) hg 0 one_pos
  have time:=PhysMS.length_rate.rpow a
  have rt:Tendsto (fun r:ℝ=>r^a) trail trail := tendsto_nhdsWithin_iff.mpr
    ⟨time.tends (by linarith only [ap]) PhysMS.to_log_zoom,time.pos⟩
  refine ⟨1+N*H,by positivity,?_⟩
  filter_upwards [p,near,rt.eventually farBound,length_rate.pos] with r charged origin farArm rp X hX u hu b v
  change 0<r at rp
  let y:=far (r^a) u
  let w:=fields B D b J (r^a)
  let ins:=Frame.born J r v
  let size:=∏ i,‖v i‖
  have n0 : 0 ≤ size :=Finset.prod_nonneg fun _ _=>norm_nonneg _
  let localValue:=Orbits.moment V (posed r X) ins
  let ext:=upon V 0 0 y w (V.unit 0)
  have trueNorm:‖localValue‖≤N*size := by rw [show localValue=_ from identify F rp (sep hX) ins];exact origin X hX v
  have diff:‖whole V (posed r X) ins y w-localValue*ext‖≤ size := by
    have h:=charged (posed r X) (room r rp X hX) u hu b v
    simp only [pow_zero,Real.rpow_zero,one_mul] at h;exact h
  have fore:‖ext‖≤H:=farArm b u hu
  calc
    _≤‖whole V (posed r X) ins y w-localValue*ext‖+‖localValue*ext‖ := norm_le_norm_sub_add _ _
    _≤ size+(N*size)*H := add_le_add diff (by rw [norm_mul];exact mul_le_mul trueNorm fore (norm_nonneg _) (mul_nonneg np.le n0))
    _=_ := by dsimp only [size];ring

end YM.Integration.WilsonSeparatedContinuumAmplitude
