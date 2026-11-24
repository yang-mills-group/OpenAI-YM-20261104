import YM.Integration.WilsonPositionProgramPublicDirectoryGround

/-! The small change of the whole independently measured finite Handoff
under an actual compact reflected probe, including the original vacuum. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicDirectoryBoard
open Filter Set Function Finset MeasureTheory Metric Lattice Maxwell MS MS.Land MS.Menus Local.Physical
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Table.Pairing
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open WilsonPositionProgramPublicBulb WilsonPositionProgramPublicDirectoryCoin
open private tested from YM.Integration.WilsonPositionProgramPublicBulb
open private entry from YM.Integration.WilsonPositionCompactEpochSampling
open scoped Topology BigOperators Classical

variable {G:Gauge} (Z:WilsonPrescription G) {g:G.Simple}
    {S:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g S T dial) (a:Axis) (b:Bulb (center a) a) {d:ℕ}
    (v:Tags G d 2) (q:ℕ)

def integral {i B:ℕ} (P:Handoff.Directory Z i B)(u:ℝ)(c:Four ℝ):ℂ :=
  ∫y:Pair,weight a b y • drawValue Z v q P u (node a (Z.run.step i) c y).layout

private theorem measurable_read {E:Type*}[MeasurableSpace E](f:pack 2→E)(M:Mesh)(c:Four ℝ):
    Measurable (fun y:Pair=>f (node a M c y).layout):=by
  apply (measurable_of_countable f).comp
  apply measurable_pi_lambda
  intro t
  apply measurable_pi_lambda
  intro e
  apply Int.measurable_ceil.comp
  let C:Pair→Points (1+1):=(pairIso a (n:=1) (m:=1)).symm
  change Measurable fun y:Pair=>(C y t e+c e)/M.spacing
  have con:Continuous C:=(pairIso a (n:=1) (m:=1)).symm.continuous
  fun_prop

private theorem sampled (f:Pair→ℂ)(hf:Measurable f){t:ℝ}
    (paid:∀y,weight a b y≠0 → ‖f y‖≤t):Integrable (fun y=>weight a b y • f y):=by
  let w:=weight a b
  have hw:Integrable w:=b.bump.integrable_normed.mul_prod b.bump.integrable_normed
  apply (hw.mul_const t).mono' (hw.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  apply ae_of_all
  intro y
  have hp:0≤w y:=mul_nonneg (b.bump.nonneg_normed _) (b.bump.nonneg_normed _)
  change ‖w y • f y‖≤_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hp]
  by_cases hz:w y=0
  · simp [hz]
  exact mul_le_mul_of_nonneg_left (paid y hz) hp

private theorem difference (f h:Pair→ℂ)(mf:Measurable f)(mh:Measurable h) {C δ:ℝ}
    (ground:∀y,weight a b y≠0→‖h y‖≤C)
    (rest:∀y,weight a b y≠0→‖f y-h y‖≤δ):
    ‖(∫y:Pair,weight a b y • f y)-(∫y:Pair,weight a b y • h y)‖≤δ:=by
  have hg:=sampled a b h mh ground
  have hf:=sampled a b f mf (t:=δ+C) (fun y hy=>by
    calc ‖f y‖=‖(f y-h y)+h y‖:=by rw [sub_add_cancel]
         _ ≤ _ := (norm_add_le ..).trans (add_le_add (rest y hy) (ground y hy)))
  rw [←integral_sub hf hg]
  simp_rw [←smul_sub]
  simpa only [zero_sub,norm_neg] using tested a b (fun y=>f y-h y) 0 (mf.sub mh) (δ:=δ)
    (fun y hy=>by rw [zero_sub,norm_neg];exact rest y hy)

include H in
theorem cell (l:Filter ℝ) {t:ℝ→ℝ} (pos:∀ᶠ r in l,0<t r)
    (small:Tendsto t l (𝓝 0)) (D:ℕ)(J:ℝ) {δ:ℝ}(hδ:0<δ) :
    ∀ᶠ r in l, ∀ i≥WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀ {B} (P:Handoff.Directory Z i B),
      Handoff.Directory.budget G 2 d+q≤B → ∀ c∈(Z.run.step i).Box,∀ u:ℝ,|u|≤8*t r →
      ‖integral Z a b v q P u c-(∫y:Pair,weight a b y • Rose.cooked Z.scheme Z.store d
        (node a (Z.run.step i) c y) 0 v)‖≤δ := by
  let w:=tsupport b.bump
  let geom:Pair→Points (1+1):=(pairIso a (n:=1) (m:=1)).symm
  let K:=geom '' (w ×ˢ w)
  have compact:IsCompact K:=(b.bump.hasCompactSupport.prod b.bump.hasCompactSupport).image
    (pairIso a (n:=1) (m:=1)).symm.continuous
  have apart:K⊆conf 2:=by
    rintro _ ⟨y,hy,rfl⟩
    exact Table.Pairing.spans (b.active y.1 hy.1) (b.active y.2 hy.2)
  obtain ⟨Δ,positive,clear⟩:=compact.exists_cthickening_subset_open (conf_open _) apart
  have space:IsCompact (cthickening Δ K):=compact.cthickening
  obtain ⟨C,_,terms⟩:=WilsonPositionProgramPublicDirectoryCoin.terms Z H v q space clear
  have cx:Tendsto (fun i:ℕ=>(8:ℝ)*(Z.run.step i).spacing) atTop (𝓝 0):=by
    simpa only [mul_zero,comp_apply,Expense.a,id_eq] using (frontier.endpt.comp H.onSchedule).const_mul (8:ℝ)
  have ready:∀ᶠ i:ℕ in atTop,Rose.Use Z.scheme Z.criterion (Z.run.step i) ∧
      8*(Z.run.step i).spacing<Δ ∧ (Z.run.step i).spacing≤1 ∧ (16:ℝ)≤((Z.run.step i).p.side.val:ℝ):=by
    exact (((goesFront (Expense.Stretched.runs Z.run)).eventually (Rose.usable Z.scheme Z.criterion g)).and
      ((cx.eventually_lt_const positive).and ((H.onSchedule.eventually frontier.smaller).and
      ((frontier.horizon.comp H.onSchedule).eventually_ge_atTop 16))))
  obtain ⟨i₀,start⟩:=eventually_atTop.mp (terms.and ready)
  filter_upwards [WilsonPositionProgramPublicDirectoryGround.original Z H v q space clear l pos small D J hδ,
    (WilsonPositionAuxiliaryMesh.grows Z.run q l pos small).eventually_ge_atTop i₀] with
    r wager start' i ge le B P cover c hc u hu
  let M:=Z.run.step i
  obtain ⟨caps,yes,fine,unit,large⟩:=start i (start'.trans ge)
  have live (y:Points 1)(hy:b.r y≠0):y∈w:=by
    have h:y∈Function.support (b.bump.normed volume):=hy
    rw [b.bump.support_normed_eq] at h
    change y∈tsupport b.bump
    rw [b.bump.tsupport_eq]
    exact ball_subset_closedBall h
  have inside (y:Pair)(hy:weight a b y≠0):familiar (node a M c y)∈cthickening Δ K:=by
    have home:geom y∈K:=⟨y,⟨live _ (left_ne_zero_of_mul hy),live _ (right_ne_zero_of_mul hy)⟩,rfl⟩
    have corner:=M.upper_corner c (x:=draw (geom y) M c) (z:=geom y) rfl
    have near:dist (M.rel (draw (geom y) M c) c) (geom y)≤8*M.spacing:=by convert corner using 1;norm_num
    exact mem_cthickening_of_dist_le _ (geom y) Δ K home (near.trans fine.le)
  apply difference a b (fun y=>drawValue Z v q P u (node a M c y).layout)
    (fun y=>Rose.cooked Z.scheme Z.store d (node a M c y) 0 v)
    (measurable_read a _ _ _) (measurable_read a (fun h=>Rose.cooked Z.scheme Z.store d ⟨M,h,c⟩ 0 v) _ _)
  · intro y hy
    rw [←WilsonPositionProgramPublicDirectoryGround.point Z P _ rfl yes (by omega) v]
    apply caps P cover _ rfl (entry _ (by exact_mod_cast large) unit hc) (inside y hy) 0 (Nat.zero_le _)
  · intro y hy
    exact wager i ge le P cover (node a M c y) rfl hc (inside y hy) u hu

variable {B:Deck G}{I:Type}[Fintype I](leg:I→Glyph B d)

def table {i B':ℕ}(P:Handoff.Directory Z i B')(u:ℝ)(c:Four ℝ)(j k:I):ℂ:=
  integral Z a b (signed a leg j k) q P u c

include H in
theorem original (l:Filter ℝ) {t:ℝ→ℝ} (pos:∀ᶠ r in l,0<t r)
    (small:Tendsto t l (𝓝 0)) (D:ℕ)(J:ℝ) {δ:ℝ}(hδ:0<δ) :
    ∀ᶠ r in l, ∀ i≥WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀ {B'} (P:Handoff.Directory Z i B'),
      Handoff.Directory.budget G 2 d+q≤B' → ∀ c∈(Z.run.step i).Box,∀ u:ℝ,|u|≤8*t r →
      ‖table Z a b q leg P u c-Gram a Z.scheme Z.store leg b (Z.run.step i) c‖≤δ:=by
  have rows:∀ᶠ r in l,∀j k:I,∀i≥WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀ {B'}(P:Handoff.Directory Z i B'),
      Handoff.Directory.budget G 2 d+q≤B' → ∀c∈(Z.run.step i).Box,∀u:ℝ,|u|≤8*t r →
      ‖table Z a b q leg P u c j k-Gram a Z.scheme Z.store leg b (Z.run.step i) c j k‖≤δ :=
    eventually_all.mpr fun j=>eventually_all.mpr fun k=>cell Z H a b (signed a leg j k) q l pos small D J hδ
  filter_upwards [rows] with r wage i ge le B' P cover c hc u hu
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  exact fun k=>wage j k i ge le P cover c hc u hu
end YM.Integration.WilsonPositionProgramPublicDirectoryBoard
