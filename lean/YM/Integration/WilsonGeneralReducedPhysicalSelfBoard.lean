import YM.Integration.WilsonOriginalPublicPlantedGramBudget
import YM.Integration.WilsonPositionProgramPublicDirectoryBoard

/-! The complete smooth physical quotient has a uniformly positive measured Gram
on the short finite inversion board, at its actual finite reporting coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfBoard
open Filter Set Function Finset MeasureTheory Metric Lattice Maxwell MS MS.Land MS.Menus Local.Physical
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Table.Pairing
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open WilsonPositionProgramPublicBulb WilsonPositionProgramPublicDirectoryCoin
open WilsonPositionProgramPublicDirectoryBoard (integral table)
open private difference measurable_read from YM.Integration.WilsonPositionProgramPublicDirectoryBoard
open private entry from YM.Integration.WilsonPositionCompactEpochSampling
open scoped Topology BigOperators Classical

variable {G:Gauge} (Z:WilsonPrescription G) {g:G.Simple}
    {S:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g S T dial) (a:Axis) (b:Bulb (center a) a) {d:ℕ}
    (v:Tags G d 2) (q:ℕ)

include H in
theorem cell (l:Filter ℝ) {t:ℝ→ℝ} (pos:∀ᶠ r in l,0<t r)
    (small:Tendsto t l (𝓝 0)) (D:ℕ)(J:ℝ) {δ:ℝ}(hδ:0<δ) :
    ∃i₀:ℕ,∀ᶠ r in l, ∀ i≥i₀,
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
  obtain ⟨i₁, paid⟩:=WilsonOriginalPublicPlantedGramBudget.original Z H v q space clear l pos small D J hδ
  refine ⟨max i₀ i₁,?_⟩
  filter_upwards [paid] with r wager i ge le B P cover c hc u hu
  let M:=Z.run.step i
  obtain ⟨caps,yes,fine,unit,large⟩:=start i ((le_max_left ..).trans ge)
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
    exact wager i ((le_max_right ..).trans ge) le P cover (node a M c y) rfl hc (inside y hy) u hu
variable (B:Deck G) (h:ℕ)

include H in
theorem original :
    ∃(b:Bulb (center a) a)(k:ℝ),0<k ∧
      ∀(q:ℕ)(l:Filter ℝ){t:ℝ→ℝ},(∀ᶠ r in l,0<t r) → Tendsto t l (𝓝 0) →
      ∀(D:ℕ)(J:ℝ),∃j₀:ℕ,∀ᶠ r in l,∀j≥j₀,(j:ℝ)≤J*(-Real.log (t r))^D →
      ∀{cap}(P:Handoff.Directory Z j cap),Handoff.Directory.budget G 2 h+q≤cap →
      ∀c∈(Z.run.step j).Box,∀u:ℝ,|u|≤8*t r → ∀v:Glyph B h→ℂ,
        k*‖v‖^2≤‖WilsonPositionProgramPublicContrast.assay v v
          (table Z a b q (id:Glyph B h→Glyph B h) P u c)‖:=by
  classical
  let leg:=id (α:=Glyph B h)
  obtain ⟨b,k,δ,hk,hδ,margin⟩:=WilsonPositionProgramPublicBulb.original a Z.scheme Z.store leg injective_id
  obtain ⟨j₀,coercive⟩:=eventually_atTop.mp ((goesFront (Expense.Stretched.runs Z.run)).eventually margin)
  refine ⟨b,k,hk,?_⟩
  intro q l t pos small D J
  choose first due using fun (j k:Glyph B h)=>cell Z H a b (signed a leg j k) q l pos small D J hδ
  refine ⟨j₀+∑j,∑k,first j k,?_⟩
  filter_upwards [eventually_all.mpr (fun j=>eventually_all.mpr (due j))] with r paid i hi short cap P levels c hc u hu
  apply coercive i ((Nat.le_add_right ..).trans hi) c hc
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
  intro k
  have own:first j k≤∑j,∑k,first j k:=
    (single_le_sum (fun _ _=>Nat.zero_le _) (mem_univ k)).trans
      (single_le_sum (f:=fun j=>∑k,first j k) (fun _ _=>Nat.zero_le _) (mem_univ j))
  exact paid j k i (own.trans ((Nat.le_add_left ..).trans hi)) short P levels c hc u hu

end YM.Integration.WilsonGeneralReducedPhysicalSelfBoard
