import YM.Integration.WilsonViewerElectedHierarchy
import YM.Integration.WilsonExteriorCharacterCapture

/-! The alternating cutoff product and every ground character use the same original
counterterm, housing dates and fee, with independently placed physical exteriors. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalOriginalReplicaAndCharacter
open Function Filter Lattice Wilson Cells Extraction OPE OPE.Log OPE.Cards Frontier6.Road
open IntrinsicPhysicalCell IntrinsicProductCompactness WilsonExteriorReplicaCapture ActualFoundryDetectorSource
open WilsonMixedPlacement WilsonExteriorTrains WilsonViewerElectedHierarchy PhysicalNext.Repeat.Legato
open OPE.Orbits OPE.Orbits.Reader Climb
open scoped Topology Classical BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Spec.Final R.family f S} {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {L:EveryPhase.Almanac F} {Y:(Bel R.family.book).Hierarchy}
    {arch:Trace.Terrace.Arch R.family} {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple}
    {cohort:Ultrafilter (ℕ×ℕ)→Prop} (run:Selected.{u} F L Q J Y arch ℓ simple cohort)
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ}

private theorem small (S₀ : Schedule) (a c : ℝ) (hc : 0 < c) (base : ℕ) :
    ∃ k : ℕ, base ≤ k ∧ a * S₀.a k < c := by
  have h : Tendsto (fun k => a * S₀.a k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := a)).mul S₀.shrinks
  exact ((eventually_ge_atTop base).and (h.eventually (gt_mem_nhds hc))).exists

include run in
/-- A single invocation of the original cell estimator serves both the replica and
character receivers. Its radius threshold precedes every replica count. -/
theorem original {α : Type*} {l : Filter α} {T : α → ℝ}
    (anchor : I) (hT : Tendsto T l atTop) (D : ℕ)
    (v : α → (i : I) → R.family.label (d i)) (hv : ∀ i k, RateLE l T (fun s => v s i k) (-(d i : ℝ)))
    (y : E → E4) (hy : Injective (Sum.elim (fun _ : Unit => 0) y))
    (de : E → ℕ) (cap : E → ℝ) (hc : ∀ i, 0 < cap i) (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η)
    (apart : Apart η y) (away : ApartFrom η (fun _ : Unit => (0:E4)) y) :
    ∃ outer n₁ n₂ : ℕ, ∃ A : E → ℝ, (∀ i, 0 ≤ A i) ∧
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height R.family.S l T b h ∧ Height R.family.S l T m a ∧
      Height R.family.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
    ∃ fee : α → ℝ, RateLE l T fee (-(D:ℝ)-1/32) ∧ ∀ᶠ s in l,
    ∀ x : I → Cover, Plot R.family (b s) (m s) (j s) x →
      (∀ copies : ℕ, ∀ᶠ t : ℕ in atTop, ∀ᶠ w : ℕ×ℕ in f.fuse,
        ∀ e : (i:E) → R.family.label (de i), (∀ i, ‖e i‖ ≤ cap i) →
        ‖reading R.family w outer t copies y (discrepancy F.room.cutoff D (b s) (j s) x (v s) w) de e‖ ≤
          (fee s * ∏ i, (A i*R.family.S.a n₁^(-(de i:ℝ)-δ)+1))^(2*copies)) ∧
      (Screen (R.family.S.gridPoint (j s) ∘ x) → Injective (beside (R.family.S.gridPoint (j s) ∘ x) y) →
        ∀ e : (i:E) → R.family.label (de i), (∀ i, ‖e i‖ ≤ cap i) →
        ∀ l' : Filter (ℕ×ℕ), l'.NeBot → l' ≤ f.fuse → ∀ z : R.family.label D,
        Tendsto (fun w : ℕ×ℕ => value (D:=D) F.room.cutoff (b s) w
          (leaves R.family (j s) d x (v s) w.1 w.2)) l' (𝓝 z) →
        ∀ χ : Viewers F, ‖glance F χ (WilsonExteriorCharacterCapture.wordError F D (j s) x (v s) z y de e)‖ ≤
          fee s * ∏ i, (A i*R.family.S.a n₂^(-(de i:ℝ)-δ)+1)) := by
  obtain ⟨n₀,A,hA,ext⟩ := exterior_bounds F de cap hc δ hδ
  obtain ⟨outer,_,q,_,n₁,hn₁,_,_,train⟩ :=
    placements (C:=R.family) f (fun _ : Unit => 0) y hy 0 0 n₀
  obtain ⟨o,_,ho⟩ := small R.family.S 2 η hη 0
  obtain ⟨u,hou,hu⟩ := small R.family.S 10 (R.family.S.a o) (R.family.S.a_pos _) o
  obtain ⟨n₂,hn₂,hsize⟩ := small R.family.S ((Fintype.card E:ℝ)*6) (R.family.S.a u) (R.family.S.a_pos _) (max u n₀)
  obtain ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,ha₁,ht,fee,he,seen⟩ :=
    IntrinsicPhysicalCell.engineering F run.facilities anchor hT D v hv
  refine ⟨outer,n₁,n₂,A,hA,b,m,j,h,a,c,hb,hm,hj,hh,ha,ha₁,ht,fee,he,?_⟩
  filter_upwards [seen,hb.grows.eventually_ge_atTop q,hb.grows.eventually_ge_atTop u] with s paid hq hus
  intro x hx
  constructor
  · intro copies
    filter_upwards [train (2*copies)] with t fits
    filter_upwards [fits,paid x hx,ext n₁ ((le_max_right q n₀).trans hn₁) 1 one_pos] with w fitsW hw bank
    obtain ⟨places⟩ := fitsW
    intro e hext
    exact WilsonExteriorReplicaCapture.placed F.room.cutoff places hq _ (discrepancy_paid hw) de e (bank e hext)
  · intro screen separate e hext l' live sub z hz χ
    letI := live
    have hall : Hall R.family.S o u (b s) u n₂ 1 (Fintype.card E) := by
      refine ⟨hou,le_rfl,hus,(le_max_left ..).trans hn₂,?_,?_⟩
      · simpa only [Nat.cast_one,one_mul] using (show 2*(5*R.family.S.a u)<R.family.S.a o by linarith)
      · convert hsize using 1
        ring
    have sm : 2*R.family.S.a u < η := by linarith [R.family.S.a_pos u]
    have ht : Prepared (C:=R.family) (fun i => ⟨de i,e i⟩) f n₂
        (fun i => A i*R.family.S.a n₂^(-(de i:ℝ)-δ)+1) :=
      ⟨fun i => (ext n₂ ((le_max_right ..).trans hn₂) 1 one_pos).mono fun w hw => hw e hext i⟩
    have hoJ : o ≤ j s :=
      ((hall.first.trans hall.third).trans hx.first).trans ((Nat.le_succ _).trans hx.last)
    apply (glance_bound F χ _).trans
    exact WilsonExteriorCharacterCapture.ground F run.facilities.toServices (v s) de e y hoJ screen
      (fun i k dif => sm.trans (apart i k dif)) (fun i k => ho.trans (away i k))
      separate hall sub hz ((paid x hx).filter_mono sub) ht

end YM.Integration.WilsonPhysicalOriginalReplicaAndCharacter
