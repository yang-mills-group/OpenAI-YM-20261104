import YM.Integration.WilsonMacroscopicDerivativePrice

/-! Uniform inner-position changes of a true measured full correlation at
arbitrary separated macroscopic spectators on the original existence
experiment. All spectators keep their actual physical positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicDisplacement
open Function Filter Finset Set Metric MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}
  {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
  (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
  (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
  (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J : ℝ → PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d)
  {n : ℕ} (d : Caps n) {E : Type} [Fintype E] {e : E→ℕ} (w : Labels V e)
  {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) {δ : ℝ} (hδ : 0<δ)
  {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g)

include hk sep hδ in
theorem joined : ∀ᶠ r in RG17.home,∀ x∈K,∀ y : E→E4,ClearOf 0 y δ → Injective (beside (RG17.posed r x) y) := by
  obtain ⟨a,t,ha,ht,room⟩ := RG17.roomCosts hk sep
  have a1 : 0<a+1 := by linarith only [ha]
  have tiny : ∀ᶠ r in RG17.home,r<δ/(a+1) := nhdsWithin_le_nhds (gt_mem_nhds (div_pos hδ a1))
  filter_upwards [tiny,RG17.positiveLength] with r small rp x hx y clear
  have hM := room r rp x hx
  refine beside_distinct.mpr ⟨Work.A05.smul_conf rp (sep hx),?_,?_⟩
  · intro i j eq;by_contra ne
    have tooClose := clear.spread i j ne
    rw [eq,sub_self,norm_zero] at tooClose;exact (not_le_of_gt hδ) tooClose
  · intro i j eq
    have a' : ‖RG17.posed r x i‖≤a*r := by simpa only [sub_zero] using hM.span i
    have e' : δ≤‖y j‖ := by simpa only [zero_sub,norm_neg] using clear.openSpace j
    rw [eq] at a'
    have tiny' := (lt_div_iff₀ a1).mp small
    nlinarith only [a',e',tiny',rp]

include hG W source pace hB Q fac leading paid hk sep hδ hg
theorem gradient : ∃ M : ℝ,0≤M ∧ ∀ᶠ r in RG17.home,∀ x∈K,∀ y : E→E4,ClearOf 0 y δ →
    ∀ t : Viewers F,∀ v : (i:Fin n)→Free R.family (d i),
      let read (z : Points n) := whole (spectator F t) (RG17.posed r z) (fun i=>J r (d i) (v i)) y w
      let ext := upon (spectator F t) 0 0 y w (V.unit 0)
      DifferentiableAt ℝ read x ∧ ‖fderiv ℝ read x‖ ≤ M*(1+‖ext‖)*(∏ i,‖v i‖) := by
  let I := Fin n × Axis
  have atAxis (j : I) := WilsonMacroscopicDerivativePrice.axis hG W source pace hB F fac Q J leading paid d j.1 j.2 w hk sep hδ hg
  choose c h₀ check using atAxis
  refine ⟨∑ j : I,c j,sum_nonneg (fun j _=>h₀ j),?_⟩
  filter_upwards [eventually_all.mpr check,joined hk sep hδ (E:=E)] with r slopes joins x hx y clear t v
  let ins (j : Fin n) := J r (d j) (v j)
  let ext := upon (spectator F t) 0 0 y w (V.unit 0)
  let bill := (1+‖ext‖)*(∏ j,‖v j‖)
  let read (s : Points n) := whole (spectator F t) (RG17.posed r s) ins y w
  have safe := joins x hx y clear
  have sm := WilsonMacroscopicRelativeGradient.smooth F t (fun j=> (⟨d j,ins j⟩ : V.Tag)) (fun j=> (⟨e j,w j⟩ : V.Tag)) r y safe
  refine ⟨sm,?_⟩
  change ‖fderiv ℝ read x‖≤(∑ j : I,c j)*(1+‖ext‖)*(∏ j,‖v j‖)
  calc
    _ ≤ ∑ j : I, ‖Points.gradient j.1 j.2 read x‖ := Work.B10.norm_le_direction_sum _
    _ ≤ ∑ j : I, c j*bill := sum_le_sum fun j _=>(slopes j x hx y clear safe t v).trans_eq (mul_assoc ..)
    _ = _ := (sum_mul ..).symm.trans (mul_assoc ..).symm

theorem original : ∃ M a : ℝ,0≤M ∧ 0<a ∧ ∀ᶠ r in RG17.home,∀ x∈K,
    ∀ x' : Points n,‖x'-x‖≤a → ∀ y : E→E4,ClearOf 0 y δ →
    ∀ t : Viewers F,∀ v : (i:Fin n)→Free R.family (d i),
      let read (z : Points n) := whole (spectator F t) (RG17.posed r z) (fun i=>J r (d i) (v i)) y w
      let ext := upon (spectator F t) 0 0 y w (V.unit 0)
      ‖read x'-read x‖ ≤ M*(1+‖ext‖)*(∏ i,‖v i‖)*‖x'-x‖ := by
  obtain ⟨a,ha,domain⟩ := hk.exists_cthickening_subset_open (conf_open n) sep
  obtain ⟨M,hM,bought⟩ := gradient hG W source pace hB F fac Q J leading paid d w hk.cthickening domain hδ hg
  refine ⟨M,a,hM,ha,?_⟩
  filter_upwards [bought] with r atRadius x hx x' size y clear t v
  let B := closedBall x a
  have inside (z : Points n) (hz : z∈B) : z∈cthickening a K := mem_cthickening_of_dist_le z x a K hx (mem_closedBall.mp hz)
  have x0 : x∈B := mem_closedBall_self ha.le
  have x1 : x'∈B := mem_closedBall.mpr (by simpa only [dist_eq_norm] using size)
  exact (convex_closedBall x a).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz=>(atRadius z (inside z hz) y clear t v).1) (fun z hz=>(atRadius z (inside z hz) y clear t v).2) x0 x1

end YM.Integration.WilsonMacroscopicDisplacement
