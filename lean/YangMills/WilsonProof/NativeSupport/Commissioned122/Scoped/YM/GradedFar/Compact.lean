import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Continuity

/-!
# Extend to any T ≥ T₀ with compact clearance
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Filter Function Set Scale O O.Enh O.Score O.Read O.Canon PowerSeries
open XSpace XSpace.Normalize Register MS.Land Dframe
open scoped Topology Classical BigOperators

variable {G : Gauge} {n m h p H : ℕ}
    {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : Covered d H) (he : Covered e H)
    {V : Arenas G} {ψ : ℝ → PowerSeries ℂ} {B : ℝ → Frames G} (phys : Canon.Physical V ψ B)
    {K : Set (Points n)} {S : Set (Points m)}
    (kc : IsCompact K) (hk : K ⊆ conf n) (sc : IsCompact S) (hs : S ⊆ Outside m)
    {T₀ : ℝ} (t0 : 1 ≤ T₀)

/-- Compact polydisc in the same coordinates as `FieldBudget`. -/
abbrev Block (G : Gauge) (d : Fin n → ℕ) (R : ℝ) :=
  Metric.closedBall (0 : (i : Fin n) → Account G (d i)) R
noncomputable def credit {D : ℝ} (x : Block G d D) : Appointed122Fields G d :=
  fun i => (account G (d i)).symm (x.val i)
noncomputable def ticket {D : ℝ} (hD : 0 ≤ D) (x : Appointed122Fields G d) (hv : FieldBudget x D) : ↥(Block G d D) :=
  ⟨fun i => account G (d i) (x i), by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hD]; exact (fieldBudget_iff x hD).mp hv⟩
lemma ticket_credit {D : ℝ} (hD : 0 ≤ D) (x : Appointed122Fields G d) (hv : FieldBudget x D) :
    credit (ticket hD x hv) = x := funext fun i => (account G (d i)).symm_apply_apply _

/-- It suffices to specify any sufficiently large clearance cut on the shapes alone (independent
of perturbative order), even if before the threshold where our power-log argument applies.
The project uses `Outside` separately; outgoing automatic then. -/
abbrev Clear (K : Set (Points n)) (S : Set (Points m)) (T₀ : ℝ) :=
  ∀ T ≥ T₀, ∀ x ∈ K, ∀ y ∈ S, forest x (T • y) ∈ conf _

lemma outgoing_t {T : ℝ} (ht : 0 < T) {y : Points m} (hy : y ∈ Outside m) :
    outgoing (T • y) ∈ conf _ := by rw [← squeeze_log ht]; exact lives _ hy

include kc hk sc hs
lemma clear_after (k : ℝ) : ∃ T ≥ k, Clear K S T := by
  obtain ⟨U,HU⟩ := eventually_atTop.mp (configurations kc hk sc hs)
  exact ⟨max k U, le_max_left .., fun t ht _ hx _ hy => (HU t ((le_max_right ..).trans ht) _ hx _ hy).1⟩

include t0 phys in
lemma compact_residual (r p : ℕ) (lh : r ≤ H) {R L T : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hT : Clear K S T₀) : ∃ C : ℝ, 0 < C ∧
    ∀ t ∈ Icc T₀ T, ∀ x ∈ K, ∀ y ∈ S, ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e,
    FieldBudget u R → FieldBudget v L → ∀ z : ℂ, ‖z‖ ≤ 1 →
    ‖jointY V B hd he u v p z t x y - jointD V B he u v p lh z t x y‖ ≤ C*(t^(r+1))⁻¹ := by
  let I := (↥(Icc T₀ T) × (Profiles K S)) × (↥(Block G d R) × ↥(Block G e L)) ×
    ↥(Metric.closedBall (0:ℂ) 1)
  let x := fun i : I => i.1.2.1.val
  let y := fun i : I => i.1.2.2.val
  let t := fun i : I => i.1.1.val
  let u := fun i : I => credit i.2.1.1
  let v := fun i : I => credit i.2.1.2
  let z := fun i : I => i.2.2.val
  have tt := zero_lt_one.trans_le t0
  have h₀ (i : I) := i.1.1.property.1
  have cx : Continuous x := by unfold x; fun_prop
  have cy : Continuous y := by unfold y; fun_prop
  have cz : Continuous z := by unfold z; fun_prop
  have ct : Continuous t := by unfold t; fun_prop
  have cu j : Continuous fun i => account G (d j) (u i j) := by
    simp only [u, credit,LinearEquiv.apply_symm_apply]; exact (continuous_apply j).comp (by fun_prop : Continuous (fun i : I => i.2.1.1.val))
  have cv j : Continuous fun i => account G (e j) (v i j) := by
    simp only [v, credit,LinearEquiv.apply_symm_apply]; exact (continuous_apply j).comp (by fun_prop : Continuous (fun i : I => i.2.1.2.val))
  obtain ⟨A,D⟩ := joint_cont phys hd he cx cy ct (fun i => tt.trans_le (h₀ i)) (fun i => hk i.1.2.1.property) u v p lh cz
    (fun i => ⟨hT _ (h₀ i) _ i.1.2.1.property _ i.1.2.2.property, outgoing_t (tt.trans_le (h₀ i)) (hs i.1.2.2.property)⟩) cu cv
  letI := isCompact_iff_compactSpace.mp kc; letI := isCompact_iff_compactSpace.mp sc
  -- take sup of weighted error
  have Y := A.sub D; obtain ⟨C,hC⟩ := (isCompact_univ (X:=I)).exists_bound_of_continuousOn
    (Y.norm.mul (ct.pow (r+1))).continuousOn
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one,?_⟩; intro t' ht x' hx y' hy u' v' hv hw w W
  let h₁ := ticket hR u' hv; let h₂ := ticket hL v' hw
  have h := hC (((⟨t',ht⟩, (⟨x',hx⟩, ⟨y',hy⟩)),(h₁,h₂),⟨w, by simpa using W⟩) : I) trivial
  rw [← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos (tt.trans_le ht.1) _)).mpr
  apply le_trans _ (h.trans (le_max_right ..)); simp [x,y,u,v,z,t,h₁,h₂, ticket_credit, Real.norm_eq_abs, abs_of_pos (tt.trans_le ht.1)]

include t0 in
lemma full_le_from_clear (lh : h ≤ H) (p : ℕ) {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (clear : Clear K S T₀) (N : WilsonPrescription G)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {Sms : MS.Land.Prescription (Press.portDeck G)} (ν : ℝ) {hG : G.Simple} (mh : Main.Match N hG M Sms true) :
    let V := Scale.Measure.outlook N.scheme N.criterion
    let B := GroupS.gaugeN N.scheme N.criterion M ν
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ T ≥ T₀, ∀ x ∈ K, ∀ y ∈ S,
    ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e, FieldBudget u R → FieldBudget v L → ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖jointY V B hd he u v p z T x y - jointD V B he u v p lh z T x y‖ ≤
        C*((T^(h+1))⁻¹+‖z‖^(p+1))*(1+Real.log T)^a := by
  intro V B
  obtain ⟨C,hC,a,f⟩ := formal_match kc hk sc hs hd he N ν mh h p lh R L
  obtain ⟨U,hU⟩ := eventually_atTop.mp f
  obtain ⟨D,hD,hcomp⟩ := compact_residual hd he (mh.separatedOPE ν).wilson kc hk sc hs t0 h p lh hR hL
    (T:=max T₀ U) clear
  refine ⟨max C D, lt_max_of_lt_left hC, a,?_⟩; intro T ht x hx y hy u v hu hv z hz
  have hg : 1 ≤ T := t0.trans ht
  have h1 : 1 ≤ 1+Real.log T := le_add_of_nonneg_right (Real.log_nonneg hg)
  have hp : 0 < T := zero_lt_one.trans_le hg
  rcases le_total U T with hw|hw
  · apply le_trans ((hU T hw x hx y hy).2.2 u v hu hv z hz); gcongr; apply le_max_left
  apply le_trans (hcomp _ ⟨ht,hw.trans (le_max_right ..)⟩ x hx y hy u v hu hv z hz)
  calc
    _ ≤ max C D*((T^(h+1))⁻¹+‖z‖^(p+1)) := by
      gcongr <;> simp
    _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ h1)
end YM.FVA2.GradedFar
