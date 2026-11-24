import YM.Integration.WilsonHeldPriorCovariance
import YM.Integration.WilsonMacroscopicRichFlatKernel

/-! Resampling the local incoming links on the actual Wilson posterior at
a fixed lower field. The unaltered exterior is integrated with that same
posterior before forming any connected combination. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldExteriorLaw

open Function Set MeasureTheory Lattice RG Wilson
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical

section fibers

/- The coordinate splitting and Haar Fubini identities below use the finite
product measures in SelectedCofactorChamberMarginal. They depend only on the
current Wilson groups and their Haar measure. -/
variable {G : Gauge} {n : Side}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def links (X : Set (Site n)) : Set (Edge (Site n)) := {e | e.1 ∈ X ∧ e.1 + step e.2 ∈ X}

abbrev Fields (G : Gauge) (A : Set (Edge (Site n))) := A → G.El

def sheet (G : Gauge) (A : Set (Edge (Site n))) : Measure (Fields G A) := Measure.pi fun _ => G.probHaar

instance (A : Set (Edge (Site n))) : IsProbabilityMeasure (sheet G A) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : A => G.probHaar))

instance (A : Set (Edge (Site n))) : IsFiniteMeasure (sheet G A) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : A => G.probHaar))

instance (A : Set (Edge (Site n))) : SFinite (sheet G A) :=
  inferInstanceAs (SFinite (Measure.pi fun _ : A => G.probHaar))

def cut (G : Gauge) (A : Set (Edge (Site n))) : Config G n ≃ᵐ Fields G A × Fields G Aᶜ :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge (Site n) => G.El) (· ∈ A)

/-- Vary precisely the links outside A while keeping its entire assignment. -/
def patch_links (G : Gauge) (A : Set (Edge (Site n))) (U : Config G n) (v : Fields G Aᶜ) :
    Config G n := (cut G A).symm (((cut G A) U).1,v)

theorem fixed (A : Set (Edge (Site n))) (U : Config G n) (v : Fields G Aᶜ)
    (e : Edge (Site n)) (he : e∈A) : patch_links G A U v e = U e := by
  have kept := congrArg Prod.fst ((cut G A).apply_symm_apply (((cut G A) U).1,v))
  exact congrFun kept (⟨e,he⟩ : A)

theorem measurable_patch (A : Set (Edge (Site n))) (U : Config G n) : Measurable (patch_links G A U) :=
  (cut G A).symm.measurable.comp (measurable_const.prodMk measurable_id)

private theorem cut_preserves (A : Set (Edge (Site n))) :
    MeasurePreserving (cut G A) (prior G n) ((sheet G A).prod (sheet G Aᶜ)) := by
  convert! measurePreserving_piEquivPiSubtypeProd (α := fun _ : Edge (Site n) => G.El)
    (fun _ => G.probHaar) (· ∈ A) using 1
  unfold sheet
  congr
  apply Subsingleton.elim

def marginal (A : Set (Edge (Site n))) (f : Config G n → E) (u : Fields G A) : E :=
  ∫ y, f ((cut G A).symm (u,y)) ∂sheet G Aᶜ

private theorem marginal_env (A : Set (Edge (Site n))) {f : Config G n → E} (hf : Envelope f) :
    Envelope (marginal A f) := by
  have hm : StronglyMeasurable (fun z : Fields G A × Fields G Aᶜ => f ((cut G A).symm z)) :=
    (hf.meas.comp (cut G A).symm.measurable).stronglyMeasurable
  obtain ⟨c,hc⟩ := hf.cost
  refine ⟨hm.integral_prod_right'.measurable,c,fun u => ?_⟩
  simpa only [marginal,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := sheet G Aᶜ) (C := c) (ae_of_all _ fun y => hc ((cut G A).symm (u,y)))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
private theorem total (A : Set (Edge (Site n))) {f : Config G n → E} (hf : Integrable f (prior G n)) :
    ∫ u, marginal A f u ∂sheet G A = ∫ U, f U ∂prior G n := by
  have h := cut_preserves (G := G) A
  have hi := (h.symm.integrable_comp_emb (cut G A).symm.measurableEmbedding).2 hf
  exact (integral_prod (fun z => f ((cut G A).symm z)) hi).symm.trans (h.symm.integral_comp' f)

private theorem marginal_lower (A : Set (Edge (Site n))) {P : Config G n → ℝ} (hp : Envelope P) {a : ℝ}
    (ha : ∀ U, a ≤ P U) (u : Fields G A) : a ≤ marginal A P u := by
  have henv : Envelope (fun y : Fields G Aᶜ => P ((cut G A).symm (u,y))) :=
    ⟨hp.meas.comp ((cut G A).symm.measurable.comp (measurable_const.prodMk measurable_id)),
      hp.cost.imp fun c h y => h ((cut G A).symm (u,y))⟩
  simpa only [marginal,integral_const,probReal_univ,one_smul] using
    integral_mono (μ := sheet G Aᶜ) (integrable_const a) (henv.integrable _) (fun y => ha ((cut G A).symm (u,y)))

/-- Integrating all exterior links gives the denominator and signed numerator
on the identical retained configuration. -/
def projected (A : Set (Edge (Site n))) (P : Config G n → ℝ) (f : Config G n → E) (U : Config G n) : E :=
  let u := ((cut G A) U).1
  (marginal A P u)⁻¹ • marginal A f u

private theorem projected_env (A : Set (Edge (Site n))) {P : Config G n → ℝ} {f : Config G n → E}
    (hp : Envelope P) (hf : Envelope f) {a : ℝ} (ha : 0 < a) (hl : ∀ U, a ≤ P U) :
    Envelope (projected A P f) := by
  have hP := marginal_env A hp
  have hF := marginal_env A hf
  have hm := measurable_fst.comp (cut G A).measurable
  obtain ⟨c,hc⟩ := hF.cost
  refine ⟨(hP.meas.inv.comp hm).smul (hF.meas.comp hm),a⁻¹*c,fun U => ?_⟩
  let u := ((cut G A) U).1
  have hlow := marginal_lower A hp hl u
  have hpos := ha.trans_le hlow
  change ‖(marginal A P u)⁻¹ • marginal A f u‖ ≤ _
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact mul_le_mul (inv_anti₀ ha hlow) (hc u) (norm_nonneg _) (inv_nonneg.mpr ha.le)

private theorem pairing [CompleteSpace E] (A : Set (Edge (Site n))) {P : Config G n → ℝ} {f : Config G n → E}
    (hp : Envelope P) (hf : Envelope f) {a : ℝ} (ha : 0 < a) (hl : ∀ U, a ≤ P U) :
    (∫ U, P U • projected A P f U ∂prior G n) = ∫ U, f U ∂prior G n := by
  have hproj := projected_env A hp hf ha hl
  obtain ⟨c,hc⟩ := hp.cost
  obtain ⟨d,hd⟩ := hproj.cost
  have hE : Envelope (fun U => P U • projected A P f U) :=
    ⟨hp.meas.smul hproj.meas,c*d,fun U => (norm_smul_le ..).trans
      (mul_le_mul (hc U) (hd U) (norm_nonneg _) ((norm_nonneg _).trans (hc U)))⟩
  letI : IsFiniteMeasure (prior G n) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site n) => G.probHaar)))
  have hint {g : Config G n → E} (hg : Envelope g) : Integrable g (prior G n) :=
    (integrable_const (μ := prior G n) hg.cost.choose).mono' hg.meas.aestronglyMeasurable (ae_of_all _ hg.cost.choose_spec)
  refine (total (G := G) A (f := fun U => P U • projected A P f U) (hint hE)).symm.trans ?_
  refine Eq.trans ?_ (total (G := G) A (f := f) (hint hf))
  apply integral_congr_ae
  apply ae_of_all
  intro u
  simp only [marginal,projected,MeasurableEquiv.apply_symm_apply]
  rw [integral_smul_const,smul_smul,mul_inv_cancel₀,one_smul]
  exact (ha.trans_le (marginal_lower A hp hl u)).ne'

end fibers

variable {G : Gauge} (R : Run G) (N per j : ℕ)
local notation "fine" => Config G (R.family.side (j+1) per)
local notation "coarse" => Config G (R.family.side j per)
local notation "up" => R.family.path.rep N per (j+1)
local notation "down" => R.family.path.rep N per j
local notation "step" => R.family.path.levels.clock.op j per
local notation "β" => R.family.path.β N per (j+1)

def exterior {n : Side} (S : Support n) : Set (Edge (Site n)) := {e | e.1 ∉ S}

def weight (V : coarse) (P : Rep G (R.family.side (j+1) per)) (U : fine) : ℝ :=
  (step).density β U V * P.eval U / (down).eval V

def link_row (saved : Set (Edge (Site (R.family.side (j+1) per)))) (V : coarse)
    (P : Rep G (R.family.side (j+1) per)) (f : fine → ℂ) : fine → ℂ :=
  let w := weight R N per j V P
  projected saved w (fun U => w U • f U)

def row (S : Support (R.family.side (j+1) per)) (V : coarse)
    (P : Rep G (R.family.side (j+1) per)) (f : fine → ℂ) : fine → ℂ :=
  link_row R N per j (exterior S) V P f

private theorem weighted {X : Type*} [MeasurableSpace X] {w : X→ℝ} {f : X→ℂ}
    (ew : Envelope w) (ef : Envelope f) : Envelope (fun U => w U • f U) := by
  obtain ⟨c,hc⟩ := ew.cost
  obtain ⟨b,hb⟩ := ef.cost
  exact ⟨ew.meas.smul ef.meas,c*b,fun U => (norm_smul_le ..).trans
    (mul_le_mul (hc U) (hb U) (norm_nonneg _) ((norm_nonneg _).trans (hc U)))⟩

private theorem kernel_env {n m : Side} (op : StepData n m) (β' : ℝ)
    (h : op.patch.Branches op.kernel G) (V : Config G n) :
    Envelope (fun U : Config G m => op.density β' U V) := by
  obtain ⟨B,hB⟩ := op.density_bound h β'
  exact ⟨Measurable.comp (op.density_meas h β') (f:=fun U : Config G m => (U,V))
    (measurable_id.prodMk measurable_const),B,fun U => by
      rw [Real.norm_of_nonneg (op.density_positive β' U V)]
      exact hB U V⟩

private theorem kernel_floor (live : j+1≤N) :
    ∃ t : ℝ,0<t ∧ ∀ (U : fine) (V : coarse), t≤(step).density β U V := by
  have H := WilsonMacroscopicRichFlatKernel.purchased R j per N live
  exact ⟨_,mul_pos H.1 (Real.exp_pos _),fun U V => (H.2 U V).1⟩

theorem regularity (live : j+1≤N) (V : coarse) (P : Rep G (R.family.side (j+1) per))
    (ep : Envelope P.eval) {c : ℝ} (hc : 0<c) (lo : ∀ U,c≤P.eval U) :
    Envelope (weight R N per j V P) ∧ ∃ a : ℝ,0<a ∧ ∀ U,a≤weight R N per j V P U := by
  let d := (down).eval V
  have den : 0<d := Multi.AxisShift.chosen_positive R.makes.wilson ((Nat.le_succ j).trans live) V
  obtain ⟨t,ht,lower⟩ := kernel_floor R N per j live
  constructor
  · have h := (kernel_env (step) β (R.family.path.levels.blocks j per).branches V).mul ep
    have ec : Envelope (fun _ : fine => d⁻¹) := Envelope.const d⁻¹
    change Envelope (fun U : fine => (step).density β U V*P.eval U/d)
    simp only [div_eq_mul_inv]
    exact h.mul ec
  · exact ⟨t*c/d,div_pos (mul_pos ht hc) den,fun U =>
      div_le_div_of_nonneg_right (mul_le_mul (lower U V) (lo U) hc.le
        ((step).density_positive β U V)) den.le⟩

theorem row_envelope (live : j+1≤N) (S : Support (R.family.side (j+1) per)) (V : coarse)
    (P : Rep G (R.family.side (j+1) per)) (ep : Envelope P.eval) {c : ℝ}
    (hc : 0<c) (lo : ∀ U,c≤P.eval U) {f : fine→ℂ} (ef : Envelope f) :
    Envelope (row R N per j S V P f) := by
  obtain ⟨ew,a,ha,hw⟩ := regularity R N per j live V P ep hc lo
  exact projected_env (exterior S) ew (weighted ew ef) ha hw

private theorem interior_floor (live : j+1<N) : ∃ a : ℝ,0<a ∧ ∀ U,a≤(up).eval U := by
  let i := j+1
  let A := R.family.path.rep N per (i+1)
  let Z := partition G (R.family.side N per) (R.family.path.β N per N)
  obtain ⟨t,ht,lower⟩ := kernel_floor R N per i live
  have hZ : 0<Z := partition_pos _
  have hI := (A.envelope (R.makes.wilson.represents N per (i+1) live).good).integrable (prior G _)
  have mass : (∫ U,A.eval U ∂prior G _)=Z := R.family.path.partition_eq R.makes.wilson N per (i+1) live
  refine ⟨t*Z,mul_pos ht hZ,fun V => ?_⟩
  change t*Z≤(R.family.path.rep N per i).eval V
  have stepId : (R.family.path.rep N per i).eval V = (R.family.path.levels.clock.op i per).push
      (R.family.path.β N per (i+1)) A.eval V := congrFun (R.makes.wilson.steps N per i live).1 V
  rw [←mass,←integral_const_mul,stepId]
  exact integral_mono (hI.const_mul t)
    (StepData.push_slice (R.family.path.levels.transition_mass ..) V _ hI)
    (fun U => mul_le_mul_of_nonneg_right (lower U V)
      (Multi.AxisShift.chosen_positive R.makes.wilson live U).le)

/-- At the ultraviolet boundary the true Wilson start has a positive minimum
on the finite compact group. At every earlier date the next actual kernel
gives the floor. Neither floor is charged to the conditional estimate. -/
theorem upper_floor (live : j+1≤N) : ∃ a : ℝ,0<a ∧ ∀ U,a≤(up).eval U := by
  rcases lt_or_eq_of_le live with advanced|edge
  · exact interior_floor R N per j advanced
  have source : (R.family.path.rep N per N).eval = bare (R.family.beta N per) := (R.makes.wilson.starts N per).2
  rw [edge,source]
  obtain ⟨x,_,least⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (Wilson.bare_cont (G:=G) (n:=R.family.side N per) (R.family.beta N per)).continuousOn
  exact ⟨_,Wilson.bare_pos _ x,fun U => least (Set.mem_univ U)⟩

/-- Recover the original posterior with exactly the prescribed links held. The
retained set may include every edge disjoint from a registered gauge block,
leaving both incoming and outgoing boundary edges on the varying side. -/
theorem registered_links (live : j+1≤N) (saved : Set (Edge (Site (R.family.side (j+1) per)))) (V : coarse)
    {f : fine→ℂ} (ef : Envelope f) :
    Envelope (link_row R N per j saved V (up) f) ∧
    actualAverage R.family (N:=N) (link_row R N per j saved V (up) f) V =
      actualAverage R.family (N:=N) f V := by
  obtain ⟨c,hc,lo⟩ := upper_floor R N per j live
  obtain ⟨ew,a,ha,hw⟩ := regularity R N per j live V (up)
    ((up).envelope (R.makes.wilson.represents N per (j+1) live).good) hc lo
  exact ⟨projected_env saved ew (weighted ew ef) ha hw,pairing saved ew (weighted ew ef) ha hw⟩

theorem physical_envelope (live : j+1≤N) (S : Support (R.family.side (j+1) per)) (V : coarse)
    {f : fine→ℂ} (ef : Envelope f) : Envelope (row R N per j S V (up) f) := by
  exact (registered_links R N per j live (exterior S) V ef).1

/-- This exterior average is exactly the original conditional. Its normalization
is the existing Wilson value at V for every finite regulator and every exterior. -/
theorem all_cutoffs (live : j+1≤N) (S : Support (R.family.side (j+1) per)) (V : coarse)
    {f : fine→ℂ} (ef : Envelope f) :
    actualAverage R.family (N:=N) (row R N per j S V (up) f) V =
      actualAverage R.family (N:=N) f V := by
  exact (registered_links R N per j live (exterior S) V ef).2

theorem restored (live : j+1<N) (S : Support (R.family.side (j+1) per)) (V : coarse)
    {f : fine→ℂ} (ef : Envelope f) :
    actualAverage R.family (N:=N) (row R N per j S V (up) f) V =
      actualAverage R.family (N:=N) f V :=
  all_cutoffs R N per j live.le S V ef

end YM.Integration.WilsonHeldExteriorLaw

