import YM.Integration.WilsonCapturedRetainedProjection
import YM.RG12.Canonical.Low

/-! In the horizon-zero scalar channel the physical fitted transfer is
the identity on every opened date. A single paid capture therefore prices
the omitted stable feed in actual scalar units. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFeed

open Function Filter Finset Real Lattice RG Wilson Labels Source Work.G08
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal RG12 Bid
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "F" => R.family.labels.level 0

private theorem core_unit (m : ℕ) : (R.family.labels.level 0).core (unitVec F R.family.path m) = 0 := by
  funext i
  by_cases hi : i=0 <;> simp [Labels.Frame.core,unitVec,Labels.Frame.e0,Function.update,hi]

private theorem unit_fitting {N p i : ℕ} (op : Opened R.family 0 i p) (live : i≤N) :
    fitting (C:=R.family) 0 N p i R.makes op live (unitVec F R.family.path N) = unitVec F R.family.path i := by
  let T := R.family.factory 0 N p
  let q := T.entries i (unitVec F R.family.path N)
  have H := R.makes.calibrated 0 N p (op.post.trans live)
  have hx : q.x = unitVec F R.family.path i := H.unit_coord _ op.post live
  have cap := H.cap i op.post live (unitVec F R.family.path N)
  change q.remBound _ _ _ (_ * (R.family.labels.level 0).coeffSize ((R.family.labels.level 0).core q.x)) at cap
  rw [hx,core_unit,show (R.family.labels.level 0).coeffSize 0=0 by simp [Labels.Frame.coeffSize],mul_zero] at cap
  have price : reads (C:=R.family) 0 N p i q 0 := ⟨H.format i op.post live _,cap⟩
  have diff := measured_diff 0 N p i R.makes op.post live price
  rw [mul_zero] at diff
  have each (j : (R.family.labels.level 0).Index) : ‖(page (C:=R.family) 0 p i q - q.x) j‖ ≤
      (R.family.labels.level 0).coeffSize (page (C:=R.family) 0 p i q - q.x) :=
    Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)
  change page (C:=R.family) 0 p i q = _
  rw [← hx]
  apply sub_eq_zero.mp
  funext j
  exact norm_eq_zero.mp (le_antisymm ((each j).trans diff) (norm_nonneg _))

include simple in
/-- The actual original unmarked filing matrix acts identically on this scalar,
including its measured threshold reset and all finite-volume page corrections. -/
theorem transfer {N p i : ℕ} (op : Opened R.family 0 i p) (live : i≤N)
    (x : R.family.label 0) : fitting (C:=R.family) 0 N p i R.makes op live x = x := by
  obtain ⟨z,hz⟩ := RG12.unit_spans simple R.family 0 N (by decide) x
  rw [hz,map_smul,unit_fitting R op live]
  simp [unitVec]

include simple in
theorem scalar_cost {N p i : ℕ} (op : Opened R.family 0 i p) (live : i≤N)
    (x : R.family.label 0) : mCost R.family 0 N p i x = ‖x 0‖ := by
  change (R.family.labels.level 0).coeffSize (fitting (C:=R.family) 0 N p i R.makes op live x) = _
  rw [transfer R simple op live x]
  obtain ⟨z,hz⟩ := RG12.unit_spans simple R.family 0 N (by decide) x
  rw [hz]
  have h := RG12.mass_unit (C:=R.family) 0 N z
  simpa [RG12.mass,unitVec,Labels.Frame.e0] using h

include simple in
/-- For any single paid original capture, its two physical filed scalars include
the entire earlier stable feed. Its omitted older part is bounded at a moving
cut within the interval by twice the original capture rent. -/
theorem truncated {N p t i b : ℕ} (ot : Opened R.family 0 t p) (oi : Opened R.family 0 i p)
    (ti : t ≤ i) (ib : i ≤ b) (bN : b < N) (Y : Cut R.family N p) (B : R.family.label 0) {a : ℝ}
    (whole : WholeProductCapture.Retained R.family N b p 0 t R.makes ot (ti.trans ib) bN Y B a) :
    gainChart R.family.path b i * ‖(topReport R.family N p 0 R.makes i oi (ib.trans bN.le) Y) 0 -
      (topReport R.family N p 0 R.makes t ot ((ti.trans ib).trans bN.le) Y) 0‖ ≤ 2*a := by
  let A := topReport R.family N p 0 R.makes i oi (ib.trans bN.le) Y
  let T := topReport R.family N p 0 R.makes t ot ((ti.trans ib).trans bN.le) Y
  let X := (R.family.factory 0 N p).terminal.symm B
  have hi := WilsonCapturedRetainedProjection.measured R 0 ot (ti.trans ib) bN ti ib oi Y B a whole
  have ht := WilsonCapturedRetainedProjection.measured R 0 ot (ti.trans ib) bN le_rfl (ti.trans ib) ot Y B a whole
  rw [scalar_cost R simple oi (ib.trans bN.le),Pi.sub_apply] at hi
  rw [scalar_cost R simple ot ((ti.trans ib).trans bN.le),Pi.sub_apply] at ht
  change gainChart R.family.path b i * ‖A 0-X 0‖ ≤ a at hi
  change gainChart R.family.path b t * ‖T 0-X 0‖ ≤ a at ht
  have monotone : gainChart R.family.path b i ≤ gainChart R.family.path b t := by
    apply exp_le_exp.mpr
    have sc : Monotone R.family.S.scale := monotone_nat_of_le_succ fun j => by
      rw [Schedule.scale_succ]
      exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (R.family.S.block j).pos))
    have h := sc ti
    linarith
  have hnext := (mul_le_mul_of_nonneg_right monotone (norm_nonneg (T 0-X 0))).trans ht
  have tri : ‖A 0-T 0‖ ≤ ‖A 0-X 0‖+‖T 0-X 0‖ := by
    simpa only [dist_eq_norm,norm_sub_rev (X 0) (T 0)] using dist_triangle (A 0) (X 0) (T 0)
  calc
    _ ≤ gainChart R.family.path b i * (‖A 0-X 0‖+‖T 0-X 0‖) :=
      mul_le_mul_of_nonneg_left tri (exp_pos _).le
    _ ≤ 2*a := by rw [mul_add]; linarith

include simple in
/-- The terminal relabeling in the continuum filing fixes all unit coordinates. -/
theorem terminal {N p : ℕ} (live : R.family.ref 0≤N) (x : R.family.label 0) :
    (R.family.factory 0 N p).terminal x = x := by
  let T := R.family.factory 0 N p
  have H := R.makes.calibrated 0 N p live
  have unit : unitVec F R.family.path (R.family.ref 0) = T.terminal (unitVec F R.family.path N) :=
    (H.unit_coord _ le_rfl live).symm.trans (H.reads _)
  obtain ⟨z,hz⟩ := RG12.unit_spans simple R.family 0 N (by decide) x
  change T.terminal x=x
  rw [hz,map_smul,←unit]
  simp [unitVec]

/-- Full scalar report at a live date for this one Wilson source. -/
def report {N p : ℕ} (Y : Cut R.family N p) (j : ℕ) : ℂ :=
  if h : Opened R.family 0 j p ∧ j≤N then
    ((R.family.factory 0 N p).terminal (topReport R.family N p 0 R.makes j h.1 h.2 Y)) 0 else 0

include simple in
private theorem at_date {N p j : ℕ} (Y : Cut R.family N p) (oj : Opened R.family 0 j p)
    (live : j≤N) : report R Y j = (topReport R.family N p 0 R.makes j oj live Y) 0 := by
  simp only [report,dif_pos (And.intro oj live),terminal R simple (oj.post.trans live)]

include simple in
/-- Every signed feed in the short ledger can be computed on the actual
retained Wilson rows. Their densities evolve by the true linearized physical
push on the original quiet vacuum. The terminal scalar cancels between dates. -/
theorem stored {N p t b : ℕ} (admit : ∀j ≥ t, Opened R.family 0 j p)
    (tb : t≤b) (bN : b < N) (Y : Cut R.family N p) (B : R.family.label 0) {a : ℝ}
    (whole : WholeProductCapture.Retained R.family N b p 0 t R.makes (admit t le_rfl) tb bN Y B a) :
    ∃ (q : ∀j,store R.family 0 p j) (v : ℕ→ℝ),
      (q t).x=0 ∧
      (∀j ≥ t, j < b → value (C:=R.family) 0 N p j (q j) =
        transition (C:=R.family) 0 N p j (value (C:=R.family) 0 N p (j+1) (q (j+1)))) ∧
      ∀j ≥ t, ∀ jb : j≤b,
        reads (C:=R.family) 0 N p j (q j) (v j) ∧
        credit R.family N p 0 Y j (jb.trans bN.le) = value (C:=R.family) 0 N p j (q j) +
           calValues (C:=R.family) 0 N p j B ∧
        report R Y j = B 0 + (page (C:=R.family) 0 p j (q j)) 0 ∧
        gainChart R.family.path b j*(v j+(R.family.labels.level 0).coeffSize (q j).x) ≤ a := by
  obtain ⟨q,v,zero,step,row,_⟩ := whole
  refine ⟨q,v,zero,step,?_⟩
  intro j tj jb
  let oj := admit j tj
  let live := jb.trans bN.le
  let Z := (R.family.factory 0 N p).terminal.symm B
  have idZ : Z=B := (terminal R simple (oj.post.trans live) Z).symm.trans
    ((R.family.factory 0 N p).terminal.apply_symm_apply B)
  obtain ⟨paid,held,_,cash⟩ := row j tj jb
  have read := (WholeCaptureTransport.read_signed R.family N p 0 R.makes oj live Z paid held).2.1
  change fitting (C:=R.family) 0 N p j R.makes oj live
    (topReport R.family N p 0 R.makes j oj live Y-Z) = page (C:=R.family) 0 p j (q j) at read
  rw [transfer R simple oj live,idZ] at read
  have e := congrArg (fun x : R.family.label 0 => x 0) read
  simp only [Pi.sub_apply] at e
  refine ⟨paid,?_,?_,cash⟩
  · change credit R.family N p 0 Y j live = value (C:=R.family) 0 N p j (q j) +
      calValues (C:=R.family) 0 N p j Z at held
    simpa only [idZ] using held
  · rw [at_date R simple Y oj live]
    exact (sub_eq_iff_eq_add.mp e).trans (add_comm _ _)

include simple in
/-- Keep the source's actual signed early feeds from capture down to the
logarithmic cut. A coupling-polynomial capture bill then leaves at most twice
the requested perturbative power from every still older date, uniformly in N. -/
theorem chronological {N p t i b : ℕ} (admit : ∀j ≥ t, Opened R.family 0 j p)
    (ti : t ≤ i) (ib : i ≤ b) (bN : b < N) (Y : Cut R.family N p)
    (B : R.family.label 0) {a g : ℝ} (hg : 0<g) (K P : ℕ)
    (whole : WholeProductCapture.Retained R.family N b p 0 t R.makes (admit t le_rfl)
      (ti.trans ib) bN Y B a)
    (paid : a≤(g⁻¹)^K)
    (span : 8*((P:ℝ)+K)*log (g⁻¹) ≤ R.family.S.scale b-R.family.S.scale i) :
    ‖report R Y t - (report R Y b+∑j ∈ Finset.Ico i b, (report R Y j-report R Y (j+1)))‖ ≤ 2*g^P := by
  let f := report R Y
  have step : (∑j ∈ Finset.Ico i b, (f j-f (j+1))) = f i-f b := by
    rw [Finset.sum_Ico_eq_sub _ ib]
    simp_rw [show (fun j : ℕ => f j-f (j+1)) = (fun j => -(f (j+1)-f j)) by funext j; abel,
      Finset.sum_neg_distrib,Finset.sum_range_sub]
    abel
  change ‖f t-(f b+∑j ∈ Finset.Ico i b,(f j-f (j+1)))‖ ≤ _
  rw [step,show f b+(f i-f b) = f i by abel,norm_sub_rev]
  have bill := truncated R simple (admit t le_rfl) (admit i ti) ti ib bN Y B whole
  rw [← at_date R simple Y (admit t le_rfl) ((ti.trans ib).trans bN.le),
    ← at_date R simple Y (admit i ti) (ib.trans bN.le)] at bill
  have prod : (g⁻¹)^K ≤ gainChart R.family.path b i*g^P := by
    calc
      _ = exp ((K:ℝ)*log (g⁻¹)) := by rw [Real.exp_nat_mul,Real.exp_log (inv_pos.mpr hg)]
      _ ≤ exp ((1/8:ℝ)*(R.family.S.scale b-R.family.S.scale i)+(P:ℝ)*log g) := by
        apply exp_le_exp.mpr
        rw [Real.log_inv] at span ⊢
        linarith
      _ = _ := by rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log hg]; rfl
  apply (le_of_mul_le_mul_left _ (exp_pos ((1/8:ℝ)*(R.family.S.scale b-R.family.S.scale i))))
  change gainChart R.family.path b i*‖f i-f t‖ ≤ gainChart R.family.path b i*(2*g^P)
  calc
    _ ≤ 2*a := bill
    _ ≤ 2*(gainChart R.family.path b i*g^P) := mul_le_mul_of_nonneg_left (paid.trans prod) (by norm_num)
    _ = _ := by ring

end YM.Integration.WilsonThermometerUnitFilingFeed
