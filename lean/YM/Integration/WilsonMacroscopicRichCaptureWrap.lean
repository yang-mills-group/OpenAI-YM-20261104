import YM.Integration.WilsonMacroscopicRichMeasuredProbe
import YM.Integration.WilsonCanonicalReportingBranch

/-! Remove the wrapping ambiguity from the actual funded close capture, at any spatial rate after physical grade normalization. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCaptureWrap
open Filter Function Set Lattice Wilson RG Source OPE OPE.Orbits Spec PhysMS MergeProof
open RG16 RG16.Literal Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato RGComparison.Core16
open Labels Analysis Next.Foundations Push.Local Bid ProjectorNext.Equivariance
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G}

theorem fee (simple : G.Simple) (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (M B : ℝ) (hM : 0 < M) (hB : 20 < B) (h : ℕ) (rem : ℕ → ℝ)
    (rate : RateIs atTop C.S.scale rem (-h)) (s : ℝ) (hs : 0 ≤ s) :
    ∀ᶠ m : ℕ in atTop, ∀ p, invoice (C:=C) h (port C (8*M) B (mul_pos (by norm_num) hM) m) p * rem m ≤
      (C.S.a m)^h * Real.exp (-s*C.S.scale m) := by
  let b := port C (8*M) B (mul_pos (by norm_num) hM)
  have height := port_height C simple (8*M) B (mul_pos (by norm_num) hM) (by linarith only [hB]) pace
  have wrapping : ∀ᶠ m in atTop, ∀ p, cut (C:=C) p (b m) ≤ Real.exp ((-2*(s+2))*C.S.scale (b m)) :=
    height.1.eventually (cut_flat C simple _)
  have depth : ∀ᶠ m in atTop, (1/2:ℝ) < C.S.scale (b m) / C.S.scale m := height.2.eventually (Ioi_mem_nhds (by norm_num))
  have capital := rate.pays C.S.divergent (1-h) (by linarith)
  let P := price (C:=C) h
  have limiting := (Real.tendsto_exp_atTop.comp C.S.divergent).eventually_ge_atTop P
  filter_upwards [wrapping,depth,capital,limiting,rate.pos,C.S.divergent.eventually_gt_atTop 0] with m wrap deep money fixed rp mp
  intro p
  let t := C.S.scale m
  have half : (1/2:ℝ) * t ≤ C.S.scale (b m) := (le_div_iff₀ mp).mp deep.le
  have folded : cut (C:=C) p (b m) ≤ Real.exp (-(s+2)*t) := by
    apply (wrap p).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [mul_le_mul_of_nonneg_left half (show 0 ≤ 2*(s+2) by positivity)]
  have mfee : rem m ≤ Real.exp ((1-h)*t) := (le_abs_self _).trans money
  have eng : (C.S.a m)^h = Real.exp (-(h:ℝ)*t) := by
    have unit : C.S.a m = Real.exp (-t) := by simp [t,Schedule.scale,Real.log_inv,Real.exp_log (C.S.a_pos m)]
    rw [unit,← Real.exp_nat_mul]; congr 1; ring
  change P * cut (C:=C) p (b m) * rem m ≤ _
  calc P * cut (C:=C) p (b m) * rem m ≤ (Real.exp t * Real.exp (-(s+2)*t)) * Real.exp ((1-h)*t) :=
        mul_le_mul (mul_le_mul fixed folded (Real.exp_pos _).le (Real.exp_pos _).le) mfee rp.le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
       _ = (C.S.a m)^h * Real.exp (-s*t) := by rw [eng]; simp only [←Real.exp_add]; congr 1; ring

/-- The numerical fixed-curvature comparison and spatial rate apply to the same enrolled cap store. -/
theorem measured (R : Run G) {b N p : ℕ} (T : Slices R.family.path.levels p) (live : b < N) (h : ℕ)
    (Y : Config G (R.family.side N p) → ℂ) (ct : Continuous Y) (gi : GaugeInvariant Y)
    (door : Opened R.family h b p) (q : store R.family h p b) (r : ℝ)
    (read : reads h N p b q r) (joins : credit R.family N p h Y b live.le = value (C:=R.family) h N p b q) :
    (R.family.labels.level h).coeffSize (readPage R.family N p h Y b live.le - q.x) ≤ invoice (C:=R.family) h b p * r ∧
      ∀ t : Probe G h, runProbe (R.family.labels.level h) t (readPage R.family N p h Y b live.le) =
        Germ.jet R.family.params t (R.family.path.rep N p b).p.threshold 0 (WilsonMacroscopicRichReportedPosterior.observation R T live.le h Y) := by
  have settled : Booked R.family N p h Y b live.le := ⟨q,r,read,joins⟩
  refine ⟨?_,?_⟩
  · rw [readPage_eq R.family N p h Y R.makes live.le door.post q read joins]
    exact measured_diff h N p b R.makes door.post live.le read
  intro t
  have close := WilsonMacroscopicRichMeasuredProbe.measured R T live h Y ct gi door settled t
  exact (congrArg (runProbe (R.family.labels.level h) t) ((fitting h N p b R.makes door live.le).apply_symm_apply _).symm).trans close

end YM.Integration.WilsonMacroscopicRichCaptureWrap
