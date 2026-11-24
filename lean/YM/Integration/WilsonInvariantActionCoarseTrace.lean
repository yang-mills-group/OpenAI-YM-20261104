import YM.Integration.WilsonInvariantActionIntegratedPair
import YM.Integration.WilsonInheritedRegisteredField

/-! The central action can be priced on its actual earlier registered field.
The original physical trace pays its fourth engineering power on a near-mesh
clock. The full inherited density and its genuine vacuum stay in the price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCoarseTrace
open Filter Function Set MeasureTheory Lattice RG Wilson Source Push.Local MergeProof
open Table Spec Climb Maxwell Maxwell.Free Spin PhysMS Trace.Pilot TraceExtension
open PhysicalNext.Repeat.Legato Extraction Extraction.Order OPE OPE.Orbits
open WilsonInvariantActionIntegratedPair
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ→tower S)

theorem replacement (simple : G.Simple) {P : ℝ→Spin.change S 4} {δ g : ℝ→ℝ}
    (same : ∀ᶠr in trail,J r 4=P r) (cal : TendC F P δ) (coupling : Coupling G g)
    {U : Filter (ℕ×ℕ)} (covered : U≤f.fuse) (q : ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠr in trail,∀ (hr:0<r) (b:S.Field 4) (φ:Test 2) (cut:(N p:ℕ)→Fin (N+1)),
      let t:=Next.UVStress.dilate hr φ
      let first:=S.representative 4 (J r 4 (stepField R.family))
      let second:=S.representative 4 b
      let original:=profile R cut first second t
      let raw:=profile R cut (S.representative 4 (center F)) second t
      ∀ᶠz in U, ‖original z.1 z.2-((r^4/(4*δ r):ℝ):ℂ)*raw z.1 z.2‖≤ε*(g r)^q := by
  filter_upwards [WilsonInvariantActionPairCovariance.charged F J simple same cal coupling,coupling.positive] with r paid gr
  intro hr b φ cut t first second original raw
  have genuine:=(along (WilsonInvariantActionIntegratedPair.ordered F cut φ hr (J r 4 (stepField R.family)) b)).mono_left covered
  have inherited:=(along (WilsonInvariantActionIntegratedPair.ordered F cut φ hr (center F) b)).mono_left covered
  have scalar : Tendsto (fun _:ℕ×ℕ=>((r^4/(4*δ r):ℝ):ℂ)) U (𝓝 ((r^4/(4*δ r):ℝ):ℂ)):=tendsto_const_nhds
  have diff:=genuine.sub (scalar.mul inherited)
  have zero : Tendsto (fun z:ℕ×ℕ=>original z.1 z.2-((r^4/(4*δ r):ℝ):ℂ)*raw z.1 z.2) U (𝓝 0) := by
    simpa only [paid b φ,sub_self] using! diff
  filter_upwards [Metric.tendsto_nhds.mp zero (ε*(g r)^q) (mul_pos he (pow_pos gr _))] with z hz
  simpa only [dist_zero_right] using hz.le

theorem embedded {N p k : ℕ} (hk:k≤N) (live:R.family.ref 4≤k) (w:R.family.label 4)
    (o:Site (R.family.side k p)) (U:Config G (R.family.side k p)) (r δ : ℝ) :
    ((r^4/(4*δ):ℝ):ℂ)*actualTransport R.family (N:=N)
      (R.family.O N p w ((R.family.S.toDepth hk p).embed o)) hk U=
    (((r/R.family.S.a k)^4/(4*δ):ℝ):ℂ)*
      ((WilsonInheritedRegisteredField.packet R.makes hk w o).density o (R.family.localSection 4)
        (R.family.path.rep N p k) U / ((R.family.path.rep N p k).eval U:ℂ)) := by
  have transfer:=congr_fun (WilsonInheritedRegisteredField.original (C:=R.family) (N:=N) (per:=p) R.makes hk live w o) U
  calc
    _=((r^4/(4*δ):ℝ):ℂ)*WilsonInheritedRegisteredField.field R.makes hk w o U :=
      congr_arg (fun z:ℂ=>((r^4/(4*δ):ℝ):ℂ)*z) transfer
    _=_ := by
      unfold WilsonInheritedRegisteredField.field MergeProof.alto
      push_cast
      rw [div_pow]
      ring
      rfl

include F in
theorem coarse_price (simple : G.Simple) {P : ℝ→Spin.change S 4} {δ g : ℝ→ℝ}
    (cal : TendC F P δ) (coupling : Coupling G g) :
    Tendsto (fun r=>g r^2/(4*δ r)) trail (𝓝 (-G.slopeConstant⁻¹)) := by
  have trace:=Trace.Link.logfit F simple g δ P coupling cal
  have ratio:=coupling.running.div trace (by norm_num : (-1:ℝ)≠0)
  rw [div_neg,div_one] at ratio
  apply ratio.congr'
  have logpos : Tendsto LogV trail atTop:=Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  filter_upwards [logpos.eventually_gt_atTop 0,trace.eventually_ne (by norm_num : (-1:ℝ)≠0)] with r hl ht
  have hs : 4*δ r≠0:=right_ne_zero_of_mul ht
  change (LogV r*(g r)^2)/(LogV r*(4*δ r))=_
  field_simp [hl.ne',hs]

include F in
theorem charged (simple : G.Simple) {P : ℝ→Spin.change S 4} {δ g : ℝ→ℝ}
    (cal : TendC F P δ) (coupling : Coupling G g) :
    ∃K:ℝ,0<K ∧ ∀ᶠr in trail,∀ (N p k:ℕ) (hk:k≤N) (_:R.family.ref 4≤k)
      (w:R.family.label 4) (o:Site (R.family.side k p)) (U:Config G (R.family.side k p)),
      let density:=(WilsonInheritedRegisteredField.packet R.makes hk w o).density o (R.family.localSection 4)
        (R.family.path.rep N p k) U / ((R.family.path.rep N p k).eval U:ℂ)
      (g r)^2*‖((r^4/(4*δ r):ℝ):ℂ) * actualTransport R.family (N:=N)
        (R.family.O N p w ((R.family.S.toDepth hk p).embed o)) hk U‖ ≤
      K * (r/R.family.S.a k)^4 * ‖density‖ := by
  let K:=‖-G.slopeConstant⁻¹‖+1
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  have bounded:=((coarse_price F simple cal coupling).norm).eventually_lt_const (lt_add_one _)
  filter_upwards [bounded] with r h N p k hk live w o U
  intro density
  have fee : (g r)^2*‖(r/R.family.S.a k)^4/(4*δ r)‖=
      (r/R.family.S.a k)^4*‖(g r)^2/(4*δ r)‖ := by
    simp only [Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg (g r)),
      abs_of_nonneg (show 0≤(r/R.family.S.a k)^4 by positivity)]
    ring
  rw [embedded (R:=R) hk live w o U r (δ r),norm_mul,Complex.norm_real,←mul_assoc,fee]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg density)
  exact (mul_le_mul_of_nonneg_left h.le (by positivity)).trans_eq (mul_comm _ _)

end YM.Integration.WilsonInvariantActionCoarseTrace
