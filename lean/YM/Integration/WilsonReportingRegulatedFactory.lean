import YM.RG17.Gathers
import YM.Integration.WilsonReportingFactorySingleton

/-! The engineering factor in the genuine regulated representative cancels
once, at the dated chart. The same signed full factory entry and the same
measured germ are then controlled for every ultraviolet cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingRegulatedFactory
open Filter Lattice Wilson RG Source Extraction Spec RG12 RG17 RG05Readout Address Native Extra.Histories MergeProof.Ribbons
open scoped Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {F:Final C f S}
    (L:Layout F)

def entry (z:ℂ) (d:ℕ) (r:ℝ) (w:C.label d) (N per:ℕ) :=
  let m:=L.level r
  let T:=C.factory d N per
  T.entries m (T.terminal.symm ((z/(C.S.a m:ℂ)^d) • atRef L d r (N,per) w))

theorem upper (z:ℂ) (d:ℕ) (r:ℝ) (w:C.label d) (N per:ℕ) :
    WilsonReportingFactorySingleton.upper F.room.cutoff d (L.level r) N per (z • L.shift d r w) =
    (C.factory d N per).terminal.symm ((z/(C.S.a (L.level r):ℂ)^d) • atRef L d r (N,per) w) := by
  have nz : (C.S.a (L.level r):ℂ)^d ≠ 0 :=
    pow_ne_zero d (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
  unfold WilsonReportingFactorySingleton.upper
  apply congrArg (C.factory d N per).terminal.symm
  rw [map_smul,atRef,Complex.ofReal_pow,smul_smul,div_mul_cancel₀ _ nz]

theorem exact_row (z:ℂ) (d:ℕ) (r:ℝ) (w:C.label d) (N per:ℕ) :
    entry L z d r w N per =
      WilsonReportingFactorySingleton.row F.room.cutoff d (L.level r) N per (z • L.shift d r w) := by
  unfold entry WilsonReportingFactorySingleton.row
  rw [upper]

theorem signed (z:ℂ) (d:ℕ) (r:ℝ) (w:C.label d) {N per:ℕ} (aged:C.ref d ≤ L.level r) (live:L.level r ≤ N) :
    let m:=L.level r
    let q:=entry L z d r w N per
    let rep:=C.path.rep N per m
    q.Format 0 C.params rep ∧ q.x=z • L.shift d r w ∧
      q.remBound 0 rep (Real.sqrt (C.path.levels.clock.forcedAllowance m))
        ((C.path.levels.params m).columns * ‖z‖ * mass C d (L.shift d r w)) := by
  intro m q rep
  change (entry L z d r w N per).Format 0 C.params rep ∧ (entry L z d r w N per).x=_ ∧
    (entry L z d r w N per).remBound 0 rep _ _
  rw [exact_row]
  have fee : mass C d (z • L.shift d r w) = ‖z‖ * mass C d (L.shift d r w) := Extra.Histories.Size.smul _ _ _
  simpa only [fee,mul_assoc] using
    WilsonReportingFactorySingleton.signed F.room.cutoff (per:=per) aged live (z • L.shift d r w)

theorem measured (simple:G.Simple) (d:ℕ) (K:ℝ) {u:Filter ℝ} (growing:Tendsto L.level u atTop) :
    ∀ᶠ r in u, ∀ {N per:ℕ} (t:Letter d) (z:ℂ) (w:C.label (kept t)),
      C.ref (kept t) ≤ L.level r → C.ref d ≤ L.level r → L.level r ≤ N →
      let rep:=C.path.rep N per (L.level r)
      let q:=entry L z (kept t) r w N per
      let a:=chunk t (Trace.Physical.Germ.projection (C.labels.level (kept t)) C.params rep.p.threshold 0 q)
      size (a-chunk t (z • L.shift (kept t) r w))  ≤ 
        Real.exp (-K*C.S.scale (L.level r)) * (‖z‖*mass C (kept t) (L.shift (kept t) r w)) := by
  filter_upwards [growing.eventually (WilsonReportingFactorySingleton.close F.room.cutoff simple d K)] with r bound
  intro N per t z w aged order live rep q a
  have equal := exact_row L z (kept t) r w N per
  have fee := Extra.Histories.Size.smul (C.labels.level (kept t)) z (L.shift (kept t) r w)
  change size (chunk t (Trace.Physical.Germ.projection _ _ _ _ (entry L z (kept t) r w N per)) - _) ≤ _
  rw [equal]
  exact (bound (per:=per) t (z • L.shift (kept t) r w) aged order live).trans_eq (congrArg _ fee)

end YM.Integration.WilsonReportingRegulatedFactory
