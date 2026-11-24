import YM.Integration.WilsonReportingCellIntegral
import YM.Integration.WilsonReportingCellRoute

/-! Integrate the actual full reporting source through every intervening
cell on the same finite Wilson field, retaining the actual affine test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingCellField
open Function Filter Finset MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open Trace.Physical RG05Readout Address Native Harvest
open WilsonReportingCellIntegral WilsonReportingCellMotion WilsonReportingBareCell
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {d m N per b:ℕ}

def transfer (C:Family G) (per m k:ℕ) (w:Body→ℂ) (φ:Body):ℂ :=
  Address.average (fun s:Bud C per m=>((C.S.block m).val:ℂ)^k*w
    (Native.pull (displacement C per m s) ((C.S.block m).val:ℝ)⁻¹ φ))

def profile (C:Family G) (per m k:ℕ) : ℕ→(Body→ℂ)→Body→ℂ
  | 0,w=>w
  | q+1,w=>profile C per m k q (transfer C per (m+q) k w)

private def Priced (t:Letter d) (v:C.label (kept t)) (N per j:ℕ)
    (F:Body→Goods G (C.side j per)) (w:Body→ℂ):Prop :=
  BLight F ∧ ∀φ,total (F φ)=w φ*total (row C t v N per j)

private theorem recorded (h:C.Makes) (t:Letter d) (v:C.label (kept t))
    (aged:C.ref (kept t) ≤ m) (live:m ≤ N) :
    Priced t v N per m (centered C t v N per m) (readJ t 0) := by
  have legal:=h.calibrated _ N per (aged.trans live)
  have hi:=TransferData.density_int h.wilson legal v m aged live
  constructor
  · intro φ
    exact hi.smul (readJ t 0 φ)
  · intro φ
    change total (readJ t 0 φ • row C t v N per m)=_
    simp [total,Pi.smul_apply,smul_eq_mul,integral_const_mul]

private theorem moves (h:C.Makes) (t:Letter d) (v:C.label (kept t))
    (aged:C.ref (kept t) ≤ m) (live:m<N) {F:Body→Goods G (C.side (m+1) per)} {w:Body→ℂ}
    (good:Priced t v N per (m+1) F w) :
    Priced t v N per m (journey C per m N d F) (transfer C per m (depth t) w) := by
  have legal:=h.calibrated _ N per (aged.trans live.le)
  have hi:=TransferData.density_int h.wilson legal v (m+1) (aged.trans (Nat.le_succ _)) live
  have eqrow:row C t v N per m=blast C.path N per m (kept t) (row C t v N per (m+1)):=
    legal.unnormalized m aged live v
  have eh : ((C.S.block m).val:ℂ)^d=((C.S.block m).val:ℂ)^depth t*((C.S.block m).val:ℂ)^kept t := by
    rw [← pow_add,Nat.add_sub_of_le (Nat.le_of_lt_succ t.1.isLt)]
  have balance:=WilsonReportingCellIntegral.step (N:=N) (d:=kept t) (row C t v N per (m+1)) hi
  refine ⟨sailed F good.1,?_⟩
  intro φ
  rw [WilsonReportingCellIntegral.original F good.1,eqrow,balance,eh]
  simp_rw [good.2]
  unfold transfer Address.average
  simp only [smul_eq_mul,← Finset.sum_mul,← Finset.mul_sum]
  ring

private theorem route (h:C.Makes) (t:Letter d) (v:C.label (kept t))
    (aged:C.ref (kept t) ≤ m) (q:ℕ) (live:m+q ≤ N)
    (F:Body→Goods G (C.side (m+q) per)) (w:Body→ℂ) (good:Priced t v N per (m+q) F w) :
    Priced t v N per m (WilsonReportingCellRoute.route C per N d m q F)
      (profile C per m (depth t) q w) := by
  induction q generalizing w with
  | zero => exact good
  | succ q ih =>
    exact ih (by omega) _ _ (moves h t v (aged.trans (Nat.le_add_right ..)) live good)

theorem integral (h:C.Makes) (t:Letter d) (v:C.label (kept t))
    (aged:C.ref (kept t) ≤ m) (q:ℕ) (live:m+q ≤ N) (φ:Body) :
    total (WilsonReportingCellRoute.route C per N d m q (centered C t v N per (m+q)) φ)=
    profile C per m (depth t) q (readJ t 0) φ * total (row C t v N per m) := by
  exact (route h t v aged q live _ _
    (recorded h t v (aged.trans (Nat.le_add_right ..)) live)).2 φ

end YM.Integration.WilsonReportingCellField
