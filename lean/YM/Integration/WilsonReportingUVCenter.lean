import YM.Integration.WilsonReportingUVLikelihood

/-! The centered factory density follows the same actual Wilson kernels as
its displaced partner. Both can therefore be subtracted at the physical
ultraviolet end, including their original scale factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUVCenter
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source RG12
open RG05Readout Native Address Many Records Harvest Extra.Histories
open PhysicalNext.Repeat.Legato MergeProof Accent WilsonReportingUVReturn WilsonReportingUVLikelihood
open Trace.Physical
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} (h:C.Makes) {N p m d:ℕ}

private theorem factor (C:Family G) (k j:ℕ) :
    ((C.S.block j).val:ℂ)^k*(C.S.a (j+1):ℂ)^k=(C.S.a j:ℂ)^k := by
  rw [←mul_pow]
  congr 1
  exact_mod_cast (show ((C.S.block j).val:ℝ)*C.S.a (j+1)=C.S.a j from by
    rw [C.S.a_step]; field_simp [(Nat.cast_pos.mpr (C.S.block j).property).ne'])

include h in
theorem row (t:Letter d) (x:C.label (kept t)) (live:m ≤ N) (aged:C.ref (kept t) ≤ m) :
    WilsonReportingCellMotion.row C t ((C.factory (kept t) N p).terminal.symm x) N p m=
      (C.S.a m:ℂ)^(kept t) • dyes C m N p live (C.O N p x 0) := by
  let k:=kept t
  let T:=C.factory k N p
  let v:=T.terminal.symm x
  let H:=C.path
  have ready:=h.calibrated k N p (aged.trans live)
  induction live using Nat.decreasingInduction with
  | self =>
    funext X
    change (T.entries N v).density 0 (C.localSection k) (H.rep N p N) X=_
    rw [ready.encode v X]
    have bare:C.O N p x 0 = Source.initial (C.localSection k) H N p v 0:=rfl
    rw [bare]
    simp only [dyes,gust_base,Pi.smul_apply,smul_eq_mul]
    ring
  | of_succ j hj ih =>
    let K:=H.levels.clock.op j p
    let β:=H.β N p (j+1)
    have each:=ready.unnormalized j aged hj v
    have above:=ih (aged.trans j.le_succ)
    change (T.entries j v).density 0 (C.localSection k) (H.rep N p j)=_
    rw [each]
    change ((C.S.block j).val:ℂ)^k • K.push β (WilsonReportingCellMotion.row C t v N p (j+1))=_
    rw [above,Address.preserves,smul_smul,factor]
    exact congrArg ((C.S.a j:ℂ)^k • ·) (gust_step H N p N _ hj).symm

def specimen (t:Letter d) (x:C.label (kept t)) (m N p:ℕ) (φ:Body):Goods G (C.side N p):=
  (readJ t 0 φ*(C.S.a m:ℂ)^kept t) • C.O N p x 0

include h in
theorem centered (t:Letter d) (x:C.label (kept t)) (live:m ≤ N) (aged:C.ref (kept t) ≤ m) (φ:Body) :
    WilsonReportingBareCell.centered C t ((C.factory (kept t) N p).terminal.symm x) N p m φ=
      dyes C m N p live (specimen t x m N p φ) := by
  change readJ t 0 φ • WilsonReportingCellMotion.row C t _ N p m=_
  rw [row h t x live aged,smul_smul,specimen,dye_pitch]

end YM.Integration.WilsonReportingUVCenter
