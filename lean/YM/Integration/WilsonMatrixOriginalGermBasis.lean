import YM.Integration.WilsonMatrixOriginalGermColumn
import YM.Trace.Physicalv2.GermSplit

/-! The physical signed capture at its actual finite stop, in the independently priced grade-four basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermBasis
open Lattice Wilson RG Source Labels Precision PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph FVA2 MS.Local.Physical MS.Menus
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open MeasureTheory Finset Extra.Histories
open scoped Classical BigOperators

variable {G:Gauge}

private theorem spread (C:Family G) (d N p i:ℕ) {f:Config G (C.side (i+1) p)→ℂ}
    (hf:Integrable f (prior G _)) (a:ℂ):
    transition (C:=C) d N p i (a • f)=a • transition (C:=C) d N p i f:=by
  unfold transition blast
  rw [StepData.push_smul _ _ _ _ hf]
  exact smul_comm .. 

/-- Calibration carries the complete complex signed source through every physical density integration. -/
def density (C:Family G) (H:C.Makes) (d N p i:ℕ) (age:C.ref d ≤ i) (live:i ≤ N):
    C.label d →ₗ[ℂ] (Config G (C.side i p)→ℂ) where
  toFun:=calValues (C:=C) d N p i
  map_add':=cal_add d N p i H age live
  map_smul' a x:=by
    change calValues (C:=C) d N p i (a • x)=a • calValues (C:=C) d N p i x
    induction live using Nat.decreasingInduction with
    | self =>
      have start(v U):=(H.calibrated d N p age).encode v U
      ext U
      unfold calValues value
      simp only [Pi.smul_apply]
      rw [start,start]
      unfold initial
      simp only [map_smul,Pi.smul_apply,SectionData.places,(C.localSection d).eval_linear.map_smul,smul_eq_mul]
      ring
    | of_succ i next following =>
      have after:=age.trans i.le_succ
      have budget:Integrable (calValues (C:=C) d N p (i+1) x) (prior G _):=message d N p (i+1) H after next (entryOk d N p (i+1) H after next x)
      rw [factory_eq d N p i H age next (a • x),following after,spread C d N p i budget,←factory_eq d N p i H age next x]

private theorem combine {E W A:Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W] [Fintype A]
    (M:E→ₗ[ℂ] W) (z:E) (a:A→ℂ) (s:A→E) (eq:z=∑i,a i • s i):
    M z=∑i,a i • M (s i):=by rw [eq,map_sum M];simp only [map_smul]

private theorem normalize {E A:Type*} [AddCommGroup E] [Module ℂ E] [Fintype A]
    (fit:E≃ₗ[ℂ] E) (x:E) (a:A→ℂ) (s:A→E) (resolved:x=∑i,a i • s i):
    x=∑i,a i • fit (fit.symm (s i)):=by simpa only [fit.apply_symm_apply] using resolved

variable (R:Run G) (B:Deck G) {m N p:ℕ}
local notation "V" => warehouse R

/-- The actual remaining captured head has coefficient one, each independent basis vector is funded by
the original inverse periodic normalization, and the entire signed remainder has zero intrinsic germ. -/
theorem captured (simple:G.Simple) (opened:Opened R.family 4 m p) (live:m ≤ N)
    (q:Coefficient (R.family.labels.level 4) (R.family.side m p)) {r:ℝ}
    (paid:reads (C:=R.family) 4 N p m q r):
    let fit:=fitting 4 N p m R.makes opened live
    let x:=page (C:=R.family) 4 p m q
    let a:=weights V B 4 x
    let source:=fun i:Glyph B 4=>fit.symm (column V B 4 i)
    let fee:=r+2*stock R.family m*(R.family.labels.level 4).coeffSize x
    ∃s:Coefficient (R.family.labels.level 4) (R.family.side m p),
      page (C:=R.family) 4 p m s=0 ∧ reads (C:=R.family) 4 N p m s fee ∧
      (R.family.labels.level 4).coeffSize s.x ≤ invoice (C:=R.family) 4 m p*fee ∧
      x=∑i,a i • fit (source i) ∧
      value (C:=R.family) 4 N p m q=value (C:=R.family) 4 N p m s+
        ∑i,a i • calValues (C:=R.family) 4 N p m (source i) ∧
      (∑i,‖a i‖)≤(R.family.labels.level 4).coeffSize x*fare V B 4:=by
  intro fit x a source fee
  obtain ⟨s,y,sp,zero,actual,ent⟩:=fresh_split0 (d:=4) (N:=N) (p:=p) (i:=m) R.makes opened live q paid
  have budget:=measured_diff 4 N p m R.makes opened.post live sp
  rw [zero,zero_sub,count_neg] at budget
  have record:x=∑i,a i • fit (source i):=
    normalize fit x a (fun i:Glyph B 4=>column V B 4 i) (resolution V B simple x)
  have common:y=∑i,a i • source i:=by
    apply fit.injective
    rw [map_sum fit]
    simp only [map_smul]
    exact ent.trans record
  let D:=density R.family R.makes 4 N p m opened.post live
  have assembled:=combine D y a source common
  exact ⟨s,zero,sp,budget,record,actual.trans (congrArg (fun u=>value (C:=R.family) 4 N p m s+u) assembled),bounded V B 4 x⟩

end YM.Integration.WilsonMatrixOriginalGermBasis
