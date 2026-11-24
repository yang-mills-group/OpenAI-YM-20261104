import YM.Integration.WilsonReportingUVCell
import YM.Integration.WilsonReportingCoarseQuotient
import YM.Integration.ActualTrajectoryTransport

/-! The entire displaced coarse density is conditioned from an explicit
finite sum of original translated microscopic fields at every coarse gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUVReturn
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source RG12
open RG05Readout Native Address Many Records Harvest Extra.Histories
open PhysicalNext.Repeat.Legato MergeProof Accent WilsonReportingUVCell
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p:ℕ)

def sheets (m d:ℕ) : (q:ℕ)→m+q ≤ N→Bin G (R.family.side N p)→Bin G (R.family.side N p)
  | 0,_,F=>F
  | q+1,live,F=>sheets m d q (by omega) (merged R N p d live F)

private theorem identical (m d i j:ℕ) (eq:i=j) (hi:m+i ≤ N) (hj:m+j ≤ N)
    (F:Bin G (R.family.side N p)) :
    sheets R N p m d i hi F=sheets R N p m d j hj F := by
  cases eq
  rfl

theorem smooth (d m q:ℕ) (live:m+q ≤ N) (F:Bin G (R.family.side N p)) (good:timely F) :
    timely (sheets R N p m d q live F) := by
  induction q generalizing F with
  | zero => exact good
  | succ q ih => exact ih (by omega) _ (ready R N p d live F good)

theorem history (d m q:ℕ) (live:m+q ≤ N) (F:Bin G (R.family.side N p)) (good:timely F) :
    WilsonReportingCellRoute.route R.family p N d m q
        (fun φ=>dyes R.family (m+q) N p live (F φ))=
      fun φ=>dyes R.family m N p (by omega) (sheets R N p m d q live F φ) := by
  induction q generalizing F with
  | zero => rfl
  | succ q ih =>
    change WilsonReportingCellRoute.route R.family p N d m q (journey R.family p (m+q) N d
      (fun φ=>dyes R.family (m+q+1) N p live (F φ)))=_
    rw [show journey R.family p (m+q) N d (fun φ=>dyes R.family (m+q+1) N p live (F φ))=
      (fun φ=>dyes R.family (m+q) N p (by omega) (merged R N p d live F φ)) from
        funext (one R N p d live F good)]
    exact ih (by omega) _ (ready R N p d live F good)

def raw {d:ℕ} (t:Letter d) (x:R.family.label (kept t)) : Bin G (R.family.side N p) :=
  fun φ=>(readJ t 0 φ*(R.family.S.a N:ℂ)^(kept t)) • R.family.O N p x 0

theorem raw_smooth {d:ℕ} (t:Letter d) (x:R.family.label (kept t)) :
    timely (raw R N p t x) := fun _=>(R.family.continuousO ..).const_smul _

theorem incoming {d:ℕ} (t:Letter d) (x:R.family.label (kept t))
    (starts:∀e ≤ d,R.family.ref e ≤ N) :
    pulseOut (basisTop R.family d N p (chunk t ((R.family.factory (kept t) N p).terminal.symm x))) =
      fun φ=>dyes R.family N N p le_rfl (raw R N p t x φ) := by
  funext φ X
  have entered:=WilsonReportingBareCell.incidence (C:=R.family) (N:=N) (p:=p) R.makes t φ (0:Site (R.family.side N p)) x
  have neutral (g:Goods G (R.family.side N p)):stepUp (1,false) 0 g=g:=Motion.dance_nil g
  rw [neutral] at entered
  change (basisTop R.family d N p (chunk t ((R.family.factory (kept t) N p).terminal.symm x)) φ).1 X=_
  rw [basis_agrees R.family d N p R.makes starts φ X,congrFun entered X]
  simp only [dyes,gust_base,raw]

theorem original {b d m:ℕ} {D:Rail R.family} {B:ℕ→ℕ→ℝ}
    {V:Sight R.family d p} {U:Emblems R.family d}
    (spine:Spine D B R.makes b p d N V U) (starts:∀e ≤ d,R.family.ref e ≤ N)
    (t:Letter d) (x:R.family.label (kept t)) (beginning:b ≤ m) (live:m ≤ N) :
    pulseOut (V m (Many.point U (chunk t ((R.family.factory (kept t) N p).terminal.symm x)) N m)) =
      fun φ=>dyes R.family m N p live
        (sheets R N p m d (N-m) (by omega) (raw R N p t x) φ) := by
  obtain ⟨q,rfl⟩:=Nat.exists_eq_add_of_le live
  rw [←WilsonReportingCellRoute.bare (C:=R.family) (m:=m) (N:=q) (per:=p) R.makes spine beginning
    (chunk t ((R.family.factory (kept t) (m+q) p).terminal.symm x)),incoming R (m+q) p t x starts]
  rw [identical R (m+q) p m d (m+q-m) q (by omega) (by omega) le_rfl (raw R (m+q) p t x)]
  exact history R (m+q) p d m q le_rfl _ (raw_smooth R (m+q) p t x)

end YM.Integration.WilsonReportingUVReturn
