import YM.Integration.WilsonCoherentAffineBook
import YM.Integration.WilsonCoherentReportingPivot
import YM.Dict06.Wilson.Tags

/-! The entire finite marked source in its original signed engineering basis.
Each factor is the affine evaluation of the preassigned section polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentAffineRoster
open Function Lattice RG Wilson Source Finset PowerSeries
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open WilsonCoherentReportingFrame Dict06.Series
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ) {n:Side}

def seed (o:I→Site n) (b:Config G n) (z:Edge (Site n)→G.Color) (a:WilsonCoherentReportingFrame.Axis R d):PowerSeries ℂ:=
  ∏ i, WilsonCoherentAffineBook.book (R.family.localSection (d i)) (Pi.single (a i) 1)
    (expandAt (o i) b) (expandAt (o i) z)

def filed (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site n)
    (b:Config G n) (z:Edge (Site n)→G.Color):PowerSeries ℂ:=
  ∑ a,PowerSeries.C (charge R d θ y a)*seed R d o b z a

theorem received (o:I→Site n) (b:Config G n) (z:Edge (Site n)→G.Color) (a:WilsonCoherentReportingFrame.Axis R d) :
    ps (fun t:ℝ=>WilsonCoherentPivotStencil.field (roster R d a) (b ∘ legs (roster R d a) o)
        (t • (z ∘ legs (roster R d a) o)))=seed R d o b z a := by
  let f (i:I) (t:ℝ):=(R.family.localSection (d i)).evaluate (Pi.single (a i) 1)
    (WilsonCoherentAffineBook.field (expandAt (o i) b) (expandAt (o i) z) t)
  have read: (fun t:ℝ=>WilsonCoherentPivotStencil.field (roster R d a) (b ∘ legs (roster R d a) o)
       (t • (z ∘ legs (roster R d a) o)))=∏ i,f i:=by
    funext t
    let U:Config G n:=fun e=>G.lieExp (t • z e)*b e
    change exhibit (roster R d a) (U ∘ legs (roster R d a) o)=_
    rw [exhibition,Finset.prod_apply]
    rfl
  have each i:=WilsonCoherentAffineBook.source (R.family.localSection (d i)) (Pi.single (a i) 1)
      (expandAt (o i) b) (expandAt (o i) z)
  rw [read,(Dict06.Tags.ps_product f univ (fun i _=>(each i).1)).2]
  exact prod_congr rfl (fun i _=>(each i).2)

theorem reported (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site n) (b:Config G n)
    (z:Edge (Site n)→G.Color) (p:ℕ) (t:ℝ) :
    WilsonCoherentReportingPivot.row R d θ y o b z p t =
      ∑ j∈range (p+1),t^j • PowerSeries.coeff j (filed R d θ y o b z) := by
  classical
  unfold WilsonCoherentReportingPivot.row WilsonCoherentPivotStencil.row filed
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [map_sum,Finset.smul_sum]
  apply sum_congr rfl
  intro a _
  rw [PowerSeries.coeff_C_mul,←received,ps_at]
  change _ = t^j • (charge R d θ y a * SignedChartTaylor.jet _ _ j)
  exact mul_smul_comm ..

end YM.Integration.WilsonCoherentAffineRoster
