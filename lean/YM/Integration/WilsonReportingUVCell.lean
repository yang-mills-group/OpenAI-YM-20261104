import YM.Integration.WilsonPositionSeparatedProfileCenteredBranch

/-! One full displaced reporting step as an actual microscopic observable.
All retained degrees use the same physical transition and the original finite
average over its embedded children. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingUVCell
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source
open RG05Readout Native Address Many Records Harvest Extra.Histories
open WilsonPositionSeparatedProfileCenteredBranch PhysicalNext.Repeat.Legato MergeProof Accent
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p:ℕ) {m:ℕ}

private theorem smoothSum {n:Side} {I:Type*} (s:Finset I) (X:I→Goods G n)
    (smooth:∀i,Continuous (X i)) : Continuous (∑i∈s,X i) := by
  simp_rw [Finset.sum_fn]
  exact continuous_finsetSum _ (fun i _=>smooth i)

theorem averaged {I:Type*} [Fintype I] {m:ℕ} (live:m≤N)
    (X:I→Goods G (R.family.side N p)) (smooth:∀i,Continuous (X i)) :
    dyes R.family m N p live (Address.average X)=
      Address.average (fun i=>dyes R.family m N p live (X i)) := by
  have sums (s:Finset I):dyes R.family m N p live (∑i∈s,X i)=
      ∑i∈s,dyes R.family m N p live (X i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,dye_vac]
    | @insert i s hin ih =>
      simp only [Finset.sum_insert hin]
      rw [dye_plus (C:=R.family) (N:=N) (p:=p) R.makes (X i) (∑j∈s,X j) live (smooth i) (smoothSum s X smooth),ih]
  unfold Address.average
  rw [dye_pitch,sums]

def merged (d:ℕ) (top:m+1≤N) (F:Bin G (R.family.side N p)) : Bin G (R.family.side N p) :=
  fun φ=>((R.family.S.block m).val:ℂ)^d • Address.average (arrangement R N p top F φ)

theorem ready (d:ℕ) (top:m+1≤N) (F:Bin G (R.family.side N p)) (smooth:timely F) :
    timely (merged R N p d top F) := by
  intro φ
  apply Continuous.const_smul
  unfold Address.average
  apply Continuous.const_smul
  exact smoothSum _ _ (fun i=>(smooth _).comp (continuous_pull (G:=G) 1 _))

theorem one (d:ℕ) (top:m+1≤N) (F:Bin G (R.family.side N p)) (smooth:timely F) (φ:Body) :
    journey R.family p m N d (fun f=>dyes R.family (m+1) N p top (F f)) φ =
      dyes R.family m N p (m.le_succ.trans top) (merged R N p d top F φ) := by
  let C:=R.family
  let S:=C.path.levels.clock.op m p
  let β:=C.path.β N p (m+1)
  have row (i:Bud C p m):
      S.push β ((dyes C (m+1) N p top (F (headFee C p m i φ))) ∘ Lattice.pull 1 (child C p m i))=
        dyes C m N p (m.le_succ.trans top) (arrangement R N p top F φ i) := by
    rw [← covariance R N p top (child C p m i) _ (smooth _)]
    exact (gust_step C.path N p N _ top).symm
  unfold merged
  rw [dye_pitch,averaged R N p (m.le_succ.trans top) (arrangement R N p top F φ) (fun i=>(smooth _).comp (continuous_pull (G:=G) 1 _))]
  change Address.average (fun i:Bud C p m=>((C.S.block m).val:ℂ)^d •
    S.push β ((dyes C (m+1) N p top (F (headFee C p m i φ))) ∘ Lattice.pull 1 (child C p m i)))=_
  simp_rw [row]
  exact Address.ave_smul _ _

end YM.Integration.WilsonReportingUVCell
