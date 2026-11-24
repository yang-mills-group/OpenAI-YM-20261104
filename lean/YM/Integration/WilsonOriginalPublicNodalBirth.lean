import YM.Integration.WilsonOriginalPublicNodalCash

/-! The genuine measured finite vector is one distribution of socket weights
on all tori and every occupied subset, after moving the trial clock. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonOriginalPublicNodalBirth
open Finset Lattice Wilson RG Labels Source Pert.Asymptotics Laurent
open ActualRunPhysicalPages PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedCanonicalVerseBasis (dose restored)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOriginalPublicTrialFigure (amount)
open WilsonOriginalPublicNodalCash (axis)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOriginalPublicNodalStencils (retime)
open WilsonOriginalPublicNodalFibre (change)
open WilsonReceivedCanonicalVersePosterior (word)
open WilsonPositionProgramReportedField (entire)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[DecidableEq I](d:I→ℕ)
    {N p K:ℕ}(live:K≤N){h:I→ℕ}(κ:(j:I)→Knob (h j))(pt:I→Chamber)
    (w:(j:I)→R.family.label (d j))
local notation "g" => regulatorRun R.family N p K
local notation "F" j:max => R.family.labels.level (d j)
local notation "V" => (fun i=>entire R (d i) K (N,p) (w i))

include live in
theorem source (t:ℝ)(ht:t≠0)(j:I){n:Side}(z:Site n)(U:Config G n):
    ∑b:(F j).Index,amount R d g V j b*(R.family.localSection (d j)).places (Pi.single b 1) z U=
      ∑c:Choice R d j,(dose R d N p K w j c*retime R d (N:=N) (p:=p) (K:=K) t j c)*
          restored R d κ pt t j c z U:=by
  classical
  have basis(b:(F j).Index):(R.family.localSection (d j)).places (Pi.single b 1) z U=
      ∑c:Choice R d j,(dose R d N p K (request R d (axis R d j b) (N:=N) (p:=p) (K:=K)) j c*
        retime R d (N:=N) (p:=p) (K:=K) t j c)*restored R d κ pt t j c z U:=by
    have exactRow:=WilsonOriginalPublicNodalStencils.priced R d (axis R d j b) (p:=p) live κ pt t ht j z U
    rw [show axis R d j b j=b by simp [axis]] at exactRow
    exact exactRow
  simp_rw [basis,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [←WilsonOriginalPublicNodalCash.original R d (p:=p) live w j c,sum_mul,sum_mul]
  apply sum_congr rfl
  intro b _
  ring

include live in
theorem original (S:Finset I)(z:I→ Cover)(t:ℝ)(ht:t≠0){n:Side}(U:Config G n):
    WilsonOriginalPublicTrialFigure.measured R (fun j:S=>d j) g (fun j:S=>V j)
        (fun j:S=>z j) U=
      ∑c:Selection R d S,weight R d N p K w S c*change R d (N:=N) (p:=p) (K:=K) t S c*
        word R d κ pt t (fun j=>wrap n (z j)) S c U:=by
  unfold WilsonOriginalPublicTrialFigure.measured
  change (∏j:S,∑b:(F j).Index,amount R d g V j b*
    (R.family.localSection (d j)).places (Pi.single b 1) (wrap n (z j)) U)=_
  simp_rw [source R d (p:=p) live κ pt w t ht]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro c _
  simp only [prod_mul_distrib]
  rfl

end YM.Integration.WilsonOriginalPublicNodalBirth
end
