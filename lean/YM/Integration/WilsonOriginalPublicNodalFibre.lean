import YM.Integration.WilsonOriginalPublicNodalStencils

/-! The complete public measuring vectors on the common incoming group. Each
original marked term keeps its measured coefficient when the trial coupling
and the finite torus are varied independently. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
namespace YM.Integration.WilsonOriginalPublicNodalFibre
open Finset Lattice Wilson RG Source Labels RegulatorIR.FVAAlt2
open ActualRunPhysicalPages Laurent Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonOriginalPublicNodalTransport (group)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOriginalPublicNodalStencils (retime)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[LinearOrder I](d:I→ℕ)
    {N p K:ℕ}(live:K≤N){h:I→ℕ}(κ:(j:I)→Knob (h j))(pt:I→Chamber)
local notation "g" => regulatorRun R.family N p K

/-- The total Laurent change on the selected occupied sockets. -/
def change (t:ℝ)(S:Finset I)(c:Selection R d S):ℂ:=
  ∏j:S,retime R d (N:=N) (p:=p) (K:=K) t j (c j)

include live in
theorem sliced (a:Columns R d)(z:I→ Cover)(S:Finset I)(t:ℝ)(ht:t≠0){n:Side}(U:Config G n):
    group R (fun j:S=>d j) (fun j:S=>z j) (fun j:S=>a j) n U=
      ∑c:Selection R d S,weight R d N p K (request R d a (N:=N) (p:=p) (K:=K)) S c*
        change R d (N:=N) (p:=p) (K:=K) t S c*word R d κ pt t (fun j=>wrap n (z j)) S c U:=by
  rw [WilsonOriginalPublicNodalUnits.product]
  simp_rw [WilsonOriginalPublicNodalStencils.priced R d a live κ pt t ht (p:=p)]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro c _
  simp only [prod_mul_distrib]
  rfl

/-- Missing letters are filled by the already deposited scalar basis index. -/
def complete (S:Finset I)(b:Columns R (fun j:S=>d j)):Columns R d:=
  fun j=>if h:j∈S then b ⟨j,h⟩ else 0

include live in
theorem measured (w:(j:I)→R.family.label (d j))(z:I→ Cover)(S:Finset I)(t:ℝ)
    (ht:t≠0){n:Side}(U:Config G n):
    let δ:=fun j:S=>d j
    let e:=(fun j:S=>WilsonPositionProgramReportedField.entire R (d j) K (N,p) (w j))
    WilsonOriginalPublicTrialFigure.measured R δ g e (fun j:S=>z j) U=
      ∑b:Columns R δ,WilsonOriginalPublicTrialFigure.weight R δ g e b*
        ∑c:Selection R d S,weight R d N p K (request R d (complete R d S b) (N:=N) (p:=p) (K:=K)) S c*
          change R d (N:=N) (p:=p) (K:=K) t S c*word R d κ pt t (fun j=>wrap n (z j)) S c U:=by
  intro δ e
  rw [WilsonOriginalPublicTrialFigure.opened]
  apply sum_congr rfl
  intro b _
  congr 1
  have away:(fun j:S=>complete R d S b j.val)=b:=by funext j;simp [complete]
  have result:=sliced R d (p:=p) live κ pt (complete R d S b) z S t ht U
  rw [away] at result
  exact result

end YM.Integration.WilsonOriginalPublicNodalFibre
end
