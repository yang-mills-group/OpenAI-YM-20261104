import YM.Integration.WilsonIndependentNotebookReflectedPost
/-! Coordinatewise conjugation of the two real admitted components at the actual report clock. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookReflectedComplex
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonIndependentNotebookReflectedDose (axes)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D d k u e:ℕ}

def read (A:Levels G)(O:ChartRatio G)(N m host q:ℕ)(t:ℝ)(v:Cost):ℂ:=
  cash q t (embed (clock A O N m host v))

theorem real (A:Levels G)(O:ChartRatio G)(N m host q:ℕ)(hm:host ≤ m)(t:ℝ)(v:Cost):
    star (read A O N m host q t v)=read A O N m host q t v:=by
  rw [read,WilsonIndependentNotebookDoseCoefficients.actual A O N m host q hm t]
  exact Complex.conj_ofReal _

theorem reflected (A:Levels G)(O:ChartRatio G)(Q:SealR G)(N m host q:ℕ)(hm:host ≤ m)(t:ℝ)
    (M:Wall Q.F)(vR vI wR wI:Q.Rider)(pR:wR=matrix M vR)(pI:wI=matrix M vI):
    let see:=read A O N m host q t
    ∀i,see (wR i)-Complex.I*see (wI i)=
      ∑j,M i j • star (see (vR j)+Complex.I*see (vI j)):=by
  intro see i
  have turn:=WilsonIndependentNotebookReflectedPost.measured A O Q N m host q hm t M
  change read A O N m host q t (wR i)-Complex.I*read A O N m host q t (wI i)=_
  rw [pR,pI,show read A O N m host q t (matrix M vR i)=_ from turn vR i,
    show read A O N m host q t (matrix M vI i)=_ from turn vI i,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  change M i j • see (vR j)-Complex.I*(M i j • see (vI j))=_
  have hR:star (see (vR j))=see (vR j):=real A O N m host q hm t _
  have hI:star (see (vI j))=see (vI j):=real A O N m host q hm t _
  rw [star_add,star_mul',hR,hI,Complex.star_def,Complex.conj_I]
  simp only [Complex.real_smul]
  ring

end YM.Integration.WilsonIndependentNotebookReflectedComplex
