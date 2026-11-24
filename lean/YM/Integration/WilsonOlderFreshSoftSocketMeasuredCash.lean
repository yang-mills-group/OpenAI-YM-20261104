import YM.Integration.WilsonOlderFreshSoftSocketFaces
import YM.Integration.WilsonOriginalPublicNodalBirth

/-! The exact measured contraction of the complex K-dated socket cash on any proper source face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketMeasuredCash
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonOriginalStarSceneWords (pole)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketInitial (charge)
open WilsonOlderFreshSoftSocketFaces (cash)
open WilsonOriginalPublicTrialFigure (amount)

open WilsonOriginalPublicNodalCash (axis)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonReceivedCanonicalVerseBasis (dose)
open WilsonPositionProgramReportedField (entire)
open ActualRunPhysicalPages Pert.Asymptotics
variable {G:Gauge}{I:Type}[DecidableEq I](R:Run G)(d:I→ℕ){N per K:ℕ}
local notation "F" j:max => R.family.labels.level (d j)
local notation "g" => regulatorRun R.family N per K
variable (S:Finset I)(w:(j:I)→R.family.label (d j))
local notation "V" => (fun j=>entire R (d j) K (N,per) (w j))
def packet (N per K:ℕ)(b:Columns R (fun j:S=>d j)):ℂ:=
  ∏i:S,amount R d (regulatorRun R.family N per K) (fun j=>entire R (d j) K (N,per) (w j)) i (b i)
def ticket (N per K:ℕ)(q:(i:S)→Choice R d i):ℂ:=
  ∏i:S,dose R d N per K w i (q i)*((regulatorRun R.family N per K:ℝ):ℂ)^(-(pole R d (entry R d i (q i)):ℤ))

def seats (b:Columns R (fun i:S=>d i)):Columns R d:=fun i=>if h:i∈S then b ⟨i,h⟩ else 0

omit [DecidableEq I] in
private theorem here (u v:(j:I)→R.family.label (d j))(i:I)(eq:u i=v i)(c:Choice R d i):
    dose R d N per K u i c=dose R d N per K v i c:=by
  cases c with
  | inl a=>cases a;exact congrFun eq 0
  | inr x=>
    change _*((F i).core (u i)) x.1*_= _*((F i).core (v i)) x.1*_
    rw [eq]

theorem original [Fintype I](live:K≤N)(q:(i:S)→Choice R d i):
    ∑b:Columns R (fun j:S=>d j),packet R d S w N per K b * WilsonOlderFreshSoftSocketFaces.cash R d (seats R d S b) S N per K q=
      ticket R d S w N per K q:=by
  classical
  let k (i:S):ℂ:=((g:ℝ):ℂ)^(-(pole R d (entry R d i (q i)):ℤ))
  let a (i:S)(l:(F i).Index):ℂ:=amount R d g V i l *
    (dose R d N per K (request R d (axis R d i l) (N:=N) (p:=per) (K:=K)) i (q i)*k i)
  have one (i:S):∑l:(F i).Index,a i l=dose R d N per K w i (q i)*k i:=by
    simp only [a,←mul_assoc,←Finset.sum_mul,WilsonOriginalPublicNodalCash.original R d (p:=per) live w]
  calc
    _ = ∑b:Columns R (fun j:S=>d j),∏i:S,a i (b i):=by
      apply Finset.sum_congr rfl
      intro b _
      rw [packet,WilsonOlderFreshSoftSocketFaces.cash,←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      have paid :request R d (seats R d S b) (N:=N) (p:=per) (K:=K) i=
          request R d (axis R d i (b i)) (N:=N) (p:=per) (K:=K) i:=by
        simp only [request,seats,dif_pos i.property,WilsonOriginalPublicNodalCash.axis,Pi.single_eq_same]
      have eq:=here R d _ _ (i:I) paid (q i) (N:=N) (per:=per) (K:=K)
      simp only [WilsonOlderFreshSoftSocketInitial.charge,a,k,eq]
    _ = ∏i:S,∑l:(F i).Index,a i l:=by rw [Fintype.prod_sum]
    _ = _:=by rw [ticket];exact Finset.prod_congr rfl fun i _=>one i

end YM.Integration.WilsonOlderFreshSoftSocketMeasuredCash
end
