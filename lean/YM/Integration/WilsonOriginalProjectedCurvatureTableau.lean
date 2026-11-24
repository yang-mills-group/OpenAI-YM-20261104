import YM.Integration.WilsonOriginalProjectedCurvatureLamps
import YM.QuadraticLocal.Germ.Annual

/-! The authenticated point rows are separately linear on their original unit test bills. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureTableau
open Lattice Wilson RG Marker PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open ActualOriginalQReaders ActualOriginalQPackets QuadraticLocal
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureRoster
open scoped Classical

variable {G:Gauge} {R:Run G} {B:MS.Local.Physical.Deck G}
  {p L n:ℕ} {hn:n≤L} {V:Type} [DecidableEq V] [Fintype V]
  (D:ActualRunQlocalNativeTuple.Datum R p L n hn V)

abbrev actors (i:V) : Set (Pos→ℂ) := fun f=>(ActualRunQlocalNativeTuple.orbit D i).Bill f 1

/-- The genuine signed native reader's null space, realized in its ambient function space. -/
def nulls (i:V) : Submodule ℂ (Pos→ℂ) :=
  (ActualRunQlocalNativeTuple.reader D i).ker.map (ActualRunQlocalNativeTuple.orbit D i).Mood.subtype

omit [Fintype V] in
theorem tested (i:V) (c:ℂ) :
    Affinity.Attn (nulls D) (actors D) ({i}:Finset V)
      (fun x=>c*ActualRunQlocalNativeTuple.reader D i
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) x i)) := by
  let lift (a:actors D i):(ActualRunQlocalNativeTuple.orbit D i).Mood:=⟨a.val,⟨1,a.property⟩⟩
  constructor
  · intro x y agree
    have same:x i=y i:=agree i (by simp)
    change c*ActualRunQlocalNativeTuple.reader D i (lift (x i))=c*ActualRunQlocalNativeTuple.reader D i (lift (y i))
    rw [same]
  · intro j hj t x y z a b combined
    obtain rfl:=Finset.mem_singleton.mp hj
    have linear:lift z=a • lift x+b • lift y:=Subtype.ext combined
    simp only [testInclusion,Function.update_self]
    change c*ActualRunQlocalNativeTuple.reader D _ (lift z)=
      a • (c*ActualRunQlocalNativeTuple.reader D _ (lift x))+b • (c*ActualRunQlocalNativeTuple.reader D _ (lift y))
    rw [linear,map_add,map_smul,map_smul]
    simp only [smul_eq_mul]
    ring
  · intro j hj t zero
    obtain rfl:=Finset.mem_singleton.mp hj
    obtain ⟨y,hy,same⟩:=zero
    have recorded:lift (t j)=y:=Subtype.ext same.symm
    change c*ActualRunQlocalNativeTuple.reader D j (lift (t j))=0
    rw [recorded,show ActualRunQlocalNativeTuple.reader D j y=0 from hy,mul_zero]

variable (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B) (μ:ℝ) (orders:V→ℕ)
  (N:ℕ) (σ:ℝ) (extra:V→ℕ)

theorem original :
    Earn.Tableau (nulls D) (actors D) (WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra) := by
  constructor
  intro i
  let s:=i.1
  let c:ℂ:=((placed u s).budget σ:ℂ)*
      ((Pert.Asymptotics.regulatorRun R.family N p L:ℂ)^ActualRunKernelPackets.fieldRank R (degree u) s*
        ActualRunKernelPackets.weight R (degree u) N p L s) *
      fee Q u μ orders s.1 * scaledCoordinates (R:=R) (p:=p) (L:=L) u N s.1 s.2.1
  have one:(WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra i).paint=
      fun x=>c*ActualRunQlocalNativeTuple.reader D s.1.1 (testInclusion (ActualRunQlocalNativeTuple.orbit D) x s.1.1) := by
    funext x
    change ((placed u s).budget σ:ℂ)*ActualRunKernelPackets.amplitude R (ActualRunQlocalNativeTuple.orbit D)
      (degree u) N p L (labels Q D u μ orders N) s (testInclusion (ActualRunQlocalNativeTuple.orbit D) x)=_
    simp only [c,ActualRunKernelPackets.amplitude,labels,readers,Pi.smul_apply,LinearMap.smul_apply,smul_eq_mul]
    ring
  rw [one]
  exact tested D s.1.1 c

/-- The enrolled next step uses the underlying real test space with this same null space. -/
theorem real :
    Earn.Tableau (fun i=>(nulls D i).restrictScalars ℝ) (actors D)
      (WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra) := by
  have source:=original D Q u μ orders N σ extra
  constructor
  intro i
  have row:=source.bill i
  refine ⟨row.sit,?_,row.idle⟩
  intro j hj t x y z a b combine
  have eq:z.val=(a:ℂ) • x.val+(b:ℂ) • y.val := by
    ext k
    exact congrFun combine k
  exact row.turns j hj t x y z (a:ℂ) (b:ℂ) eq

end YM.Integration.WilsonOriginalProjectedCurvatureTableau
