import YM.Integration.WilsonPositionProgramTrialPublicJointFourGroundRows
import YM.WilsonCoeffUV.Root.UV.InverseTransfer

/-! Coefficient control of the nonconstant rows by the genuine inverse train. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveKernel

open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Matrix PowerSeries Finset
open scoped BigOperators Classical
variable {G:Gauge}{F:Frame G 4}

def watch (F:Frame G 4):Wall F→ₗ[ℝ]Wall F where
  toFun := fun A i j=>if sheet F i=0 then 0 else A i j
  map_add' A B:=by ext i j; by_cases c:sheet F i=0 <;>simp [c]
  map_smul' r A:=by ext i j; by_cases c:sheet F i=0 <;>simp [c]

lemma watched (A:Wall F)(i j:Alma F):
    watch F A i j=if sheet F i=0 then 0 else A i j:=rfl

def Live (B:Coil F):Prop:=∀i j:Alma F,sheet F i≠0→sheet F j=0→B i j=0

lemma multi (B:Coil F)(live:Live B)(a:ℕ)(C:Wall F):
    watch F (lineS B a*C)=watch F (lineS B a)*watch F C:=by
  classical
  ext i j
  by_cases quiet:sheet F i=0
  · simp [watched,Matrix.mul_apply,quiet]
  simp only [watched,if_neg quiet,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro t _
  by_cases unit:sheet F t=0
  · have vanish:lineS B a i t=0:=by simp [lineS,live i t quiet unit]
    simp [vanish]
  · simp [unit]

lemma head {A B:Coil F}(direct:A*B=1)
    (origin:∀ i j:Alma F,sheet F i≠0→lineS A 0 i j=(1:Wall F) i j)
    (i j:Alma F)(live:sheet F i≠0):lineS B 0 i j=(1:Wall F) i j:=by
  classical
  have old:=congrArg (fun M:Coil F=>lineS M 0) direct
  rw [line_mul,Finset.Nat.antidiagonal_zero,Finset.sum_singleton,junior] at old
  calc
    _=(lineS A 0 * lineS B 0) i j:=by
      change _=∑t,(lineS A 0 i t)*lineS B 0 t j
      simp [origin i _ live,Matrix.one_apply]
    _= _:=congrFun (congrFun old i) j

theorem step {A B:Coil F}(inverse:B*A=1)(q:ℕ)(pos:0<q)(live:Live B)
    (origin:∀i j:Alma F,sheet F i≠0→lineS B 0 i j=(1:Wall F) i j):
    watch F (lineS A q)=-(∑j∈houseD q,watch F (lineS B j.1)*watch F (lineS A j.2)):=by
  classical
  have old:lineS (B*A) q=0:=by rw [inverse]; exact choral F _ pos
  have member:(0,q)∈HasAntidiagonal.antidiagonal q:=HasAntidiagonal.mem_antidiagonal.mpr (show (0,q).1+(0,q).2=q from zero_add q)
  rw [line_mul,←Finset.add_sum_erase _ _ member] at old
  have entry:=congrArg (watch F) old
  simp only [map_add,map_sum,map_zero] at entry
  have id:watch F (lineS B 0*lineS A q)=watch F (lineS A q):=by
    ext i j
    by_cases quiet:sheet F i=0
    · simp [watched,quiet]
    · simp [watched,quiet,Matrix.mul_apply,origin i _ quiet,Matrix.one_apply]
  rw [id] at entry
  simp_rw [multi B live] at entry
  exact eq_neg_of_add_eq_zero_left entry

end YM.Integration.WilsonPositionProgramTrialPublicJointFourActiveKernel
