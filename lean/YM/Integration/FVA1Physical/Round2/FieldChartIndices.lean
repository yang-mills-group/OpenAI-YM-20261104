import YM.Integration.FVA1Physical.Round2.IndependentWordBanks
import YM.Integration.FVA1Physical.Marked.QuaySpatialReserve
import YM.MSbar.Lis.Scout

/-! Reindex the physical bond directions as independent Wilson chart
coordinates without changing any absolute spatial weight or test point. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Finset Function Lattice RG YM.Wilson MSbar MSbar.Lis MSbar.Whisk MSbar.Wave MSbar.CrossH
open Push.Uniform RGComparison.Core16.Lam RGComparison.Core16.Catkin Integration.FVA1Physical.Marked
open scoped Classical BigOperators

def bondKeys (G:Gauge) (c:Side) : Operand G c ≃ Primary c G where
  toFun u:=primary u.1 u.2
  invFun i:=(rope i,i.2)
  left_inv u:=by rcases u with ⟨e,t⟩;change (rope (primary e t),t)=(e,t);rw [curb]
  right_inv i:=curr i

theorem sum_rekey {ι κ:Type} [Fintype ι] [Fintype κ] (e:ι ≃ κ) (q:ℕ) (F:List κ→ℝ) :
    Yarn q (fun l=>F (l.map e))=Yarn q F := by
  induction q generalizing F with
  | zero=>rfl
  | succ q ih=>
    rw [twilled,twilled]
    calc
      _ = ∑ i:ι,Yarn q (fun l=>F (e i::l)) :=
        sum_congr rfl fun i _=>ih (fun l=>F (e i::l))
      _ = _ := e.sum_comp (fun i=>Yarn q (fun l=>F (i::l)))

theorem charge_in_bonds {G:Gauge} {c:Side} (b:Site c) (a:ℝ) (s q:ℕ)
    (Z:List (Primary c G)→Positions (Primary c G)) (f:Positions (Primary c G)→ℝ) :
    fieldCharge (Measuring.chart c G) b a s q Z f =
      Yarn q (fun l:List (Operand G c)=>
        |buoy f (Z (l.map (bondKeys G c))) (l.map (bondKeys G c))| * spread crest {b} a s l) := by
  unfold fieldCharge
  rw [←sum_rekey (bondKeys G c) q]
  apply stitch
  intro l _
  congr 1
  unfold spread zone
  rw [List.map_map]
  rfl

end YM.Integration.FVA1Physical.Round2.Curvature
