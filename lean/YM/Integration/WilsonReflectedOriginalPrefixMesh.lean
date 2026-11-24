import YM.Integration.WilsonCapturedSoldDeckPlacement
import YM.Next.RANK.Coordinates

/-! Every occurrence keeps the physical separation through the finer original dates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOriginalPrefixMesh
open Function Finset Lattice Wilson RG PhysicalNext.Repeat.Legato
open scoped BigOperators

variable (S:Schedule)(p:ℕ)(q:∀i,Ratio (S.side i p) (S.side (i+1) p))
  (x y:∀ i,Site (S.side i p))

theorem count (i:ℕ):(q i).count.val = (S.block i).val:=by
  have eq:=WilsonCapturedSoldDeckPlacement.ratio S i p (q i)
  change (S.denominator i).val*(S.block i).val=(S.denominator i).val*(q i).count.val at eq
  exact Nat.eq_of_mul_eq_mul_left (S.denominator i).property eq.symm

theorem dyadic (j t:ℕ):2^t ≤ (S.steps j t).val:=by
  induction t with
  | zero => simp [Schedule.steps]
  | succ t h =>
    rw [pow_succ,Schedule.steps,PNat.mul_coe]
    exact Nat.mul_le_mul h ((by norm_num:2≤3).trans (S.block_large _))

theorem lower (j t:ℕ)
    (rx:∀i,j ≤ i → i<j+t → (q i).parent (x (i+1))=x i)
    (ry:∀i,j ≤ i → i<j+t → (q i).parent (y (i+1))=y i):
    (S.steps j t).val*separation (x j) (y j)+2 ≤
      separation (x (j+t)) (y (j+t))+2*(S.steps j t).val:=by
  induction t with
  | zero => simp [Schedule.steps]
  | succ t ih =>
    let T:=(S.steps j t).val
    let L:=(S.block (j+t)).val
    let d:=separation (x j) (y j)
    let e:=separation (x (j+t)) (y (j+t))
    let f:=separation (x ((j+t)+1)) (y ((j+t)+1))
    have old:T*d+2≤e+2*T:=ih (fun i a b=>rx i a (by omega)) (fun i a b=>ry i a (by omega))
    have step:L*e≤f+L:=by
      have localStep := Corona.foreshorten (q (j+t)) (x ((j+t)+1)) (y ((j+t)+1))
      rwa [rx _ (by omega) (by omega),ry _ (by omega) (by omega),count S p q (j+t)] at localStep
    have high:2≤L:=(by norm_num:2≤3).trans (S.block_large _)
    change (T*L)*d+2≤f+2*(T*L)
    nlinarith only [step,high,Nat.mul_le_mul_left L old]

theorem rooted (j t u:ℕ)(away:u+2 ≤ separation (x j) (y j))
    (rx:∀i,j ≤ i → i<j+t → (q i).parent (x (i+1))=x i)
    (ry:∀i,j ≤ i → i<j+t → (q i).parent (y (i+1))=y i):
    u*(S.steps j t).val ≤ separation (x (j+t)) (y (j+t)):=by
  have extent:=lower S p q x y j t rx ry
  have paid:=Nat.mul_le_mul_left (S.steps j t).val away
  nlinarith only [extent,paid]

theorem height {G:Gauge}(C:Calendar G)(m t:ℕ):
    C.hatBeta (m+t)=C.hatBeta m+G.slopeConstant*Real.log ((C.schedule.steps m t).val:ℝ):=by
  have left:(0:ℝ)<(C.schedule.denominator m).val:=by exact_mod_cast (C.schedule.denominator m).property
  have right:(0:ℝ)<(C.schedule.steps m t).val:=by exact_mod_cast (C.schedule.steps m t).property
  rw [Calendar.hatBeta,Calendar.hatBeta,Schedule.scale,Schedule.scale,Schedule.a,Schedule.a,inv_inv,inv_inv,Schedule.den_add,PNat.mul_coe,Nat.cast_mul,
    Real.log_mul left.ne' right.ne'];ring

end YM.Integration.WilsonReflectedOriginalPrefixMesh
