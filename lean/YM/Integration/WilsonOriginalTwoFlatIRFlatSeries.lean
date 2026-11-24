import YM.Integration.WilsonOriginalTwoFlatIRFlatSolo

/-! The coefficient at zero angular rank is multiplicative for the ordinary
proper-face expansion on the cover. This uses the common marked probe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatSeries
open Function Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open Laurent WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open Power PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}
def unitSeries (A:Case D)(S:Finset I) : Era G (Pen D S)→ₗ[ℝ] PowerSeries ℝ where
  toFun P:=PowerSeries.mk fun e=>touch A S (P.2 e 0 Fin.elim0)
  map_add' a b:=by ext e; simp
  map_smul' t p:=by ext e; simp

omit [DecidableEq I] in
theorem value (A:Case D)(S:Finset I)(P:Era G (Pen D S))(e:ℕ):
    PowerSeries.coeff e (unitSeries A S P)=touch A S (P.2 e 0 Fin.elim0):=by simp [unitSeries]

private theorem product (A:Case D){S J:Finset I}(incl:J⊆S)
    (P:Era G (Pen D J))(Q:Era G (Pen D (S\J))):
    unitSeries A S (waxV incl P Q)=unitSeries A J P*unitSeries A (S\J) Q:=by
  ext e
  rw [PowerSeries.coeff_mul]
  simp_rw [value]
  change touch A S ((foam incl P.2 Q.2) e 0 Fin.elim0)=_
  have take:=congrFun (congrFun (congrFun (fp incl P.2 Q.2 A) e) 0) Fin.elim0
  change touch A S ((foam incl P.2 Q.2) e 0 Fin.elim0) = _ at take
  rw [take]
  simp [woad,knitS,swirl,webT,Finset.sum_apply,pPly,ply,cloaks,tinct]

omit [DecidableEq I] in
private theorem blank (A:Case D):unitSeries (G:=G) A ∅ (puff D G)=1:=by
  ext e
  rw [value]
  change touch A ∅ (uband 1 e 0 (Fin.elim0:Fin 0→YForest G) • ochre D)=_
  rw [map_smul,ochre_v]; simp [uband,shine]

theorem original (P:family G D)(empty:P ∅=0)(A:Case D):
    Equation (fun S=>unitSeries A S (levelsO P S)) (fun S=>unitSeries A S (P S)):=by
  refine ⟨by change unitSeries A ∅ (levelsO P ∅)=1; rw [empty_level,blank],by change unitSeries A ∅ (P ∅)=0; rw [empty,map_zero],?_⟩
  funext S
  by_cases z:S=∅
  · subst S; rw [shells_emp]; simp [dial]
  have nonzero:(S.card:ℝ)≠0:=by exact_mod_cast (show S.card≠0 from by simp [z])
  rw [dial,levelsO,dif_neg z,map_smul,map_sum,←Nat.cast_smul_eq_nsmul ℝ S.card _,smul_smul,
    mul_inv_cancel₀ nonzero,one_smul]
  apply Finset.sum_congr rfl
  intro J hJ
  split
  next live=>
    rw [map_smul,product,←smul_mul_assoc]
    exact congrArg (fun f=>f*_) (Nat.cast_smul_eq_nsmul ℝ J.card _)
  next no=>
    obtain rfl:=not_ne_iff.mp (fun e=>no ⟨Finset.mem_powerset.mp hJ,e⟩)
    rw [map_zero]; simp [dial]

end YM.Integration.WilsonOriginalTwoFlatIRFlatSeries
end
