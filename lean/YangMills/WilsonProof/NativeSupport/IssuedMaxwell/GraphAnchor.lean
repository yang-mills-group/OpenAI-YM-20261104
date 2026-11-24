import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphInverseExterior
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphAnchor
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.Dframe YM.FVA2.Scale
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}
theorem represented:Nonempty (Toon g.core 0):=by
  by_contra empty
  letI:IsEmpty (Toon g.core 0):=not_nonempty_iff.mp empty
  have lost:leaf g.core 0 =0:=by simpa only [Fintype.sum_empty] using (all_sig (leaf g.core 0)).symm
  have ruined:(1:Maxwell.WickPol g.core)=0:=congrArg (fun a:Sec g.core 0=>a.val) lost
  exact one_ne_zero ruined
def label:Q g.core:=flash (Classical.choice (represented g))
theorem weight:heft (label g)=0:=Nat.eq_zero_of_le_zero (size_le (Classical.choice (represented g)))
def word (n:ℕ):Scan g.core n:=fun _=>label g
theorem total:totalG (word g n)=0:=by
  change (∑_:Fin n,heft (label g))=0
  simp only [weight,Finset.sum_const_zero]

theorem converted (p:Ordinary.Price (B g) n)(b:Fin m→Ordinary.Label (B g))(e c h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    Ordinary.truncation (B g) (read g) p e h k b t x y=
      (Real.exp (((e:ℝ)-(c:ℝ))*t):ℂ)*Ordinary.truncation (B g) (read g) p c h k b t x y:=by
  unfold Ordinary.truncation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _=>?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _=>?_
  rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add]
  congr 3
  ring
end IssuedMaxwell.GraphAnchor
end
