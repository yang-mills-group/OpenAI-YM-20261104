import YM.OPE.Compatible.Arch.Haws
/-!
# From stationary fields to the two-order cone
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore Asymptotics
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
local notation "Lf" => Tested.germ
open Zone Radial ScriptJ
local notation "R" => Radial.zone (E:=E)
omit [FiniteDimensional ℝ E] in lemma levels1 {f:E→ℝ}(x:E): expsum (layers f) 1 1 x= -jet f 3 x:=by
    simp only [expsum,Finset.sum_range_succ,TaylorPow, Zone.mul, Radial.layers]; norm_num [Finset.Nat.antidiagonal_succ] -- find
omit [FiniteDimensional ℝ E] in lemma levels2 {f:E→ℝ}(x:E): expsum (Radial.layers f) 2 2 x= -jet f 4 x+(jet f 3 x)^2/2:=by norm_num [expsum,Finset.sum_range_succ,TaylorPow, Zone.mul,Radial.layers,Finset.Nat.antidiagonal_succ]; ring
omit [FiniteDimensional ℝ E] in
def wheel (u: ScriptJ E) : ScriptJ E:=fun x=>let v:=u x; ⟨1,-v.l,-v.h+v.l^2/2⟩
omit [FiniteDimensional ℝ E] in lemma heightens (u: ScriptJ E)(h:u.B): (wheel u).B:=by
     obtain ⟨_,hh,hj⟩:= bondX h; exact Xbond Bond.one hh.neg (by convert! hj.neg.add ((hh.pow 2).mul (Bond.keep (2:ℝ)⁻¹)) using 1)
lemma spender {c:ℝ}(hc:0<c){f:E→ℝ}(F:Radial.Stationary f): Bears (shade c) (fun t x=>Real.exp (higher f t x)) (wheel (Pawn.mold f 2)):=by
      have h:= F.exponential hc; refine ⟨heightens _ (Pawn.trio F).toll,?_⟩; convert! h.fits 2 using 2; ext x y; simp only [quitt,wheel,JetS.atK,Zone.eval,Finset.sum_range_succ]; norm_num [levels1,levels2, Finset.sum_range_succ, smul_eq_mul, show expsum (layers f) 0 0 y =1 from by norm_num [expsum,TaylorPow, Finset.sum_range_succ]] -- try
end YM.OPE.Libra
