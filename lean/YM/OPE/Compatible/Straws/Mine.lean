import YM.OPE.Compatible.Straws.Ring
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
structure Fiber (E: Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] (G:Gauge)(I:Type)[Fintype I] where
   f:E ×Keys G I→ℝ
   w:E ×Keys G I→ℝ
   H: Radial.Stationary f
   C: Measurable f
   HC: ContDiffAt ℝ ∞ w 0
   hw:0<w 0
   hv: Measurable w
   M: E→L[ℝ] Keys G I
   Q: Law (Keys G I)
   split:∀ x y, jet f 2 (x,M x+y)= jet f 2 (x,M x)+Q.P y y/2
-- Lift parameter
namespace Fiber
variable (F:Fiber E G I)
abbrev u_q (x:E):= jet F.f 2 (x,F.M x)
def wSign (P:ChartRatio G) : E× Keys G I→ℝ:= F.w * fun x=> Chart.jacobian P x.2
def drape (E Y:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y](M:E→L[ℝ] Y): (E×Y) ≃L[ℝ] (E×Y):= LinearEquiv.toContinuousLinearEquiv {
   toFun :=fun x=>(x.1,M x.1+x.2)
   invFun:=fun y=>(y.1,y.2-M y.1)
   left_inv:=fun ⟨x,y⟩=>by dsimp only; rw [add_sub_cancel_left]
   right_inv:=fun ⟨x,y⟩=>by dsimp only; simp
   map_add':=by intro x y; change (x.1+y.1,M (x.1+y.1)+(x.2+y.2)) =(_,M x.1+x.2+(M y.1+y.2));rw [map_add]; congr 1; abel
   map_smul':=by intro c x; change (c • x.1,M (c • x.1)+c • x.2) =(c • x.1,c • (M x.1+x.2)); rw [map_smul,smul_add] }
omit [BorelSpace E] in
lemma signB {P:ChartRatio G}(R:LocalRatio P):ContDiffAt ℝ ∞ (wSign F P) 0:= F.HC.mul ((show ContDiffAt ℝ ∞ (Chart.jacobian P (U:=I)) 0 from (Chart.Ratio.jacobian_smooth R).of_le le_top).comp (f:=(Prod.snd (α:=E))) (0:E×Y!) contDiffAt_snd)
omit [BorelSpace E] in
lemma signPay {P:ChartRatio G}(R:LocalRatio P):0 < wSign F P 0:= mul_pos F.hw (by change 0<Chart.jacobian P (0:Y!); unfold Chart.jacobian; apply Finset.prod_pos; intro i _; rw [Chart.fee,Pi.zero_apply,R.anchored, mul_one]; exact lt_sup_of_lt_left R.scale)
abbrev cloth (P:ChartRatio G):E× Keys G I → Token:= Curling F.f (F.wSign P) ∘ drape E Y! F.M
structure Path (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][MeasurableSpace E](G:Gauge)(D:Type)[Fintype D] where
    A: Keys G D→ E
    hA: ContDiffAt ℝ ∞ A 0
    hf: Measurable A
    ha: A 0=0
variable (X:Path E G D)
abbrev Path.deck (x:Keys G D):E:= fderiv ℝ X.A 0 x
nonrec def Spine (p:Keys G (D ⊕ I)):E ×Keys G I:= (X.A (BL p),BR p)
def camp : (U!×Y!)≃L[ℝ] K!:= (drape U! Y! (F.M ∘L fderiv ℝ X.A 0)).trans (Pilot.drinks (Equiv.refl _) G).symm
omit [BorelSpace E] in
lemma rig (i:U!×Y!): BL (camp F X i)=i.1 ∧ BR (camp F X i)= F.M (X.deck i.1)+i.2:=by
     let A:=Pilot.drinks (Equiv.refl (D ⊕ I)) G; have he:A (camp F X i)= (i.1,F.M (X.deck i.1)+i.2):= A.apply_symm_apply _; exact Prod.mk.inj he
-- lift accepted
structure SeriesUp (u:Keys G D→ℝ) where
    C:Lid G (D⊕I)
    Z:Law U!
    f:C.f = (F.f ∘ Spine X)+(u ∘ BL)
    v:C.w= F.w ∘ Spine X
    hX:∀ (v:U!)(y:Y!), jet C.f 2 (camp F X (v,y))= Z.P v v/2+F.Q.P y y/2
    pu:Radial.Stationary u
-- decoration computed path. changes y!
def Caul (p:E ×Keys G I→Token)(x:Keys G (D ⊕ I)):Token:= mine fun t=> p (t⁻¹ • Spine X (t • x))
omit [FiniteDimensional ℝ E][BorelSpace E][Fintype I] in lemma SpineBlew :Spine (I:=I) X 0=0:=by unfold Spine;rw [map_zero,map_zero,X.ha];rfl
omit [FiniteDimensional ℝ E][BorelSpace E] in lemma SpineJet : ContDiffAt ℝ ∞ (Spine (I:=I) X) 0:= ((show ContDiffAt ℝ ∞ X.A (BL 0) from ((BL).map_zero).symm ▸ X.hA).comp _ (BL).contDiff.contDiffAt).prodMk (BR).contDiff.contDiffAt
omit [BorelSpace E] in
lemma caulB (p:E×Keys G I→Token)(hp:ScriptJ.B p):ScriptJ.B (Caul X p):=by
     obtain ⟨q,h⟩:= Pawn.amplified (Spine X) (SpineJet X) (SpineBlew X) _ hp; rw [show Caul X p=q from funext fun i=> Gael.chooses (h.stale i)]; exact h.toll
end Fiber
end YM.OPE.Libra
