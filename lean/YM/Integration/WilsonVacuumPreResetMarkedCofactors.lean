import YM.Integration.WilsonVacuumPreResetMarkedConditionalBound

/-! One before-period price for the entire conditional connected
polynomial of the occupied old faces on the actual elected heat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedCofactors
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake WilsonVacuumPreResetFiniteHeatWindow
open WilsonVacuumPreResetMarkedProducts WilsonVacuumPreResetMarkedOrdinaryBound
open scoped Classical BigOperators
variable {ι:Type}[DecidableEq ι]

theorem original (G:Gauge)(D:ι→ℕ)(I:Finset ι)(e l r:ℕ):∃M:ℝ,0≤M ∧
    ∀C:Arch G,∀p:ScrollV e C,∀A:ℝ,0≤A →
    (∀i≤e,∀v≤horizon e (r+2*l),∀x,|casePW p.wheel C.R p.cone p.W' i v x|≤A) →
    ∀V:PChart G (p.n*C.P.L),(∀i≤e,∀v≤horizon e (r+2*l),∀x,|V i v x|≤1) →
    ∀t:ℝ,|t|≤1 →∀(K:family G D)(a:ι→ℝ),(∀j,0<a j)→
    (∀J⊆I,J.Nonempty→Bounded e (horizon e (r+2*l)) ((K J).1 (p.n*C.P.L)) (weights a J))→
    ∀h≤l+3*e,Bounded e r
      (inHeat p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•V) K I h)
      (M*(fee p A (r+2*l))^((20*3^(l+3*e))*I.card)*weights a I):=by
  let cap:=horizon e (r+2*l)
  let H:=20*3^(l+3*e)
  choose w wpos ordinary using (fun J:Finset ι=>WilsonVacuumPreResetMarkedOrdinaryBound.original G D J e cap)
  let W:=1+∑J∈I.powerset,w J
  have narrow(J:Finset ι)(inc:J⊆I):w J≤W:=by
    have below:=Finset.single_le_sum (fun J _=>wpos J) (Finset.mem_powerset.mpr inc)
    dsimp only [W];linarith
  have wide:1≤W:=le_add_of_nonneg_right (Finset.sum_nonneg (fun J _=>wpos J))
  obtain ⟨C₀,cpos,log⟩:=WilsonVacuumPreResetMarkedLogBound.original D I e r (l+3*e)
  refine ⟨C₀*W^I.card,mul_nonneg cpos (pow_nonneg (by linarith) _),?_⟩
  intro C p A apos old V small t unit K a hot bands
  let B:=fee p A (r+2*l)
  obtain ⟨base,_,_,_,_,_⟩:=inputs p A (r+2*l) apos old V small t unit
  have b:1≤B:=by dsimp only [B];linarith
  let Z:=W*B^H
  have z1:1≤Z:=one_le_mul_of_one_le_of_one_le wide (one_le_pow₀ b)
  let a'(j:ι):=Z*a j
  have restore(J:Finset ι):weights a' J=Z^J.card*weights a J:=by
    simp only [weights,a',Finset.prod_mul_distrib,Finset.prod_const]
  let X:thalamus D (Joint G (p.n*C.P.L) p.n):=oven p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•V) K
  have pre(J:Finset ι)(inc:J⊆I)(alive:J.Nonempty):
      ∀h≤l+3*e,Bounded e r (X J h) (weights a' J):=by
    have positiveW:0<W*weights a J:=mul_pos (by linarith) (Finset.prod_pos (fun j _=>hot j))
    have previous:=ordinary J (p.n*C.P.L) K a (fun j=>(hot j).le) (fun U inside=>bands U (inside.trans inc))
    have fitting:Bounded e cap ((levelsO K J).1 (p.n*C.P.L)) (W*weights a J):=by
      intro i hi v hv x
      exact (previous i hi v hv x).trans (mul_le_mul_of_nonneg_right (narrow J inc) (positive a (fun j=>(hot j).le) J))
    have selected:=WilsonVacuumPreResetMarkedConditionalBound.selected p A l r apos old V small t unit
      _ ((levelsO K J).1 (p.n*C.P.L)) (W*weights a J) positiveW fitting
    intro h hh i hi v hv y
    apply (selected h hh i hi v hv y).trans
    rw [restore]
    have grow:Z≤Z^J.card:=by
      simpa only [pow_one] using pow_le_pow_right₀ z1 alive.card_pos
    calc
      W*weights a J*(fee p A (r+2*l))^(20*3^(l+3*e))=Z*weights a J:=by dsimp only [Z,B,H];ring
      _≤Z^J.card*weights a J:=mul_le_mul_of_nonneg_right grow (positive a (fun j=>(hot j).le) J)
  intro h hh i hi v hv x
  apply (log _ X a' (fun j=>mul_nonneg (by linarith) (hot j).le) pre h hh i hi v hv x).trans_eq
  rw [restore]
  dsimp only [Z,B,H]
  rw [mul_pow,←pow_mul]
  ring

end YM.Integration.WilsonVacuumPreResetMarkedCofactors
end
