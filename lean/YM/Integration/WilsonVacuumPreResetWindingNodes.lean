import YM.Integration.WilsonVacuumPreResetWindingWindow
import YM.Integration.WilsonVacuumPreResetWindingPolynomial
import YM.WilsonCoeffUV.Winding.Gazette

/-! Each interpolated genuine fine quiet input is charged on the original
dated winding treasury. The physical side is the sole side tested. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetWindingNodes
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G:Gauge} {e i m:ℕ} {E:Credit}

def inlet (L:Levels G)(O:ChartRatio G)(N j:ℕ):Crude G:=
  emera (actionW L O N j)

def tested (L:Levels G)(O:ChartRatio G)(N j:ℕ)(t:ℝ):Crude G:=
  fun q=>inlet L O N j q + t•((story L O N j).1 q-inlet L O N j q)

/-- Translation covariance and the signed input error on the actual finite
side. The exponential buys the diameter of that particular torus. -/
def Enter (L:Levels G)(O:ChartRatio G)(N j e:ℕ)(q:Side)(η s:ℝ):Prop:=
  ∀a ≤ e,∀r,stroll ((story L O N j).1 q a r) ∧ ∀x,
    |pruce ((story L O N j).1 q a r-inlet L O N j q a r) x| ≤ η*Real.exp (-s*(4*q.val))

/-- The constant is fixed before every UV date and finite period. The
original forecast vacuum, forest, affine predictor, Jacobian and tree
precision are shared by all interpolation nodes. -/
theorem original (Q:Realm G (e+1) E)(hm:Q.anchor ≤ m)(r:ℕ)(hi:i ≤ e)(s:ℝ)(hs:0<s):
    ∃K:ℝ,0 ≤ K ∧ ∀N,m<N→∀(n:Side)(η t:ℝ),0<η→|t| ≤ 1→
      Enter Q.draws Q.paid N (m+1) e (n*(loose Q.draws m).L) η
        (arborθ s (Q.mint m hm).gear e)→
      ∀x,|pruce (unripe Q.draws Q.paid N m
        (tested Q.draws Q.paid N (m+1) (t/η)) n i r) x| ≤ K:=by
  let I:=holt Q m hm s hs
  let B:=admissionA (Q.mint m hm).gear e*Q.cash (costXV G e E) m
  obtain ⟨d,award⟩:=windingVault G e i r hi
  obtain ⟨β,C,positive,price,native⟩:=award I
  have Bnonnegative:0 ≤ B:=mul_nonneg ((admissionSeal _).trans' zero_le_one)
    (zero_le_one.trans (Credit.purchase _ (Q.depth m hm)))
  refine ⟨C*(B+1)^d,mul_nonneg price (pow_nonneg (by linarith) _),?_⟩
  intro N date n η t unit clock data x
  let p:=cloVent Q m N n hm date s hs
  let pt:ScrollV e I:={ p with
    W:=tested Q.draws Q.paid N (m+1) (t/η)
    coin:=B+1
    paid:=by linarith
    fare:=fun a ha l=>by
      have a0:=data a ha l
      have fold:p.W'=inlet Q.draws Q.paid N (m+1) (n*(loose Q.draws m).L):=rfl
      have width:I.s=arborθ s (Q.mint m hm).gear e:=rfl
      have h:=WilsonVacuumPreResetWindingWindow.submitted I.s 1 B t η I.h.le zero_le_one unit
        clock ((story Q.draws Q.paid N (m+1)).1 (n*(loose Q.draws m).L) a l)
        (p.W' a l) (p.Z a l) a0.1 (p.fare a ha l)
        (fun z=>by rw [fold,width,one_mul];exact a0.2 z)
      exact h }
  have bound:|pruce (pt.player i r) x| ≤ C*(B+1)^d*Real.exp (-β*(soar (tor n) x)):=
    (Real.norm_eq_abs _).ge.trans ((native pt).aim.2 x)
  exact bound.trans (mul_le_of_le_one_right (mul_nonneg price (pow_nonneg (by linarith) _))
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr positive.le)
      (Nat.cast_nonneg _))))

end YM.Integration.WilsonVacuumPreResetWindingNodes
end
