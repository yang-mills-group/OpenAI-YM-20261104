import YM.Integration.WilsonMarkedIndependentFiniteHeat
import YM.Integration.WilsonVacuumPreResetFiniteHeatWindow

/-! Uniform section of the true nonbare finite one-mark Wick polynomial. The
old vacuum may vary along its full original signed finite discrepancy. The
source magnitude stays linear, including at angular rank zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentSelectedHeat
open Function Finset Lattice Laurent Wilson RG Precision WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake WilsonVacuumPreResetFiniteHeatWindow
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{C:Arch G}

def power(e l r:ℕ):ℕ:=r+1+20*3^(1+l+3*e)

/-- With the complete selected affine conditional and its exact source
pullback, the cost is an explicit power of the original finite wallet. -/
theorem original(p:ScrollV e C)(A:ℝ)(l₀ r:ℕ)(positive:0 ≤ A)
    (old:∀i ≤ e,∀l ≤ horizon e (r+2*l₀),∀x,|casePW p.wheel C.R p.cone p.W' i l x| ≤ A)
    (D T:PChart G (p.n*C.P.L))(η:ℝ)(hot:0<η)
    (small:∀i ≤ e,∀l ≤ horizon e (r+2*l₀),∀x,|D i l x| ≤ 1)
    (marked:∀i ≤ e,∀l ≤ horizon e (r+2*l₀),∀x,|T i l x| ≤ η)
    (t:ℝ)(unit:|t| ≤ 1)(i:ℕ)(hi:i ≤ e)(x):
    |reed p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•D) l₀ T i r x| ≤
      η*(fee p A (r+2*l₀))^(power e l₀ r):=by
  let J:=horizon e (r+2*l₀)
  let B:=fee p A (r+2*l₀)
  let H:=20*3^(1+l₀+3*e)
  have cm:=zero_le_one.trans C.book
  have z:0 ≤ (Fintype.card (Joint G (p.n*C.P.L) p.n):ℝ):=Nat.cast_nonneg _
  have fine:0 ≤ (Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass:=mul_nonneg (Nat.cast_nonneg _) cm
  have far:0 ≤ (1+(Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^J:=pow_nonneg (by linarith) _
  have term:0 ≤ ((J+2:ℕ):ℝ):=Nat.cast_nonneg _
  have width:((J+2:ℕ):ℝ) ≤ B:=by dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  have many:(Fintype.card (Joint G (p.n*C.P.L) p.n):ℝ) ≤ B:=by
    dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  have base:2 ≤ B:=by push_cast at width;linarith [(show (0:ℝ) ≤ J from Nat.cast_nonneg _)]
  have b:1 ≤ B:=by linarith
  have bp:=zero_le_one.trans b
  have mass:C.mass ≤ B:=by dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  have input(a:ℕ)(u:a ≤ e)(l:ℕ)(j:l ≤ J)(y):
      |casePW p.wheel C.R p.cone (p.W'+t•D) a l y| ≤ B:=by
    have h:=incoming p p.W' D t a l y unit (small a u l j)
    have raised:((Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^l ≤
        (1+(Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^J:=
      (pow_le_pow_left₀ fine (by linarith) l).trans (pow_le_pow_right₀ (by linarith) j)
    apply h.trans ((add_le_add (old a u l j y) raised).trans _)
    dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith

  have source(a:ℕ)(ha:a≤e)(l:ℕ)(hl:l ≤ J)(y):
      |srCold T p.cone a l y| ≤ η*B:=by
    have allowed:=application (camber G p.cone) (T a) l C.mass η cm hot.le (shifted p) (marked a ha l hl) y
    have factor:((Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^l ≤ B:=by
      calc
        _≤(1+(Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^J:=
          (pow_le_pow_left₀ fine (by linarith) l).trans (pow_le_pow_right₀ (by linarith) hl)
        _≤B:=by dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
    exact allowed.trans (by simpa only [mul_comm η] using mul_le_mul_of_nonneg_right factor hot.le)
  have budget:=WilsonMarkedIndependentFiniteHeat.original J e (by unfold J horizon;omega) _ _ _ B η
    base hot width many (fun a v=>(noise p a v).trans mass) input source
  have card:((1+l₀+3*i:ℕ):ℝ) ≤ B:=(by exact_mod_cast (show 1+l₀+3*i ≤ J+2 by unfold J horizon;omega):
    ((1+l₀+3*i:ℕ):ℝ) ≤ ((J+2:ℕ):ℝ)).trans width
  let V:=∑j∈range (1+l₀+3*i),srShade p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•D) T j i
  have rack(y):|V r y| ≤ B*(η*B^H):=by
    dsimp only [V]
    simp only [Finset.sum_apply]
    apply WilsonVacuumPreResetFiniteHeatBudget.sum _ _ (by positivity) (by simpa using card)
    intro h take
    have stage:=Finset.mem_range.mp take
    apply (budget h i r hi (by unfold J horizon;omega) y).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ b (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))) hot.le
  have plugcost(a:Joint G (p.n*C.P.L) p.n)(v:Woods G p.n):|plug a v| ≤ 1:=by
    simp only [plug,Matrix.transpose_apply,rightFlag,Matrix.of_apply]
    split <;> norm_num
  apply (application plug V r 1 (B*(η*B^H)) zero_le_one (by positivity) plugcost rack x).trans
  calc
    _≤B^r*(B*(η*B^H)):=by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right (pow_le_pow_left₀ z many r) (by positivity:0≤B*(η*B^H))
    _=η*B^(power e l₀ r):=by simp only [power,H,pow_add,pow_one];ring

end YM.Integration.WilsonMarkedIndependentSelectedHeat
end
