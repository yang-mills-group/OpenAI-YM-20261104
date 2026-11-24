import YM.Integration.WilsonVacuumPreResetFiniteHeatBaseline
import YM.Integration.WilsonVacuumPreResetWindingTransfer

/-! On a physical period, an unweighted unit error in the fine angular
entries has a polynomial output cost at fixed coupling order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatWindow
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{C:Arch G}

def horizon(e r:ℕ):ℕ:=r+2*(3+3*e)+e+2
def power(e r:ℕ):ℕ:=r+1+16*3^(3+3*e)
def fee(p:ScrollV e C)(A:ℝ)(r:ℕ):ℝ:=
  ((horizon e r+2:ℕ):ℝ)+Fintype.card (Joint G (p.n*C.P.L) p.n)+C.mass+
    A+(1+(Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^(horizon e r)

/-- The enrolled Schur and affine dimensions, the full quiet intake and
every marked affine pullback share this one fixed finite-period bill. -/
theorem inputs(p:ScrollV e C)(A:ℝ)(r:ℕ)(positive:0 ≤ A)
    (old:∀i ≤ e,∀l ≤ horizon e r,∀x,|casePW p.wheel C.R p.cone p.W' i l x| ≤ A)
    (D:PChart G (p.n*C.P.L))(small:∀i ≤ e,∀l ≤ horizon e r,∀x,|D i l x| ≤ 1)
    (t:ℝ)(unit:|t| ≤ 1):
    let J:=horizon e r
    let B:=fee p A r
    2≤B ∧ ((J+2:ℕ):ℝ)≤B ∧ (Fintype.card (Joint G (p.n*C.P.L) p.n):ℝ)≤B ∧ C.mass≤B ∧
    (∀l≤J,((Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^l≤B) ∧
    ∀i≤e,∀l≤J,∀x,|casePW p.wheel C.R p.cone (p.W'+t•D) i l x|≤B:=by
  intro J B
  have cm:=zero_le_one.trans C.book
  have z:0 ≤ (Fintype.card (Joint G (p.n*C.P.L) p.n):ℝ):=Nat.cast_nonneg _
  have fine:0 ≤ (Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass:=mul_nonneg (Nat.cast_nonneg _) cm
  have far:0 ≤ (1+(Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^J:=pow_nonneg (by linarith) _
  have term:0 ≤ ((J+2:ℕ):ℝ):=Nat.cast_nonneg _
  have width:((J+2:ℕ):ℝ) ≤ B:=by dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  have many:(Fintype.card (Joint G (p.n*C.P.L) p.n):ℝ) ≤ B:=by
    dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  have base:2 ≤ B:=by push_cast at width;linarith [(show (0:ℝ) ≤ J from Nat.cast_nonneg _)]
  have mass:C.mass ≤ B:=by dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  have shifts(l:ℕ)(j:l≤J):((Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^l≤B:=by
    calc
      _≤(1+(Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^J:=
        (pow_le_pow_left₀ fine (by linarith) l).trans (pow_le_pow_right₀ (by linarith) j)
      _≤B:=by dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  have input(a:ℕ)(u:a ≤ e)(l:ℕ)(j:l ≤ J)(y):
      |casePW p.wheel C.R p.cone (p.W'+t•D) a l y| ≤ B:=by
    have h:=incoming p p.W' D t a l y unit (small a u l j)
    have raised:((Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^l ≤
        (1+(Fintype.card (Woods G (p.n*C.P.L)):ℝ)*C.mass)^J:=
      (pow_le_pow_left₀ fine (by linarith) l).trans (pow_le_pow_right₀ (by linarith) j)
    apply h.trans ((add_le_add (old a u l j y) raised).trans _)
    dsimp only [B,fee];change _ ≤ ((J+2:ℕ):ℝ)+_+_+_+_;linarith
  exact ⟨base,width,many,mass,shifts,input⟩

/-- Price of the actual pre-reset connected heat on every interpolated
node. The original affine row and the whole registered folded intake
are the inputs to this estimate. -/
theorem window(p:ScrollV e C)(A:ℝ)(r:ℕ)(positive:0 ≤ A)
    (old:∀i ≤ e,∀l ≤ horizon e r,∀x,|casePW p.wheel C.R p.cone p.W' i l x| ≤ A)
    (D:PChart G (p.n*C.P.L))(small:∀i ≤ e,∀l ≤ horizon e r,∀x,|D i l x| ≤ 1)
    (t:ℝ)(unit:|t| ≤ 1)(i:ℕ)(hi:i ≤ e)(x):
    |summer p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•D) i r x| ≤ (fee p A r)^(power e r):=by
  let J:=horizon e r
  let B:=fee p A r
  let H:=16*3^(3+3*e)
  obtain ⟨base,width,many,mass,_,input⟩:=inputs p A r positive old D small t unit
  have b:1≤B:=by linarith
  have bp:=zero_le_one.trans b
  have z:0≤(Fintype.card (Joint G (p.n*C.P.L) p.n):ℝ):=Nat.cast_nonneg _
  have budget:=WilsonVacuumPreResetFiniteHeatBudget.through J e
    (by unfold J horizon;omega) _ _ B base width many (fun a v=>(noise p a v).trans mass) input
  have card:((3+3*i:ℕ):ℝ) ≤ B:=(by exact_mod_cast (show 3+3*i ≤ J+2 by unfold J horizon;omega):
    ((3+3*i:ℕ):ℝ) ≤ ((J+2:ℕ):ℝ)).trans width
  let V:=∑j∈range (3+3*i),xray p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•D) j i
  have rack(y):|V r y| ≤ B*B^H:=by
    dsimp only [V]
    simp only [Finset.sum_apply]
    apply WilsonVacuumPreResetFiniteHeatBudget.sum _ _ (pow_nonneg bp _) (by simpa using card)
    intro k hk
    have kn:=Finset.mem_range.mp hk
    apply (budget k i r hi (by unfold J horizon;omega) y).trans
    exact pow_le_pow_right₀ b (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
  have plugcost(a:Joint G (p.n*C.P.L) p.n)(v:Woods G p.n):|plug a v| ≤ 1:=by
    simp only [plug,Matrix.transpose_apply,rightFlag,Matrix.of_apply]
    split <;> norm_num
  have h:=application plug V r 1 (B*B^H) zero_le_one (mul_nonneg bp (pow_nonneg bp _))
    plugcost rack x
  apply h.trans
  simpa only [mul_one,power,H,B,pow_add,pow_one,mul_assoc] using
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ z many r) (mul_nonneg bp (pow_nonneg bp H))

end YM.Integration.WilsonVacuumPreResetFiniteHeatWindow
end
