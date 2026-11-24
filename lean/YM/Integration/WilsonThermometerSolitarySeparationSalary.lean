import YM.Integration.WilsonThermometerMixedGallery
import YM.Integration.WilsonPrecontactSeparatedLamps
import YM.Integration.WilsonThermometerMixedProgram

/-! Reprice just genuine multiply occupied ordinary rows.  The original support wallet pays
the real multiplier on each such row before its next Wilson push. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSolitarySeparationSalary
open Set Function Finset Lattice Wilson RG Marker QuadraticLocal Ac Push.AbsoluteSums
open scoped Classical BigOperators
open WilsonThermometerMixedGallery
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge}{n:Side}{X I:Type}{p:BudgetPoint}{o:Fin 3 → Site n}
  (L:Lamps X I G p o (J))

theorem priced {B M:ℕ}{w:Fin 3 → ℝ}{a C:ℝ}(wp:∀v,0<w v)
    (scope:∀i,1<(L.mode i).val.card → M ≤ coverNumber B (L.ground i))
    (bank:L.Paid w B (a+2) C)(c:ℂ)(cap:‖c‖ ≤ Real.exp (2*(M:ℝ))):
    (lamps c (fun _ _=>True) L).Paid w B a C:=by
  obtain ⟨f,nn,rows,bill⟩:=bank.budget
  let z:=fun i=>rent c (fun _=>True) (L.mode i)
  refine ⟨fun i=>‖z i‖*f i,fun i=>mul_nonneg (norm_nonneg _) (nn i),?_,?_⟩
  · intro i t v hv
    exact Next.Foundations.bound_smul (z i) (rows i t v hv)
  intro x
  apply budget_mono (bill x)
  · intro i
    change 0 ≤ if x ∈ L.ground i then Poly.toll w (L.mode i)*(‖z i‖*f i)*Real.exp _ else 0
    split
    · exact mul_nonneg (mul_nonneg (Poly.worth wp _).le (mul_nonneg (norm_nonneg _) (nn _))) (Real.exp_nonneg _)
    · exact le_rfl
  intro i
  change (if x ∈ L.ground i then Poly.toll w (L.mode i)*(‖z i‖*f i)*Real.exp (a*_) else 0) ≤ 
    (if x ∈ L.ground i then Poly.toll w (L.mode i)*f i*Real.exp ((a+2)*_) else 0)
  by_cases hx:x ∈ L.ground i
  · simp only [if_pos hx]
    let D:ℝ:=coverNumber B (L.ground i)
    have price:‖z i‖ ≤ Real.exp (2*D):=by
      by_cases mixed:1<(L.mode i).val.card
      · have finite:(M:ℝ) ≤ D:=by dsimp [D]; exact_mod_cast scope i mixed
        rw [show z i=c from if_pos ⟨mixed,trivial⟩]
        exact cap.trans (Real.exp_le_exp.mpr (by linarith))
      · rw [show z i=1 from if_neg (by tauto),norm_one]
        exact Real.one_le_exp (by dsimp [D];positivity)
    have value:‖z i‖*Real.exp (a*D) ≤ Real.exp ((a+2)*D):=by
      calc
        _  ≤  Real.exp (2*D)*Real.exp (a*D):=mul_le_mul_of_nonneg_right price (Real.exp_nonneg _)
        _ = _ :=by rw [←Real.exp_add];congr 1;ring
    calc
      _ = (Poly.toll w (L.mode i)*f i)*(‖z i‖*Real.exp (a*D)):=by
        change (Poly.toll w _)*(‖z i‖*f i)*Real.exp (a*D)=(Poly.toll w _*f i)*(‖z i‖*Real.exp (a*D))
        ring
      _  ≤  _ :=mul_le_mul_of_nonneg_left value (mul_nonneg (Poly.worth wp _).le (nn _))
  simp [hx]

theorem separated {B:ℕ}{w:Fin 3 → ℝ}{a C:ℝ}(wp:∀v,0<w v)(hB:5 ≤ B)
    (apart:∀v u:Fin 3,v ≠ u → B^2+1 ≤ separation (o v) (o u))
    (bank:L.Paid w B (a+2) C)(c:ℂ)(cap:‖c‖ ≤ Real.exp (2*(B/8:ℕ))):
    (lamps c (fun _ _=>True) L).Paid w B a C:=by
  apply priced L wp _ bank c cap
  intro i mixed
  obtain ⟨v,hv,u,hu,hvu⟩:=Finset.one_lt_card.mp mixed
  have room:B/8*(4*B+2)+2*B ≤ B^2+1:=by
    have e:=Nat.div_mul_le_self B 8
    have t:=Nat.mul_le_mul_right B e
    have f:=Nat.mul_le_mul_right B hB
    have hh:4*(B/8) ≤ B:=by omega
    nlinarith only [t,f,hh]
  have hD:=(room.trans (apart v u hvu)).trans (Corona.extent (L.ground i) B (L.roots i v hv) (L.roots i u hu))
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right hD) (by omega)

end YM.Integration.WilsonThermometerSolitarySeparationSalary
