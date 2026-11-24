import YM.Integration.WilsonPlantedOrdinaryRoster
import YM.Integration.WilsonThermometerRegisteredCapturedWords

/-! Summed true path salaries of the disjoint proper subwords, before the
scalar test is read. Each old word has its own enrolled source center. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedOffers
open Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn
open Push Push.Local Push.AbsoluteSums Finset
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {R:Census (Fin 3)} {α ι:Type}
variable (X:ι→Earn.Row P R G α) (w:Fin 3→ℝ) {σ C:ℝ}
abbrev Keys (s:R.Mode):={a:ι//(X a).mode=s}

lemma salary (hw:∀v,0<w v) (sold:Offers X w σ C) (s:R.Mode) :
    SumBudget (fun z:Keys X s=>(X z.val).height σ) ((Poly.toll w s)⁻¹*(3*C)) := by
  let F(v:Fin 3) (z:Keys X s):ℝ:=if (X z.val).center=P.origin v then Poly.toll w s*(X z.val).height σ else 0
  have one(v:Fin 3): SumBudget (F v) C :=by
    have h:=sumBudget_subtype (fun a=>(X a).mode=s) (sold (P.origin v))
    convert h using 1
    funext z
    simp only [F,z.property]
  have all(Q:Finset (Fin 3)):SumBudget (fun j=>∑v∈Q,F v j) (∑_v∈Q,C):=by
    induction Q using Finset.induction_on with
    | empty=>simp only [sum_empty]; exact ⟨fun _=>le_rfl,summable_zero,by simp⟩
    | insert v Q hv ih=>simpa [sum_insert hv] using sumBudget_add (one v) ih
  have bound:SumBudget (fun j=>∑v:Fin 3,F v j) (3*C):=by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using all univ
  have inside(z:Keys X s):Poly.toll w s*(X z.val).height σ≤∑v:Fin 3,F v z:=by
    let v:=(X z.val).binder.front
    have home:(X z.val).center=P.origin v:=rfl
    calc
      _=F v z:=by simp only [F,if_pos home]
      _≤_:=single_le_sum (fun v _=>(one v).1 z) (mem_univ v)
  have nz:=Poly.worth hw s
  have priced:=sumBudget_mono bound (fun z:Keys X s=>show 0≤Poly.toll w s*(X z.val).height σ from
    mul_nonneg nz.le (mul_nonneg (X z.val).sound.le (Real.exp_pos _).le)) inside le_rfl
  simpa only [←mul_assoc,inv_mul_cancel₀ nz.ne',one_mul] using budget_scale (inv_pos.mpr nz).le priced

theorem original (hw:∀v,0<w v) (sold:Offers X w σ C) {k:ℕ} (subword:Fin k→R.Mode):
    SumBudget (fun u:(j:Fin k)→Keys X (subword j)=>∏ j,(X (u j).val).height σ)
      (∏ j, (Poly.toll w (subword j))⁻¹*(3*C)) :=
  WilsonCapturedPrimarySoftProduct.budget _ _ (fun j=>salary X w hw sold (subword j))
end YM.Integration.WilsonThermometerRegisteredCapturedOffers
