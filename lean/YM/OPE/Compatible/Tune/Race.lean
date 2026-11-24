import YM.OPE.Compatible.Tune.Cop
/-!
# Flag ledger. compressed.P
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter Finset
open Drift
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Fin d→Type}{M E F Q:Type}{v:ℝ}{t p:M→ℝ}{ρ:ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
-- `read F→ Tokens`. Lift provided ζ.Price. specific Veins inputs
variable {A:ℕ→ M→Submodule ℝ E}{Y:M→ Submodule ℝ E}{X:(e:Fin d)→(m:M)→ A e.val m→ₗ[ℝ] Jewel (V e)}{g:E→ₗ[ℝ] E}{R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m}
namespace Pipes
variable (H:Pipes A Y X g R)
variable {B:ℕ→ Q→Submodule ℝ F}{Y':Q→ Submodule ℝ F}{W:(e:Fin d)→(m:Q)→ B e.val m→ₗ[ℝ] Jewel (V e)}{g':F→ₗ[ℝ] F}{S:(e:Fin d)→(m:Q)→ Jewel (V e)→ₗ[ℝ] B e.val m}
variable (P:Pipes B Y' W g' S)(m:M)(n:Q)
variable {D:Fin d→ Type}[∀ i,NormedAddCommGroup (D i)][∀ i,NormedSpace ℝ (D i)][∀ i,FiniteDimensional ℝ (D i)][∀ i,FiniteDimensional ℝ (V i)]
variable {p':Q→ ℝ}(A':Charge H t) (D': Charge P p')
variable (f:(i:Fin d)→ Jewel (V i)≃ₗ[ℝ] Jewel (D i))(k' : E→L[ℝ] F)
abbrev RI : Mel V→ₗ[ℝ] Mel V:=Race (R:=R) P m n k'.toLinearMap
omit [∀ i,FiniteDimensional ℝ (D i)] in
lemma stored (h:∀ x:E, P.port n (k' x)=RI (R:=R) P m n k' (H.port m x)) :
    ∀ x:E, Sentinel D' f n (k' x)= Uptake f (RI (R:=R) P m n k') (Sentinel A' f m x):=by
       intro x; rw [intent,intent,h]; change honors f _=honors f ((RI (R:=R) P m n k') ((honors f).symm _)); rw [LinearEquiv.symm_apply_apply] -- Race ..
lemma owns : Uptake f (RI (R:=R) P m n k')=((Sentinel D' f n).comp (k'.comp (ScaledB f R m))).toLinearMap:=by
       apply LinearMap.ext; intro x; change _= Sentinel D' f n (k' (ScaledB f R m x)); rw [intent]; rfl
end Pipes
end YM.OPE.Hark
