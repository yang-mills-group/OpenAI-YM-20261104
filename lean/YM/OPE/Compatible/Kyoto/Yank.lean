import YM.OPE.Compatible.Kyoto.Colors
import YM.OPE.Compatible.Tune.Theta
/-! # Complexify the real stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Dial
open Function Filter Module Set Finset WithLp
open scoped Topology ContDiff BigOperators Classical
variable {J I E F:Type}{h d:ℕ}{L:Filter I}{p:I→ℝ}
variable (D:Fin (d+1)→ℕ)
variable {t s u:ℝ}
section theoremA
open Lake Hark Yolk
lemma GiftS (a:Fin (d+1))(x y: BR (D a)): Garm D (Pi.single a x,Pi.single a y)= Pi.single a (zag (D a) (x,y)):=by
        ext1 i; change zag _ ((Pi.single a x:CanA D) i,(Pi.single a y:CanA D) i)= _; by_cases ht:i=a; subst i; rw [Pi.single_eq_same,Pi.single_eq_same,Pi.single_eq_same]; rw [Pi.single_eq_of_ne ht,Pi.single_eq_of_ne ht,Pi.single_eq_of_ne ht]; exact map_zero _
lemma spreadP (x:CanA D→L[ℝ] CanA D)(i j:Fin (d+1))(q r:BR (D j)): route (εarm D x) i j (zag (D j) (q,r))= zag (D i) (x (Pi.single j q) i,x (Pi.single j r) i):=by
        change εarm D x (Pi.single j (zag (D j) (q,r))) i = _; rw[← GiftS,Ωp];rfl
lemma canvasP (x:CanA D→L[ℝ] CanA D)(hp:∀ z≤ d+1,∀ v:CanA D,trims z v→ trims z (x v)): team (εarm D x):=by
        intro i j hi; ext1 p; obtain ⟨⟨q,r⟩,rfl⟩:=(zag (D j)).surjective p; rw [spreadP]; have he(w:BR (D j)): x (Pi.single j w) i=0:= hp j.val (Nat.le_of_lt j.isLt) _ (fun l hl=> Pi.single_eq_of_ne (ne_of_lt (show l<j from hl)) _) _ hi; rw[he,he]; exact map_zero _
lemma squared (x:CanA D→L[ℝ] CanA D)(i:Fin (d+1))(p:ℝ)(k:ℝ)(h:∀ v:BR (D i),|‖x (Pi.single i v) i‖^2-(p*‖v‖)^2|≤ k*‖v‖^2)(a:BC (D i)): |‖route (εarm D x) i i a‖^2 - (p*‖a‖)^2|≤ k*‖a‖^2:=by
        obtain ⟨⟨b,c⟩,rfl⟩:=(zag (D i)).surjective a; rw [spreadP,zag_sq,mul_pow,zag_sq]; dsimp only; refine (abs_le).mpr ⟨?_,?_⟩
        · linarith only [(abs_le.mp (h b)).1,(abs_le.mp (h c)).1]
        linarith only [(abs_le.mp (h b)).2,(abs_le.mp (h c)).2]
set_option maxHeartbeats 200000
lemma τreal (p:I→CanA D→L[ℝ] CanA D)(z:I→ℝ)(hz:Tendsto z L atTop)(h: RateLE L z p t): RateLE L z (fun i=> εarm D (p i)) t:=by
        let U: (CanA D→L[ℝ] CanA D)→ₗ[ℝ] BoxQ D →L[ℂ] BoxQ D := {toFun:=εarm D,map_add' a b:=by apply ContinuousLinearMap.ext; intro j; obtain ⟨j,rfl⟩:=(Garm D).surjective j; rw[_root_.add_apply,Ωp,Ωp,Ωp]; exact map_add (Garm D) (doublet a j) (doublet b j) ,map_smul' a b:=by apply ContinuousLinearMap.ext; intro j; obtain ⟨j,rfl⟩:=(Garm D).surjective j; rw[_root_.smul_apply,Ωp,Ωp]; exact (Garm D).map_smul a (doublet b j)}; exact RateLE.linear h hz (U.toContinuousLinearMap)
end theoremA
end YM.OPE.Dial
