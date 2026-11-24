import YM.MS.Dial.Watch

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRichFirstConnectedMoments
open Finset MS MS.Book.Convolve MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom
open scoped Classical BigOperators

private theorem prefix_one {E : Type} [AddCommGroup E] [Module ℂ E] (A : Actors E) (f : E) :
    A.cheers f 1=A.unit+f := by
  rw [Actors.cheers]
  simp [sum_range_succ,wages,phase,Actors.power,A.identityR]

private theorem prefix_two {E : Type} [AddCommGroup E] [Module ℂ E] (A : Actors E) (f : E) :
    A.cheers f 2=A.unit+f+(2:ℂ)⁻¹ • A.core f f := by
  rw [Actors.cheers]
  simp [sum_range_succ,wages,phase,Actors.power,A.identityR,Nat.factorial]

private theorem empty_head {W : Type} [DecidableEq W] (s : Finset W) (h : s.Nonempty) :
    (Trunk.stack (marked W)).unit s=0 := by
  change refineV (marked W) _ s=0
  rw [refineV,if_neg (show s≠(marked W).origin from h.ne_empty)]

theorem single (f : Finset (Fin 1) → T ℂ) :
    bouquet f univ 0=f univ 0 := by
  change (Trunk.stack (marked (Fin 1))).cheers f _ univ 0=_
  have hc : (marked (Fin 1)).grade univ=1 := by decide
  rw [hc,prefix_one,Pi.add_apply,empty_head univ univ_nonempty,zero_add]

theorem product (a b : T ℂ) : Trunk.core a b 1=a 0*b 1+a 1*b 0 := by
  change (∑ i ∈ antidiagonal (1:ℕ),a i.1*b i.2)=_
  have h : antidiagonal (1:ℕ)={(0,1),(1,0)} := by decide
  rw [h]
  simp

theorem pair (f : Finset (Fin 2) → T ℂ) (hf : f ∅=0) :
    bouquet f univ 1 =
      f univ 1 + f {0} 0*f {1} 1 + f {0} 1*f {1} 0 := by
  change (Trunk.stack (marked (Fin 2))).cheers f _ univ 1=_
  have hc : (marked (Fin 2)).grade univ=2 := by decide
  rw [hc,prefix_two]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,empty_head univ univ_nonempty,zero_add]
  change f univ 1 + (2:ℂ)⁻¹ * (∑ i∈subs (univ:Finset (Fin 2)), Trunk.core (f i.1) (f i.2)) 1 = _
  let a : Finset (Fin 2) × Finset (Fin 2) := (∅,univ)
  let b : Finset (Fin 2) × Finset (Fin 2) := ({0},{1})
  let c : Finset (Fin 2) × Finset (Fin 2) := ({1},{0})
  let d : Finset (Fin 2) × Finset (Fin 2) := (univ,∅)
  have hs : subs (univ:Finset (Fin 2))={a,b,c,d} := by decide
  have ha : a∉({b,c,d}:Finset _) := by decide
  have hb : b∉({c,d}:Finset _) := by decide
  have hc' : c∉({d}:Finset _) := by decide
  rw [hs,sum_insert ha,sum_insert hb,sum_insert hc',sum_singleton]
  dsimp only [a,b,c,d]
  simp [hf,product]
  ring

end YM.Integration.WilsonRichFirstConnectedMoments
