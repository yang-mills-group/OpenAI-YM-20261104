import YM.FVA2.Exponential
import YM.FVA2.Wick

/-! # Finite based-copy comparison of master-closed inserted states -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Letter
open Finset Function Matrix MS MS.Koszul MS.Bare MS.Book
open MS.Cylinder MS.Swirl MS.Puff MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open MS.Puff.Actors MS.Puff.Mom OddMatrix Inserted

variable {X Y : Type} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]
variable (hes : Matrix X X ℂ) (grad : Matrix X Y ℂ)

structure Hessian (H : Raw (Letter X Y) ℂ) : Prop where
  rankH : Book.rank 2 H
  evenH : Pure Letter.p false H
  a_a (i : X) (j : Letter X Y) : H [a i, j] = match j with
    | a s => -hes i s
    | _ => 0
  k_k (i : X) (j : Letter X Y) : H [k i, j] = match j with
    | c t => grad i t
    | _ => 0
  c_c (i : Y) (j : Letter X Y) : H [c i,j] = match j with
    | k t => -grad t i
    | _ => 0
  b_b (i : Y) (j : Letter X Y) : H [b i,j]=0

variable {hes grad} {H : Raw (Letter X Y) ℂ}
omit [DecidableEq X] [DecidableEq Y] in
lemma flat_Q (ht : Hessian hes grad H) (F : Raw (Letter X Y) ℂ) (hf : Symm p F) :
    link Δ true p H F= (Q hes grad).Q F := by
  let P := tokenL Δ true p H
  rw [ (bond X Y).by_lap ht.evenH,Fintype.sum_sum_type]
  simp only [playbill ht.rankH,sum_all]
  simp only [bond, Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr,
    ht.a_a, ht.k_k, ht.b_b, ht.c_c, Bonded.fee]
  simp [p]
  rw [q_action _ _ _ hf]
  rw [sum_add_distrib,sum_neg_distrib]
  rw [Finset.sum_comm (f:=fun i j=> grad i j • product p (atLetter (c j)) (D (a i) F)),
    Finset.sum_comm (f:=fun (i:X) j=> hes i j • product p (atLetter (a j)) (D (k i) F)),
    Finset.sum_comm (f:=fun i j=> grad j i • product p (atLetter (k j)) (D (b i) F))]
  abel

variable {F V : SpecB (Letter X Y)} {cov cov' : Matrix X X ℂ} {l l' : Matrix Y X ℂ}

/-- Last finite BV invariance before undoing the rooted symmetry convention.
`F` has the free quadratic removed. Can compare normalized diagrams by using
this also on no insertion. -/
theorem closed_wick_eq (ht : Hessian hes grad H) (hp : Γ F p) (he : EvenSeries p F)
    (h : F 0 = 0) (hu : tokM (bond X Y) (useN.refineV H+F)=0)
    (hm : MarkOK (bond X Y) (useN.refineV H+F) V)
    (hh : hesᵀ=hes) (hz : hes*grad=0)
    (hs : covᵀ=cov) (hv : l*grad=1) (hc : cov*hes=1-grad*l)
    (hs' : cov'ᵀ=cov') (hv' : l'*grad=1) (hc' : cov'*hes=1-grad*l') :
    ℶV (grain cov l) ((PermV p).core (exp0 p F) V) =
      ℶV (grain cov' l') ((PermV p).core (exp0 p F) V) := by
  have hk : Γ ((PermV p).core (exp0 p F) V) p:= ΤΓ_pair (expΓ hp) hm.finiteF
  have hq := interaction_master _ H hu he rfl (show (useN.refineV H + F) 0=H from by
                rw [Pi.add_apply,h,add_zero]; exact if_pos rfl) ht.evenH
  funext i
  obtain ⟨α,α'⟩ := fee_spec (hk i (Set.mem_univ _))
  have hd := closed_integrand (F:=F) _ H ht.evenH he h hq hm.typeF hm.closed
  rw [head_mod] at hd; replace hd := congr_fun hd i
  apply gauges_agree hes grad hh hz hs hv hc hs' hv' hc' _ α' α
  rw [LinearMap.add_apply, ← flat_Q ht _ α]
  exact hd

end YM.FVA2.Letter
