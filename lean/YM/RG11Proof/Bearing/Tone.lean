import YM.RG11Proof.Bearing.Ok
/-! # Unique at finite power order. higher β/b unconstrained. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bearing
open YM.RG11.Jets YM.RG11.Scale PowerSeries
open scoped Classical BigOperators
variable {J:Type*}[Fintype J]{w:J→ℕ}
local notation "ps"=>PowerSeries ℝ

 theorem even_known {N}{β μ:ps}{b m X Y:Square J ps}(h:Through N β μ)(he:MatThrough N b m):
    MatThrough N (X*b+β•flash X-Y*X) (X*m+μ•flash X-Y*X):=
      fun i j=> ((((MatThrough.refl X).mul he i j).add (h.mul (Through.refl _))).sub (Through.refl _))

-- h h' fields/generators at common β, b or approximations.
 theorem solo_perf {N}{β μ:ps}{B P X m Y b:Square J ps}
    (hβ:∀ i≤1,coeff i β=0)(hf:piece 0 B=0)(hm:Through N β μ)(hp:MatThrough N B P)
    (h:Sealed w X m β B N) (he:Sealed w Y b μ P N):
    MatThrough N X Y ∧ MatThrough N m b:=by
   have ht(k)(hk:k≤N):piece k X=piece k Y ∧ piece k m=piece k b:=by
     induction k using Nat.strong_induction_on with
     | h k ih=>
       by_cases hu:k=0
       · subst k; rw [h.base,he.base,h.empty,he.empty]; simp
       have h₀:0<k:=by omega
       have H(i)(hi:i<k):=ih i hi (hi.le.trans hk)
       let c:=known β B X m k+piece k m
       have hC: c=known μ P Y b k+piece k b:=by
         unfold c; rw [beam hβ hf h.base he.base h.empty he.empty h₀ (fun i hi=>(H i hi).1) (fun i hi=>(H i hi).2)]
         exact congrArg (·+piece k b) ((even_known hm hp).piece_eq hk)
       have hr {X q V:Square J ps}{f:ps}(g:Sealed w X q f V N)(t:c=known f V X q k+piece k q):
           piece k X=spot w c (fun r=> -1/r) ∧ piece k q=isolate w c:=by
         have hq:= g.rule.piece_eq hk
         unfold rephase at hq
         have hh:spot w (piece k X) id+known f V X q k=0:=by
            rw [←sep,show diagonalX w*X-X*diagonalX w+(X*V+f• flash X-q*X)=diagonalX w*X-X*diagonalX w+X*V+f• flash X-q*X from by abel,
               show ∀ (l e:Square J ps),piece k (l-e)=piece k l-piece k e from fun l e=>Matrix.ext fun a t=>by simp,hq,sub_self]
         exact Bearing.solo w (g.strict k h₀ hk) (fun e=>g.labelled k hk e) (by rw [t, ← add_assoc,hh,zero_add])
       exact ⟨(hr h rfl).1.trans (hr he hC).1.symm,(hr h rfl).2.trans (hr he hC).2.symm⟩
   exact ⟨MatThrough.of_piece fun k hi=>(ht k hi).1,MatThrough.of_piece fun k hi=>(ht k hi).2⟩

-- imposed CS law of pre vs post after transformation on arrays.
end YM.RG11.Bearing
