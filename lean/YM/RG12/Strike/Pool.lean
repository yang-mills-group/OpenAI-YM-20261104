import YM.RG12.Strike.Stitch
/-! # Extremal angular identity

Given harmonic/symmetric derivative tensor P with n axes, and any compact radial annulus moment against a
monomial of degree m ≤ n, kills every n-P derivative contracted with another. Thus yields
zero unless m=n exactly, then proportional to P evaluated at monomial axis-string! Works even
when exterior is a vector (hold its value-index fixed). Pure implication uses no equations of
YM. Will then apply to resonances with exact equality of engineering.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators Classical
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Finset Equiv

abbrev Strip (n:ℕ):=Fin n→Axis4
structure Cloud {n:ℕ}(P:Strip n→ℂ) : Prop where
    symmetric (t:Equiv.Perm (Fin n))(v:Strip n): P (v ∘ t)=P v
    trace (i j:Fin n)(v:Strip n): i≠j → ∑ t:Axis4, P (update (update v i t) j t)=0

variable {n m:ℕ}(i j:Fin n)
-- swapping one coordinate with scratch track. avoids any redIndex issues.
def soar : Equiv.Perm (Strip n × Axis4) where
    toFun p:= (update p.1 i p.2,p.1 i)
    invFun p:=(update p.1 i p.2,p.1 i)
    left_inv p:= by simp
    right_inv p:=by simp
lemma soared (f:Strip n→ℂ) : ∑ v:Strip n,∑ t:Axis4, f (update v i t)= 4 * ∑v:Strip n, f v:=by
    let g(p:Strip n×Axis4):= f (update p.1 i p.2)
    have h:=Fintype.sum_equiv (soar i) g (fun p=> f p.1) (fun _=>rfl)
    simp_rw [Fintype.sum_prod_type,g] at h
    simpa only [sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin, ←mul_sum] using! h
lemma fly2 (f:Strip n→ℂ) : ∑v:Strip n,∑s:Axis4,∑t:Axis4, f (update (update v i s) j t)= 16*∑v:Strip n, f v:=by
   rw [soared i (fun v=>∑ t:Axis4, f (update v j t)),soared,←mul_assoc]; norm_num

-- pair wiring
abbrev Berth (n m:ℕ):= Fin n ⊕ Fin m
abbrev woven (v: Strip n)(u:Strip m) : Berth n m →Axis4 := Sum.elim v u
abbrev matchC (x y:Axis4):ℂ:= if x=y then 1 else 0
variable {d:ℕ}(L:Lay d (Berth n m))
local notation "touch"=>fun (v:Strip n)(u:Strip m)(i:Fin d)=> matchC (woven v u (a L i)) (woven v u (b L i))
def work (v:Strip n)(u:Strip m)(i:Fin d):ℂ:= touch v u i
lemma left {u:Strip m}{f v:Strip n} (i₀ k:Fin d)(hk:k ≠ i₀)
   (h:a L i₀=Sum.inl i)(h': b L i₀=Sum.inl j)(he:∀ k:Fin n,k ≠ i → k ≠ j→ f k=v k): work L f u k=work L v u k:=by
   have hz {x : Berth n m} (hk: x≠Sum.inl i)(hl : x≠Sum.inl j) : woven f u x = woven v u x:= by cases x<;> simp_all [woven]
   have hv (y:Bool)(x:Bool):L (y,k) ≠ L (x,i₀):=fun h=> hk (congr_arg Prod.snd (L.injective h))
   unfold work; dsimp only; rw [hz (by rw [←h]; exact hv false false) (by rw [←h']; exact hv false true), hz (by rw [←h]; exact hv true false) (by rw [←h']; exact hv true true)]

-- paired self collapses the whole booking contribution exactly
variable {P : Strip n→ℂ}(hP:Cloud P)(u:Strip m)
include hP
lemma vanishes (k:Fin d)(ha:a L k=Sum.inl i)(hb:b L k=Sum.inl j):
  ∑ v:Strip n,P v * ∏ l:Fin d,work L v u l=0:=by
   let f(v:Strip n):=P v *∏ l:Fin d,work L v u l
   have hi:i ≠  j:=fun h=> by cases h; exact Bool.noConfusion (congr_arg Prod.fst (L.injective (ha.trans hb.symm)))
   have hv(v:Strip n): ∑ s:Axis4,∑ t:Axis4,f (update (update v i s) j t)=0:=by
      let A:= ∏ l∈univ.erase k, work L v u l; let q(s t:Axis4):=update (update v i s) j t
      have hl(s t:Axis4):f (q s t)=(if s=t then 1 else 0)*(P (q s t)*A):=by
         have hw : ∏ l∈univ.erase k, work L (q s t) u l = A:=by
             refine prod_congr rfl ?_; intro k' hk
             exact left i j L _ _ (ne_of_mem_erase hk) ha hb (fun k hk h=> by simp [q,hk,h])
         unfold f; rw [← mul_prod_erase _ _ (Finset.mem_univ k),hw]; have he : work L (q s t) u k= if s=t then 1 else 0 :=by simp [work, ha,hb,woven,q,hi,matchC]
         rw [he]; ring
      change ∑ s:Axis4,∑ t:Axis4,f (q s t)=_
      simp_rw [hl,ite_mul,zero_mul,one_mul,Finset.sum_ite_eq,if_pos (Finset.mem_univ (_:Axis4)),←Finset.sum_mul]; unfold q; rw [hP.trace _ _ _ hi,zero_mul]
   have hh: 16*∑v:Strip n,P v* ∏l:Fin d,work L v u l=0:=by rw [← fly2 i j f]; exact Finset.sum_eq_zero fun v _=> hv v
   exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
end YM.RG12.Strike
