import YM.RG11Proof.Travel.Driver
import YM.RG11Proof.Travel.Squalls
import YM.RG11Proof.Scale.Flowing

/-! # Acting by the constructed finite-length scaling solves CS through N

Not on testing φ rotated; on fixed arrays. Compare to moving geometry solution
using uniqueness. H0 spatial normalization uses `s 0`. Sign b as Scale/CS so
use Static b = `-generator` in this solution format. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Travel
open YM.RG11.Jets YM.RG11.Scale PowerSeries YM.PertExtension.Position
open scoped BigOperators Classical Topology
local notation "ps"=>PowerSeries ℝ
local notation "slots"=> PertExtension.Position.insert
variable {J P:Type*}{width:P→ℕ}[Fintype J]

-- derivative of acted solution exactly solves orbit PDE at any fixed scale
namespace Static
variable (K:Static J)(A:ArrayAt J ℝ width)

 theorem solves (N)(s:ℝ)(v:Mark J width): Speed (fun b:ℝ=> (K.changeBy b).act A v) s (call K.β (-K.b) ((K.changeBy s).act A) v) N:=by
   let p:= K.changeBy
   let β:=K.β
   let X:=β*derivative ℝ (p s).g
   let D:= (p s).Z
   let D':= β • flash D+K.b * D
   let a(w:Mark J width):=PowerSeries.subst (p s).g (A w)
   let χ(w:Mark J width):=PowerSeries.subst (p s).g (derivative ℝ (A w))
   have hT(u:ℝ):Anchored (p u).g:=(K.lawful_glide u).1
   have hβ:Anchored β:= Eq.trans (coeff_zero_eq_constantCoeff_apply _).symm (K.quiet 0 (by decide))
   have ht: Anchored X:=by unfold Anchored X; rw [map_mul,show constantCoeff β=0 from hβ,zero_mul]
   rw [call_derivative _ _ K.β (-K.b) (hT s)]
   -- β •flash D - (-K.b)*D = D'
   change Speed (fun b=>slots J width (fun w=>_) (fun i j=>_) v) _ (slots J width (fun w=> X*χ w) (fun i j=>D i j) v+ varies a D (_- - K.b*D) v) _
   rw [neg_mul,sub_neg_eq_add]
   unfold varies PertExtension.Position.insert
   rw [←Finset.sum_add_distrib]
   refine Speed.sum (fun w _=> Speed.mul ?_ ?_)
   · have he:= Speed.subst (p:=fun b=>(p b).g) (s:=s) (N:=N) (fun i _=>K.d_ruler s i) hT ht (A ⟨v.1,w⟩)
     dsimp only; rw [mul_comm X]; exact he
   have hv:=Speed.gate (f:=fun i:Fin (width v.1)=> fun a:ℝ=> (K.changeBy a).Z (v.2 i) (w i)) (s:=s) (v:=fun i=> ((K.β • flash (K.aim s))+K.b*K.aim s) (v.2 i) (w i)) Finset.univ (fun i _ k (_:k≤N)=> K.d_frame s k (v.2 i) (w i))
   convert! hv using 1
   congr!
end Static

-- only through order N
 theorem uniqueness {K:Static J}{n}(a b:ℝ→ArrayAt J ℝ width)
     (he:∀ v,Through n (a 0 v) (b 0 v))
     (ha:∀ s v,Speed (fun q=>a q v) s (call K.β K.b (a s) v) n)
     (hb:∀ s v,Speed (fun q=>b q v) s (call K.β K.b (b s) v) n)(s:ℝ)(v):Through n (a s v) (b s v):=by
   intro k hk
   induction k using Nat.strong_induction_on generalizing s v with
   | h k ih=>
     let til (u:ℝ):=coeff k (a u v)-coeff k (b u v)
     have H(u:ℝ): HasDerivAt til 0 u:=by
       have hf:= (ha u v k hk).sub (hb u v k hk)
       have hg(p:ℕ × ℕ)(h:p.1+p.2=k) : coeff p.1 K.β * coeff p.2 (derivative ℝ (a u v))=coeff p.1 K.β * coeff p.2 (derivative ℝ (b u v)):=by
         by_cases he:p.1≤1
         · simp [K.quiet _ he]
         rw [coeff_derivative,coeff_derivative,ih (p.2+1) (by omega) _ _ (by omega)]
       suffices hh:coeff k (call K.β K.b (a u) v)=coeff k (call K.β K.b (b u) v) by rw [hh,sub_self] at hf; exact hf
       unfold call orbit; simp_rw [map_sub,map_sum,coeff_mul]
       congr 1
       · exact Finset.sum_congr rfl (fun z hz=>hg z (Finset.HasAntidiagonal.mem_antidiagonal.mp hz))
       refine Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun j _=>Finset.sum_congr rfl (fun z hz=>?_)))
       have he:= Finset.HasAntidiagonal.mem_antidiagonal.mp hz
       by_cases ht:z.1=0
       · simp only [ht,←piece_apply (A:=K.b),K.still,Matrix.zero_apply,zero_mul]
       rw [ih _ (by omega) _ _ (by omega)]
     have ht:= is_const_of_deriv_eq_zero (fun u=>(H u).differentiableAt) (fun u=>(H u).deriv) s 0
     unfold til at ht; rw [he v k hk,sub_self] at ht; exact sub_eq_zero.mp ht
end YM.RG11.Travel
