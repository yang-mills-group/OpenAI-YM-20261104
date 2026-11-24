import YM.X.Nest.Spiral
/-! # Receipt at one alphabet. Coefficient-only multilinearity and summation. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Asymptotics Reed Braid Finset
open scoped Topology ContDiff BigOperators Classical
variable {V I: Type*}
variable (Q:Symmetric V)(f:I→poly V) (p q:poly V)(s:Finset I) [DecidableEq I] {i:I}
-- use instance binder [DecEq] rather than classical local?
lemma aeval_glyph (x: V→₀ℂ): (aeval (0:V→ℂ)) (glyph x)=0:= by unfold glyph; simp [Finsupp.linearCombination_apply,Finsupp.sum]
open spiro
lemma splice (L:V→₀ℂ)(hi:i∈s):
   spine Q (Function.update f i (glyph L*f i)) s p=spine Q f s (edge Q L p)+ ∑ j∈s.erase i, spine Q (Function.update f j (edge Q L (f j))) s p := by
   unfold spine; simp only [pulse f p (glyph L* f i) s hi,pstep,map_add,map_mul,aeval_glyph, zero_mul,zero_add]; let t:=s.erase i; let M:=edge Q L; let w (i:I):= Function.update f i (M (f i));
   have he(j:I)(hj:j∈s.erase i): spiro Q (w j) s p=knot Q (f i) (spiro Q (w j) (s.erase i) p):= by rw [pulse₁ (w j) p s hi, show w j i=f i from Function.update_of_ne ((mem_erase.mp hj).1.symm) ..] -- label ∆
   rw [spiralD,padd',map_add,← map_sum]; rw [← pulse₁ f _ s hi]; congr 1
   apply congr_arg ((aeval (0:V→ℂ)) ); rw [pcomm, Braid.psum]; apply Finset.sum_congr rfl; intro j hj;rw [pcomm]; exact (he j hj).symm -- congr restr
-- dynamic grammar
variable {T:Type*}
abbrev Stella (V T:Type*):= T→ V →₀ ℂ
abbrev Code (V T:Type*):= T→poly V
def cross (Q:T→Symmetric V)(x y:Stella V T) : T→ℂ:= fun t=> treats (Q t) (x t) (y t)
def stream (Q:T→Symmetric V)(x:Stella V T): Module.End ℂ (Code V T):= LinearMap.pi fun t:T=> (edge (Q t) (x t)).toLinearMap ∘ₗ LinearMap.proj t
lemma stream_point (Q:T→Symmetric V)(x:Stella V T)(p:Code V T)(t): stream Q x p t=edge (Q t) (x t) (p t):=rfl
variable (q':T→Symmetric V) (g:I→ Code V T) (p':Code V T) (L:Stella V T)
def drip : T→poly V:=fun t=> spiro (q' t) (fun i=>g i t) s (p' t)
def lap : T→ℂ := fun t=> (aeval (0:V→ℂ)) (drip s q' g p' t)
lemma commute_update (c:Code V T)(t:T): (fun x=> Function.update g i c x t)= Function.update (fun x=>g x t) i (c t):= by funext x; by_cases h:x=i <;> simp [h]
lemma lap_step (hi:i∈s): lap s q' (Function.update g i ((glyph ∘ L)*g i)) p'=lap s q' g (stream q' L p')+∑ j∈s.erase i,lap s q' (Function.update g j (stream q' L (g j))) p':= by
   ext1 t; simp only [lap, drip, Pi.add_apply,Finset.sum_apply, commute_update, stream_point]; exact splice (q' t) _ (p' t) s (L t) hi -- .. syntax
lemma lap_add (hi:i∈s)(a b:Code V T): lap s q' (Function.update g i (a+b)) p'=lap s q' (Function.update g i a) p'+ lap s q' (Function.update g i b) p':= by ext1 t; simp only [lap,drip, Pi.add_apply, commute_update]; rw [add_at _ _ _ hi, map_add]
lemma lap_smul (hi:i∈s)(a:T→ℂ)(b:Code V T): lap s q' (Function.update g i (fun t=>a t • b t)) p'= a * lap s q' (Function.update g i b) p':= by ext1 t; simp only [Pi.mul_apply,lap,drip, commute_update]; rw [scale_at _ _ _ _ hi, map_smul];rfl
lemma lap_pos (i:I) (c:Code V T)(h:c=g i):lap s q' (Function.update g i c) p'= lap s q' g p':= by rw [h,Function.update_eq_self]
-- fixed alphabet mean at zero
lemma lap_none (f:I→ T→ℂ): lap s q' (fun i t=>MvPolynomial.C (f i t)) p' = (∏ i∈s, f i)*fun t=>aeval (0:V→ℂ) (p' t):= by
   induction s using Finset.induction_on with
   | empty=> rw [prod_empty,one_mul]; ext1 t; simp [lap,drip]
   | insert i s hi IH=> rw [prod_insert hi,mul_assoc,← IH]; ext1 t; simp only [lap,drip, insertNew _ _ _ hi, Pi.mul_apply]; rw [pc, map_smul]; rfl
end YM.PositionX.Crate
