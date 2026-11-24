import YM.MS.Puff.Rescale
/-!
# Logarithm. Arbitrary grade-cuts.Caveat Only applied to unit-at-origin. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset MeasureTheory Real
open Koszul Book Book.Convolve Actors Engine Dynamics Stencil Swirl
open scoped Topology ContDiff Interval
variable {I E F : Type}[ AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F]
namespace Log
variable (M:Actors E)(P:SplitP I) {x:I}
set_option quotPrecheck false
local notation "g"=> P.grade
local notation "ι"=> P.origin
local infix:70 " ⋆ "=> M.core
local infix:69 " ⋄ "=> (M.stack P).core
variable {x y z:I→E}{M}{p q:E}(A:Engine M)(B:Dynamics M)
-- standalone.Engine law exp.K.
lemma goal (i:ℕ)(hp:p∈M.guard) : A.move ( M.cheers p (i+2) )= A.move p ⋆ M.cheers p (i+1)+( (2:ℂ)⁻¹ • A.join p p ) ⋆ M.cheers p i:= by
   induction i with
   | zero=>
       rw [show (0+2:ℕ)=0+1+1 from rfl]; unfold Actors.cheers; simp only [Finset.sum_range_succ, Finset.sum_range_zero,zero_add, Dynamics.firstW,map_add,A.unitLaw,Dynamics.K_W A hp 0,Dynamics.K_one A, M.identityR ]; abel
   | succ i ih=>
       rw [ show M.cheers p (i+1+2)= M.cheers p (i+2)+M.wages p (i+3) from Finset.sum_range_succ .., map_add, ih, Dynamics.K_W A hp (i+1), show M.cheers p (i+1+1) = M.cheers p (i+1)+M.wages p (i+2) from Finset.sum_range_succ .. ]; -- rewrite also ih rhs leading same number.LHS? not. only on RHS
       -- show last expansion once by targeted nth
       let d:=( (2:ℂ)⁻¹ • A.join p p ); have he: d ⋆ M.cheers p (i+1)= d ⋆ M.cheers p i+d ⋆ M.wages p (i+1):= by rw [ show M.cheers p (i+1)= _ from Finset.sum_range_succ ..,map_add ]; rfl; -- proof meta
       rw [map_add,he]; abel
lemma chore {x:I→E}(y:I→E)(hp:Happy P x)(hs:I)(n:ℕ)(hz:g hs≤ n): ( y ⋄ Cheer M P x ) hs= (y ⋄ ((M.stack P).cheers x n)) hs:= by -- malformed
    apply Finset.sum_congr rfl; intro i hi; rw [ Actors.overbook M P x hp (by obtain ht:= P.pays hi; omega) ]
local notation "Δ"=> (2:ℂ)⁻¹ • P.Lift A.join x x
local notation "P'"=> A.liftV P
local notation "V'"=> B.extrapolate P
local notation "F'"=> M.stack P
lemma porez (hp:Happy P x)(he:x∈ allIndex M.guard I) : (P').move ( Cheer M P x ) = ( (P').move x + Δ ) ⋄ Cheer M P x:= by
   funext i; let b:=g i; obtain h := congr_fun ( goal (A.liftV P) (g i) he ) i; change A.move _= ( (( P').move x+Δ ) ⋄ Cheer M P x ) i; -- syntax again
   nth_rw 1 [ ← overbook M P x hp (x:=i) (n:=b+2) (by omega) ]; rw [ map_add ( f:=( M.stack P ).core ), LinearMap.add_apply,Pi.add_apply, chore P (( P').move x) hp i (b+1) (by omega), chore P Δ hp i b (le_refl _) ]; exact h
lemma crest (hp:Happy P x)(hx:x∈allIndex M.guard I)(hy:y∈allIndex M.guard I)(hz:(V').valid x y): (V').valid ( Cheer M P x ) ( y ⋄ Cheer M P x ):= by
   have he (i:ℕ) : (V').valid (( M.stack P ).cheers x (i+1)) ( y ⋄ ( M.stack P ).cheers x i ):= by
       induction i with
       | zero=>
           have ht := Dynamics.plus (V') _ _ _ _ ( V' ).mono (Dynamics.wage_D ( M:=F' ) (V') hx hy hz 0); unfold Actors.cheers; simp only [Finset.sum_range_succ, Finset.sum_range_zero,zero_add, firstW ]; rw [ firstW,zero_add ] at ht; simpa using ht
       | succ i ih=>
           have hp:= Dynamics.plus ( V' ) _ _ _ _ ih ( wage_D ( V' ) hx hy hz (i+1) ); rw [ show ( F' ).cheers x (i+1+1) = ( F' ).cheers x (i+1) + ( F' ).wages x (i+1+1) from Finset.sum_range_succ .. ]; exact (by rwa [ ← map_add, show ( F' ).cheers x i +(F').wages x (i+1)=(F').cheers x (i+1) from (Finset.sum_range_succ ..).symm ] at hp )
   intro i; obtain h:= he (g i) i; rw [ overbook M P x hp (by omega), ← chore P y hp i ( g i ) le_rfl ] at h; exact h
lemma region (h: z ι=M.unit)(ht: ( x ⋄ z )=( y ⋄ z )): x=y:= by
   classical
   funext i; induction he:g i using Nat.strong_induction_on generalizing i with
   | h k ih=>
       obtain hx:= congr_fun ht i; have hp (a:I→E): ( a ⋄ z ) i=a i+∑ j∈ restS P i,a j.1 ⋆ z j.2:= by change P.Lift M.core _ _ _= _; rw [P.loan,← Finset.add_sum_erase _ _ ( P.sym.mp ( ( P.quiet i i ).mpr rfl ) ), h,M.identityR ]; rfl
       rw [hp,hp] at hx; exact add_right_cancel ( Eq.trans hx (congr_arg ( y i + · ) ( Finset.sum_congr rfl (fun j hj=> by rw [ ih _ ( he ▸ keep P hj ) j.1 rfl ])).symm )) -- use transport grammar
-- derivatives in guard.Use Submodule of reachable pairs.Note B.valid linear over phases. In general choice only.
def reachable (B:Dynamics M): Submodule ℂ E where
   carrier:= setOf fun p=> p∈M.guard ∧ ∃ F,F∈ M.guard ∧ B.valid p F
   zero_mem':= ⟨ M.guard.zero_mem, 0,M.guard.zero_mem,B.empty ⟩
   add_mem' {x y} h ht:= by obtain ⟨hx,V,hv,hH⟩:=h; obtain ⟨he,p,hp,hL⟩:=ht; exact ⟨ M.guard.add_mem hx he,V+p,M.guard.add_mem hv hp,B.plus _ _ _ _ hH hL⟩
   smul_mem' c x h:= by obtain ⟨h,F,hF,hC⟩:=h; exact ⟨ M.guard.smul_mem c h,c • F,M.guard.smul_mem _ hF,B.price _ _ c hC ⟩
lemma reachable_c (h:p∈reachable B)(ht:q∈reachable B): p ⋆ q∈ reachable B:= by
    obtain ⟨hp,F,hF,hv⟩:= h; obtain ⟨hu,X,hx,hX⟩:=ht; exact ⟨ M.close _ hp _ hu, F ⋆ q+p ⋆ X,M.guard.add_mem ( M.close _ hF _ hu ) ( M.close _ hp _ hx ),B.duop _ _ _ _ hv hX ⟩
variable (ht:∀ (x:E) y z,B.valid x y→ B.valid x z→ y=z)
include ht
lemma Reverse (hp:(V').valid y ((P').move y))(hu:y ι=M.unit) (he:y∈ allIndex M.guard I) : let e:= Meter M P y; (V').valid e ( (P').move e+(2:ℂ)⁻¹ • (P').join e e ):= by
    intro e; have hv(i:I): e i∈ reachable B:= MeterIN M P y _ (fun _ h _ hp=> reachable_c B h hp) (fun i=> ⟨ he i (Set.mem_univ _),_, ( P' ).stays _ he i ( Set.mem_univ _ ), hp i ⟩ ) i; choose F hF hU using fun i=> ( hv i ).2; have he' : Happy P e:= happy M P y; have hS : e∈allIndex M.guard I:= (universe0 _).mpr fun i=> (hv i).1
    have hP := crest P B he' hS ( (universe0 _).mpr hF ) hU; obtain hX := porez P A he' hS; have hm: Cheer M P e=y:= solve M P _ hu ( (universe0 _).mp he ); rw [ hm ] at hP hX; let p:=( P' ).move e+(2:ℂ)⁻¹ • (P').join e e; have hx:F ⋄ y=p ⋄ y:= funext fun i=> Eq.trans (ht _ _ _ (hP i) (hp i)) (congr_fun hX i); obtain h:= region P hu hx; change (V').valid e p; exact h ▸ ( show (V').valid e F from hU )
end Log
end YM.MS.Puff
