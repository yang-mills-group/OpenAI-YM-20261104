import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.Euler
/-! Normalized finite heat equations exponentiate. All asserted on even sector.
Save one grade for successor recursion (no global summability) -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset MeasureTheory Real
open Koszul Book Book.Convolve Actors Engine
open scoped Topology ContDiff Interval
variable {I J E : Type} [AddCommGroup E][Module ℂ E]
variable {M:Actors E}(V:Dynamics M)(K:Engine M)
namespace Dynamics
variable {c:E} (hc:c∈M.guard)
local infix:70 " ⋆ " => M.core
local notation "d"=> ((2:ℂ)⁻¹) • K.join c c
local notation "Jc"=> K.move c
local notation "A"=> Jc+d
local notation "Ew"=> M.wages c
lemma zeroN' (n:ℕ): (n+1:ℂ) ≠ 0 := by exact_mod_cast (show n+1≠0 from (by omega))
lemma phase' (n:ℕ): phase (n+1)= ( (n+1:ℂ)⁻¹ )*phase n:= by unfold phase; rw [Nat.factorial_succ]; push_cast; exact mul_inv .. -- name
lemma nextW (n:ℕ): Ew (n+1)= ( (n+1:ℂ)⁻¹ ) • ( c ⋆ Ew n ):= by rw [wages, power,phase',mul_smul,wages,map_smul]
lemma firstW : Ew 0=M.unit:= by unfold wages power; simp [phase]
lemma nextNF (n:ℕ): c ⋆ Ew n=(n+1:ℂ) • Ew (n+1):= by rw [nextW,smul_inv_smul₀ (zeroN' n)]
include hc
lemma mmc {p:E}(hp:p∈ M.guard)(g:E): c ⋆ (p ⋆ g)=p ⋆ (c ⋆ g):= by rw [← M.star_a, M.turns _ hc _ hp, M.star_a ]
lemma hands : d∈ M.guard:= M.guard.smul_mem _ ( K.join_close hc hc )
lemma wage_earn (n:ℕ): Ew n∈ M.guard:= M.guard.smul_mem _ ( M.p_well c hc _ )
lemma wage_D {f:E}(hf:f∈M.guard)(ht:V.valid c f)(n:ℕ): V.valid ( Ew (n+1) ) ( f ⋆ Ew n ):= by
   induction n with
   | zero=> rw [firstW, nextW,firstW,M.identityR,M.identityR]; simpa using ht
   | succ n ih=>
       obtain he:= V.price _ _ ((n+1+1:ℂ)⁻¹) ( V.duop _ _ _ _ ht ih ); rw [ nextW (M:=M) (n+1),show (↑(n+1)+1:ℂ)⁻¹ =(n+1+1:ℂ)⁻¹ by push_cast; rfl ]; -- expansion
       rw [ mmc hc hf, nextNF n, map_smul ] at he; convert he using 1; -- orientation add relation scalar
       rw [eq_inv_smul_iff₀ (by convert! zeroN' (n+1) using 1; push_cast; rfl : (n+1+1:ℂ)≠0)]; module -- inspect
omit hc in
lemma K_one : K.move ( Ew 1 )= K.move c ⋆ Ew 0:= by rw [nextW (n:=0),firstW,M.identityR,M.identityR]; simp
lemma K_W (n:ℕ): K.move ( Ew (n+1+1) ) = K.move c ⋆ Ew (n+1) + d ⋆ Ew n := by
   have hp := K.stays _ hc; have hu (n:ℕ): K.join c c ⋆ Ew n=(2:ℂ) • ( d ⋆ Ew n ):= by simp only [map_smul,LinearMap.smul_apply,smul_inv_smul₀ (by norm_num : (2:ℂ)≠0)]
   induction n with
   | zero =>
       rw [nextW (n:=0+1),map_smul, K.compatibility _ _ hc ( wage_earn hc _ ), join_wage K c hc _ c hc,K_one K, mmc hc hp, nextNF, map_smul, hu]; norm_num; module
   | succ n ih=>
       rw [ nextW (n:=n+2),map_smul,K.compatibility _ _ hc ( wage_earn hc _ ), ih, join_wage K c hc _ c hc ]; rw [ map_add, mmc hc hp, mmc hc (hands K hc), nextNF,nextNF,map_smul,map_smul, hu ]; rw [ inv_smul_eq_iff₀ ( zeroN' _ ) ]; push_cast; module
-- telescope for numerator
lemma lean_h (h:V.valid c A)(n:ℕ) : V.valid ( M.cheers c (n+1) ) (K.move ( M.cheers c (n+1) ) + d ⋆ M.wages c n):= by
   have hC : A∈M.guard:= M.guard.add_mem ( K.stays _ hc ) (hands K hc); obtain hv := wage_D V hc hC h n;
   induction n with
   | zero=> unfold cheers; simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]; rw [map_add, K_one K]; obtain he := V.plus _ _ _ _ V.mono hv; rw [firstW,K.unitLaw]; convert! he using 1; simp [ firstW, map_add ]
   | succ n ih=>
      rw [show M.cheers c (n+1+1)= M.cheers c (n+1)+ Ew (n+1+1) from Finset.sum_range_succ ..,map_add,K_W K hc n]; convert V.plus _ _ _ _ (ih ( wage_D V hc hC h n )) hv using 1; -- ih not function? inspect
      rw [map_add, LinearMap.add_apply ]; abel
variable (P:SplitP I) {p:I→ E}
omit hc
include K
lemma evaporate (h:Happy P p): Happy P ( (2:ℂ)⁻¹ • P.Lift K.join p p ):= by change ((2:ℂ)⁻¹) • P.Lift K.join p p P.origin=0; rw [ P.loan,P.home]; simp [(show p P.origin=0 from h)]
omit K in
lemma floor_X (ht:Happy P p)(n:ℕ)(x:I)(he:P.grade x ≤ n){v:I→E}(hQ:Happy P v): P.Lift M.core v ((M.stack P).wages p n) x=0:= by
   refine Finset.sum_eq_zero fun i hi=>?_ ; by_cases hv: P.grade i.1=0; · rw [ (P.zeroC _).mp hv, ( show v P.origin=0 from hQ ),map_zero,LinearMap.zero_apply ]
   obtain h:= P.pays hi; rw [Actors.wages, Pi.smul_apply, pole M P p ht (by omega), smul_zero,map_zero ]
lemma expense (hc:p∈ allIndex M.guard I)(h:Happy P p)( hp:(V.extrapolate P).valid p ((K.liftV P).move p + ((2:ℂ)⁻¹) • P.Lift K.join p p) ) : ( V.extrapolate P ).valid ( Cheer M P p ) (pointL I K.move ( Cheer M P p )) := by
   intro i; obtain he : V.valid ((M.stack P).cheers p (P.grade i+1) i) ( K.move (( M.stack P ).cheers p ( P.grade i+1 ) i )+ P.Lift M.core (( (2:ℂ)⁻¹) • P.Lift K.join p p) ( (M.stack P).wages p ( P.grade i )) i) := ( lean_h ( V.extrapolate P ) ( K.liftV P ) hc hp (P.grade i) ) i
   rw [ floor_X P h _ _ le_rfl ( evaporate K P h ), add_zero, Actors.overbook M P p h (by omega) ] at he; exact he -- precision of K implicit
end Dynamics
end YM.MS.Puff
