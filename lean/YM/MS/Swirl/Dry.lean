import YM.MS.Swirl.Cut
/-!
# Operators & continuous formal order laws
Cauchy series coefficient-by-coefficient. Prepare normalized Euler argument. This also applies to
inversion of exponential maps later (for cumulants) on SplitP including subset marker geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Filter Set Finset MeasureTheory Real
open Koszul Book Convolve Puff Engine SplitP Actors Dynamics
open scoped Topology ContDiff Interval
variable {I E F H J A:Type} [AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F][AddCommGroup H][Module ℂ H]
variable (P:SplitP I){n:ℕ}
-- SLift at oil.L
section L
variable (L:I→Linear E F)
def SL : Linear (I→E) (I→F):={
  toFun X i:=∑ j∈ P.pieces i,L j.1 ( X j.2 )
  map_add' _ _ := funext fun i=> by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' _ _ := funext fun i=> by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum] }
lemma slΩ (F:I→ E)(x:I): SL P L F x=∑ j∈ P.pieces x,L j.1 ( F j.2 ):=rfl
lemma slides (U:I→E)(V: Bil E E F): P.Lift V U = SL P (fun i=> V (U i)):=rfl -- definitional proof?
lemma look_c (i:I)(x:E): SL P L ( P.refineV x ) i= L i x:= by
   have hp : SL P L ( P.refineV x )=fun i=>L i x:= (P.tm (LinearMap.id ( M:=Linear E F )) x L); exact congr_fun hp i -- id implicit types
lemma borrow (K: I→Linear F H)(v:I→E): SL P K (SL P L v)= SL P (fun i=> ∑ j∈ P.pieces i, ( K j.1 ).comp ( L j.2 )) v:= by funext i; simp_rw [slΩ,map_sum, LinearMap.sum_apply]; exact P.trip H i (fun i j k=> K i (L j (v k)))
lemma repayment (K:Linear F H) (v:I→E): pointL I K (SL P L v)= SL P (fun i=>(K.comp (L i))) v:= by funext i; change K _ = _; simp_rw [slΩ,map_sum]; rfl
end L
-- Noncomm constant reward agrees at each coefficient.(∴ subspace)
lemma continueM {M:Submodule ℂ E}(K L:I→Linear E F)(hp:∀ x∈ M,SL P K (P.refineV x)=SL P L ( P.refineV x )) (v:I→E)(he:∀ i,v i∈M): SL P K v= SL P L v:= by
    have hx {x:E}(h:x∈ M)(i:I): K i x=L i x:= by rw [← look_c P K i x,← look_c P L i x,hp x h ]
    funext i; exact Finset.sum_congr rfl fun j _=> hx ( he j.2 ) j.1
-- algebra.
def Zip {J:Type}(P:SplitP I)(n:ℕ)(f g:I→J): Prop:= ∀ i, P.grade i≤n→ f i=g i
structure Filtered (P:SplitP I)(V:Linear ( I→E ) ( I→F )): Prop where
   stays {h k n}: Zip P n h k → Zip P n ( V h ) ( V k )
namespace Filtered
variable {P}
lemma sl (P:SplitP I)(K:I→Linear E F): Filtered P (SL P K):= ⟨fun h i he=> Finset.sum_congr rfl fun j hj=> by rw [h j.2 (by obtain hv:=P.pays hj; omega)]⟩
lemma loft {M:Actors E}{F H g u:I→ E}(he:Zip P n F H) (hp: Zip P n g u): Zip P n ( P.Lift M.core F g) ( P.Lift M.core H u ):= by intro i h; apply Finset.sum_congr rfl; intro j hj; obtain ht:=P.pays hj; rw [he j.1 (by omega),hp j.2 (by omega)] -- unfold lift implicit
end Filtered
variable {M:Actors E}
local notation "Mτ"=> M.stack P
set_option quotPrecheck false
local infix:70 " ⋆ "=> ( Mτ ).core
structure Cinch (P:SplitP I) (M:Actors E)(L:Linear (I→E) (I→E)): Prop extends Filtered P L where
   still : L ( (M.stack P).unit )=0
   earn {x}: x∈ allIndex M.guard I→ L x∈ allIndex M.guard I -- map close on core
   earns (x y:I→E) : L ( (M.stack P).core x y ) =(M.stack P).core ( L x ) y +( M.stack P ).core x ( L y )
namespace Cinch
variable {L: Linear ( I→E ) ( I→E )} {P} {x y:I→ E} (h:Cinch P M L)
def mode : Dynamics ( Mτ ):= {
   valid x y:= L x=y
   mono:= h.still
   empty:= map_zero _
   plus:= fun _ _ _ _ hx he=> by rw [map_add,hx,he]
   price:= fun _ _ x he=> by rw [map_smul,he]
   duop:=fun x y p q hx he=> by rw [h.earns,hx,he] }
local notation "z"=> Cheer M P x
lemma totalZ (he:x∈allIndex M.guard I) : z∈allIndex M.guard I:= (universe0 M.guard).mpr fun i=> ( (allIndex M.guard I).sum_mem (t:=Finset.range (P.grade i+1)) (fun j _=> wage_earn (M:=Mτ) he j) ) i ( Set.mem_univ _ ) -- support
include h
lemma waste (hv:x∈allIndex M.guard I)(k:ℕ): L ((Mτ).cheers x (k+1)) = ( L x ⋆ ((Mτ).cheers x k)):= by
    unfold Actors.cheers; rw [map_sum, Finset.sum_range_succ', Dynamics.firstW,h.still,add_zero,map_sum]; exact Finset.sum_congr rfl fun i _=> wage_D (h.mode) hv ( h.earn hv ) rfl i -- h∇
lemma idea (hv:x∈ allIndex M.guard I)(hp:Happy P x): L z=( L x ⋆ z ):= by
    funext i; let Ξ:= P.grade i; have he {n k:ℕ}(hh:k≤n): Zip P k (( Mτ ).cheers x n) z:= fun j hj=> overbook M P x hp ( hj.trans hh ); rw [ ← h.stays ( n:=Ξ ) ( he (n:=Ξ+1) (by omega)) i le_rfl,h.waste hv Ξ ]; exact Filtered.loft (M:=M) (n:=Ξ) (fun j hk=> rfl) (he le_rfl) i le_rfl
end Cinch
-- Euler grading
local notation "Aτ"=> allIndex M.guard I
def clock (P:SplitP I) (E:Type)[AddCommGroup E][Module ℂ E]: Linear ( I→E ) ( I→ E ):= {
   toFun x i:=(P.grade i:ℂ) • x i,
   map_add' _ _:= funext fun _=> smul_add ..
   map_smul' z _:= funext fun _=> smul_comm _ z _ }
local notation "Aχ"=> clock P E
lemma cloak (b:I→E)(i:I): (Aχ) b i=( P.grade i:ℂ ) • b i:= rfl
lemma turn_clock (M:Actors E): Cinch P M ( clock P E ):= by
   constructor
   · exact ⟨fun h i he=>by rw [cloak,cloak,h i he]⟩
   · funext i; rw [cloak]; by_cases h:i=P.origin; · rw [ h,( P.zeroC _ ).mpr rfl,Nat.cast_zero,zero_smul ]; rfl -- smul_zero
     rw [ show (M.stack P).unit i=0 from if_neg h, smul_zero ]; rfl
   · exact fun {x} h=> (universe0 M.guard).mpr fun i=> M.guard.smul_mem _ ( h i (Set.mem_univ _) )
   intro x y; funext i; change (P.grade i:ℂ) • (∑ j∈ P.pieces i, M.core _ _)= (P.Lift M.core _ _ _) + P.Lift M.core _ _ _; simp_rw [P.loan,cloak, map_smul,LinearMap.smul_apply, Finset.smul_sum, ← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [ ← add_smul, ← Nat.cast_add, P.pays hj ]
lemma tick0 (b:I→E): Happy P (clock P E b):= by unfold Happy; rw [ cloak, ( P.zeroC _ ).mpr rfl,Nat.cast_zero,zero_smul ]
lemma tick_agree (V:Actors E){u:I→E} {x y:I→ E}(hu:Happy P u)(hv:x P.origin=y P.origin)(he: clock P E x= P.Lift V.core u x)(hf:clock P E y=P.Lift V.core u y): x=y:= by
   funext i; induction hr:P.grade i using Nat.strong_induction_on generalizing i with
   | h b ib=>
      by_cases hm:b=0; · rw [(P.zeroC i).mp (hr.trans hm),hv]
      obtain hp:(b:ℂ)≠0:= by exact_mod_cast hm
      apply (IsUnit.smul_left_cancel ( isUnit_iff_ne_zero.mpr hp )).mp; rw [← hr,← cloak,← cloak,he,hf]; apply Finset.sum_congr rfl; intro j hj; by_cases hx:P.grade j.2 < b; rw [ib _ hx j.2 rfl]; obtain hz:= P.pays hj; rw [show j.1=P.origin from ( P.zeroC _ ).mp (by omega),( show u P.origin=0 from hu ),map_zero,LinearMap.zero_apply,LinearMap.zero_apply] -- smul lemmas
-- exponential. guarantee Happy. Use Euler not associator count.
variable {P}{x y:I→E}
include M
lemma cheer_a (he: x∈ Aτ)(hz:y∈ Aτ)(hp:Happy P x)(hq:Happy P y): (M.Cheer P ( x+y )) = ( M.Cheer P x ) ⋆ (M.Cheer P y) := by
    let U(t:I→E):= M.Cheer P t; let u:= clock P E (x+y); let w:= turn_clock P M; have hs:Happy P ( x+y ):= by unfold Happy at *; simp only [Pi.add_apply,hp,hq,zero_add]
    apply tick_agree P M ( tick0 P ( x+y ) ); · change M.Cheer P ( x+y ) _= P.Lift M.core _ _ _; rw [P.loan,P.home,Stencil.simple_E M _ _ hs]; simp [Stencil.simple_E M x _ hp,Stencil.simple_E M y _ hq,M.identityR ]
    · exact w.idea ( ( Aτ ).add_mem he hz ) hs
    rw [ w.earns,w.idea he hp,w.idea hz hq ]; change ( Aχ x ⋆ U x ) ⋆ U y+ U x ⋆ ( Aχ y ⋆ U y )=( _ ⋆ _ ); rw [map_add,map_add, LinearMap.add_apply, ( Mτ ).star_a ( Aχ x ), Dynamics.mmc (M:=Mτ) (c:=U x) (p:=Aχ y) ( Cinch.totalZ he ) (w.earn hz) ] -- implicit hhP required?
end YM.MS.Swirl
