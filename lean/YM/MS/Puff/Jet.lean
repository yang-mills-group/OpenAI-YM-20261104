import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.Ring
/-!
# The OP-version of heat equation

Abstract lifts through index pieces. In particular algebraic for ∆(F⋄F) relations;
when one of the terms is a Volterra multiplier these formulas still work.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset MeasureTheory Real
open Koszul Book Book.Convolve
open scoped Topology ContDiff Interval
variable {I F E J: Type} [AddCommGroup E][Module ℂ E]
variable (P:SplitP I)(M:Actors E)
abbrev Angled (E : Type)[AddCommGroup E][Module ℂ E]:= Bil E E E
local infix:70 " ⋆ "=> M.core
structure Engine (M:Actors E) where
    move : Linear E E
    stays (f:E): f∈M.guard→ move f ∈ M.guard
    unitLaw : move M.unit=0
    join : Angled E
    compatibility (f h:E): f∈ M.guard→h∈ M.guard→ move ( M.core f h )=M.core ( move f ) h + M.core f ( move h ) + join f h
    leib (f g h:E): f∈M.guard→ g∈M.guard→ h∈ M.guard → join f ( M.core g h )= M.core (join f g) h + M.core g (join f h)
variable {M}
namespace Engine
variable (V:Engine M) {f g r:E}
lemma join_close (h:f∈M.guard)(he:g∈M.guard): V.join f g∈M.guard:= by rw [ ( show V.join f g= V.move ( f ⋆ g ) - ( V.move f ⋆ g + f ⋆ V.move g ) from (by rw [V.compatibility f g h he]; abel) ) ]; exact M.guard.sub_mem ( V.stays _ ( M.close f h g he )) (M.guard.add_mem ( M.close _ (V.stays _ h) g he) ( M.close _ h _ ( V.stays _ he ) ))
lemma rear (h:f∈M.guard)(hv:g∈M.guard): V.join f g=V.join g f:= by obtain he:= V.compatibility f g h hv; rw [M.turns _ h _ hv,V.compatibility g f hv h, M.turns (V.move g) ( V.stays g hv ) _ h,M.turns g hv _ ( V.stays f h)] at he; linear_combination (norm:=abel) -he
lemma stopu (hp:g∈M.guard): V.join M.unit g= 0:= by obtain he:= V.compatibility _ g M.holds hp; rw [V.unitLaw,M.identityK,M.identityK,map_zero,LinearMap.zero_apply,zero_add] at he; exact ( add_right_inj (V.move g) )|>.mp (by rw [ add_zero ]; exact he.symm ) -- name
lemma simple (h:f∈M.guard): V.join f M.unit=0:= by rw [ V.rear h M.holds,V.stopu h ]
lemma opposite (hf:f∈ M.guard)(hg:g∈ M.guard)(hr:r∈ M.guard): V.join ( f ⋆ g ) r = V.join f r ⋆ g + f ⋆ V.join g r:= by rw [V.rear (M.close _ hf _ hg) hr,V.leib _ _ _ hr hf hg,V.rear hf hr,V.rear hg hr] -- placeholder arguments

def witness : Angled E:= V.join
abbrev pointL (I:Type)[AddCommGroup J][ Module ℂ J ] (L:Linear E J): Linear ( I→E ) (I→J):= {
  toFun x i:=L (x i)
  map_add' _ _:= funext fun _=>map_add ..
  map_smul' _ _:= funext fun _=>map_smul .. }
lemma index_prod (U: I→E)(H: I→E)(he:∀ i,U i ∈ M.guard)(hp:∀ i,H i∈ M.guard): pointL I V.move (P.Lift M.core U H)= P.Lift M.core (pointL I V.move U) H+P.Lift M.core U (pointL I V.move H)+P.Lift V.join U H:= by
    funext i; change V.move _= ( P.Lift M.core (pointL I V.move U) H i + P.Lift M.core U (pointL I V.move H) i ) + _; simp_rw [P.loan,map_sum,V.compatibility _ _ (he _) (hp _), Finset.sum_add_distrib]; rfl
lemma rewrap (E:Type)[AddCommGroup E](f:I→I→I→E)(x:I): (∑ i∈P.pieces x,∑ j∈P.pieces i.2,f i.1 j.1 j.2)=∑ i∈P.pieces x,∑ j∈P.pieces i.2,f j.1 i.1 j.2:= by
   -- use also generalized sum comm
   rw [P.trip E _ f,P.trip E _ (fun i j k=>f j i k)]; exact Finset.sum_congr rfl fun i _=> P.also (fun s t=>f s t i.2) i.1
lemma index_leib (u v w:I→E)(hx:∀ i,u i∈M.guard)(hy:∀ i,v i∈M.guard)(hw:∀ i,w i∈M.guard): P.Lift V.join u ( P.Lift M.core v w )= P.Lift M.core ( P.Lift V.join u v ) w+P.Lift M.core v ( P.Lift V.join u w ):= by
   funext i; simp_rw [ Pi.add_apply,P.loan,map_sum,V.leib _ _ _ (hx _) ( hy _ ) (hw _),Finset.sum_add_distrib, LinearMap.sum_apply ]; refine congr_arg₂ (·+·) (P.trip E i (fun x y z=> M.core ( V.join (u x) (v y) ) ( w z ))) ( rewrap P E (fun x y z=> M.core ( v y ) (V.join ( u x ) ( w z ) )) i )
lemma unit0 : pointL I V.move ( P.refineV M.unit )=0:= by
    classical
    funext i; change V.move (P.refineV M.unit i)=_; unfold SplitP.refineV; split; exact V.unitLaw; exact map_zero ..
-- stacking later on t-indexed fields (compare $ready within lift.Stay). Keep k independent of I.
def liftV : Engine (M.stack P):={
    move:= pointL I V.move, join:=P.Lift V.join
    unitLaw:=V.unit0 P
    stays:=fun _ h=> (universe0 _).mpr fun i=> V.stays _ (h i (Set.mem_univ _))
    compatibility:=fun x y h hw=> V.index_prod P x y ((universe0 _).mp h) ( (universe0 _).mp hw )
    leib f g k hp hg hk:= V.index_leib P f g k ( (universe0 _).mp hp ) ( (universe0 _).mp hg ) ( (universe0 _).mp hk ) }
-- often need `bulk + linear-lonely(B,F)` as engine. compatibility immediate.
def augment (F:E)(h:F∈ M.guard) : Engine M:={
   move:= V.move + V.join F
   unitLaw:= by rw [ LinearMap.add_apply,V.unitLaw,V.simple h, add_zero ]
   join:= V.join
   stays:= fun u he=> M.guard.add_mem (V.stays u he) ( V.join_close h he )
   compatibility f g hf hg:= by simp only [LinearMap.add_apply,map_add,LinearMap.add_apply,V.compatibility _ _ hf hg,V.leib _ _ _ h hf hg]; abel
   leib:=V.leib }
end Engine
end YM.MS.Puff
