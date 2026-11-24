import YM.MS.Puff.Heat
import YangMills.WilsonProof.NativeSupport.YM.MS.Puff.Subsets
/-!
# Packing subsets into a moment

Define remembered moment as exponent with unit. Useful identity to express singleton raw seed =>
bare product (any reorder at scalar endpoint). Probe morphism specializes to point/scalar etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff
open Set Filter Function Finset MeasureTheory Real
open Koszul Book Book.Convolve Actors Engine Dynamics
open scoped Topology ContDiff Interval
variable {I W E F : Type}[ AddCommGroup E][Module ℂ E][AddCommGroup F][Module ℂ F]
    {M:Actors E}{T:Actors F}(P:SplitP I){V:Linear E F}
structure Tether (V:Linear E F)(M:Actors E)(T:Actors F): Prop where
    unit : V M.unit=T.unit
    craft (x y:E): V (M.core x y)= T.core (V x) (V y)
namespace Tether
variable (h:Tether V M T)
include h
lemma Extrapolation : Tether (pointL I V) (M.stack P) (T.stack P):= by
    refine ⟨ funext fun i=>?_, fun x y=> funext fun i=>?_⟩; · change V (P.refineV _ _) = P.refineV _ _; unfold SplitP.refineV; split; exact h.unit; exact map_zero ..
    change V ( P.Lift M.core _ _ _ )=_; rw [ (P).loan, map_sum ]; exact Finset.sum_congr rfl fun i hi=> h.craft (x i.1) (y i.2)
lemma powerV (i:ℕ)(x:E): V ( M.power x i )= T.power (V x) i:= by induction i with| zero=>exact h.unit| succ i ih=> rw [power,power,h.craft, ih]
lemma wageV (i:ℕ)(x:E): V ( M.wages x i)=T.wages (V x) i:= by unfold wages; rw [ map_smul,h.powerV ]
lemma cheersV (i:ℕ)(x:E): V ( M.cheers x i)=T.cheers (V x) i:= by unfold cheers; rw [map_sum]; exact Finset.sum_congr rfl (fun _ _=> h.wageV ..)
lemma figure (x:I→E)(i:I): V ( M.Cheer P x i )= T.Cheer P (V∘ x) i:= congr_fun (( h.Extrapolation P ).cheersV ( P.grade i ) x ) i
end Tether
variable [DecidableEq W]
-- tagged moment
namespace Stencil
open SplitP
variable (M:Actors E){F:Finset W→E}
local notation "P"=> marked W
local notation "T"=> M.stack (marked W)
local infixl:70 " ⋆ "=> M.core
lemma spare {p:Finset W} (h:p.Nonempty): (T).wages F 0 p=0:= by rw [Dynamics.firstW]; change _root_.YM.MS.Puff.SplitP.refineV P _ _ = _; unfold SplitP.refineV; rw [if_neg (show p ≠ (P).origin from h.ne_empty)]
lemma simple_E (F:I→E)(B:SplitP I)(_hv:Happy B F): Cheer M B F B.origin=M.unit:= by unfold Cheer cheers; rw [ ( B.zeroC B.origin ).mpr rfl ]; simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Dynamics.firstW]; change B.refineV M.unit B.origin=_; unfold SplitP.refineV; rw [if_pos rfl]
lemma pay0 {w:W} {f:Finset W→ E} (u: Finset W)(h:w∉u)(hp:∀ u:Finset W,u.card≠1→ F u=0) : (∑ i∈ subs u, F (insert w i.1) ⋆ f i.2)= F {w} ⋆ f u:= by
   rw [ sumS (fun a b=>F (insert w a) ⋆ f b) u, Finset.sum_eq_single_of_mem ∅ (Finset.empty_mem_powerset _) ]; · simp
   intro a ha he; rw [ hp (insert w a) ?_,map_zero,LinearMap.zero_apply ]; rw [ Finset.card_insert_of_notMem (fun p=>h ( ( Finset.mem_powerset.mp ha ) p )) ]; obtain hz:= Finset.card_pos.mpr ( Finset.nonempty_iff_ne_empty.mpr he ); omega
variable (hx:∀ p,F p∈M.guard)(hp:∀ u:Finset W,u.card≠1→ F u=0)
include hx hp
lemma wagt (p:Finset W)(i:W)(he:i∉p)(j:ℕ): (T).wages F (j+1) (insert i p) = F {i} ⋆ ( (T).wages F j p ):= by
   let t:=F {i}; let T':=insert i p; have ht u (k:ℕ)(l:Finset W): F u ⋆ (t ⋆ ((T).wages F k l))=t ⋆ ( F u ⋆ ((T).wages F k l)):= mmc ( hx u ) (hx {i}) _; induction j generalizing p with
   | zero=>
      rw [ nextW (M:=T) (n:=0),Pi.smul_apply,firstW,(T).identityR,Nat.cast_zero, zero_add, inv_one, one_smul ]; by_cases h:p.Nonempty
      · have hv:=hp (insert i p) (by rw [ Finset.card_insert_of_notMem he ]; obtain hv:=Finset.card_pos.mpr h; omega); rw [hv, show (T).unit p=0 from Eq.trans (congr_fun firstW p).symm (spare M h ( F:=F )),map_zero]
      rw [ Finset.not_nonempty_iff_eq_empty.mp h, show insert i (∅:Finset W)={i} from rfl]; unfold Actors.stack; dsimp only; rw [ SplitP.refineV,if_pos (show (∅:Finset W)=(P).origin from rfl), M.identityR ]
   | succ j ih=>
      rw [ nextW (M:=T) (n:=j+1), Pi.smul_apply ]; change _ • (∑ x∈ subs (insert i p), _)= _; rw [ ins he (fun a b=> F a ⋆ ((T).wages F (j+1) b)), pay0 M p he hp ];
      have hz : (∑ x ∈subs p,F x.1 ⋆ ((T).wages F ( j+1 ) (insert i x.2)))=t ⋆ (( (T).core F ((T).wages F j) ) p) := by change _ = t ⋆ ((P).Lift M.core _ _ _); rw [ (P).loan,map_sum]; exact Finset.sum_congr rfl fun r hr=> (congr_arg ( F r.1 ⋆ · ) ( ih r.2 (fun v=> he ( ( cards.mp (( P).sym.mp hr ) ).1 v ) ) ) ).trans (ht r.1 j r.2)
      rw [ hz,nextNF (M:=T) j, Pi.smul_apply,map_smul, inv_smul_eq_iff₀ ( zeroN' (j+1) ) ]; push_cast; module
lemma cheers (S: Finset W)(w:W)(he:w∉S) : M.Cheer P F (insert w S) =F {w} ⋆ M.Cheer P F S:= by
   unfold Cheer Actors.cheers; simp only [ Finset.sum_apply, show ∀ p:Finset W,(P).grade p=p.card from fun _=>rfl,Finset.card_insert_of_notMem he ]; -- unfold M algebra! ptype
   rw [ Finset.sum_range_succ', spare M (Finset.insert_nonempty ..), add_zero, map_sum ]; exact Finset.sum_congr rfl fun i _=> wagt M hx hp S w he i
end Stencil
end YM.MS.Puff
