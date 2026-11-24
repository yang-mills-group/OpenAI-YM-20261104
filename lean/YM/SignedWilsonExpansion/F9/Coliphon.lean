import YM.SignedWilsonExpansion.F9.Faculty
/-!
# New-order polynomial bound from top-Step Commitment resources.Faculty

All camera sites in actual `crew`; dual evaluations via finite witnesses.Frame including cap zero.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 445000
namespace YM.SignedWilsonExpansion.Commission.Method
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes Jury Reg
open scoped Topology ContDiff BigOperators Classical
open WilsonCoeffUV.Mer.Xa
open Stair Tape RateQ
variable {G:Gauge}{n d k e j l:ℕ} {ι:Type} {L:Filter ι}{q:ι→ℝ}
variable (h:G.Simple)(T:MS_Data G (Position.OpenAxis.Plot (FVA2.Press.portDeck G)))(S:Prescription ( FVA2.Press.portDeck G)) (W:Initialize G){P':Normalize.Store G}(K:Rose.Pick P') (M:Scale.System.Contract W K T S)
namespace Faculty
variable {W K h T S} {a:Finset Query}{F:Labels.Frame G d}{U:ι→ StaffG G d}{z:ι→ InkQ}{Y:ι→magazine G d}
local notation "XY"=> Measure.start W K d
variable (P:Faculty W K F U z Y L q a k) {X:ι→ Sec G d→ₗ[ℂ] Labels.Label G d}
include P
abbrev outfit (P:Faculty W K F U z Y L q a k)(x:Query)(v:ι→ Fin x.1 → Labels.Label G d)(i:ι) := (fun j=> Tape.spur (U i) (v i j))
lemma mem_book (x:Query): Knows L q (fun i=> Y i x) l:= fun j p t=> Billed.tens ( P.reads x j t )
omit P in
def earCost (U:ι→StaffG G d)(x:Query)(z:ι→ InkQ)(Y:ι→ magazine G d)(l:ℕ)(i:ι)(v: Fin x.1→ Labels.Label G d): ℂ:= (coeff l (z i))*Y i x 1 (U i 0 ∘ v)+ ∑ j,Y i x 0 (update (U i 0 ∘ v) j (U i l (v j)))
-- spent in running induction below.Cap:
structure Before (l:Filter ι)(i:ℕ)(P:Faculty W K F U z Y l q a k) : Prop where
    zen : ∀ j : ℕ,j< i → Billed l q (fun v=> coeff j (z v))
    older : ∀ j : ℕ,j< i → Across l q ℂ (fun v=> U v j)
variable (x:Query)
lemma auditions (v:Before L (l+1) P)(i:Query)(u:i∈a)(b:l< k)(p:ι→ Fin i.1→ Labels.Label G d)(s:∀ j,Across L q ℂ (fun i'=> p i' j)): Billed L q (fun j=> earCost U i z Y (l+1) j (p j)):=by
   let A(i':ι):= z i'-(coeff (l+1) (z i')) • ( PowerSeries.X^(l+1): InkQ ); let B(i':ι): Fin i.1→ Tape (Sec G d):= outfit P i p i'; let U'(i' :ι)(j:ℕ):=(if j=l+1 then 0 else U i' j); let D (a:ι)(j:Fin i.1):= Tape.spur (U' a) (p a j)
   have hA(i':ι)(j:ℕ): coeff j (A i')= (if j=l+1 then 0 else coeff j (z i')):=by
        unfold A; simp only [map_sub,map_smul,coeff_X_pow]; split_ifs with h; · rw [h]; simp
        simp
   have Hv(i':ι)(j m) : D i' j m=(if m=l+1 then 0 else B i' j m):=by unfold D Tape.spur U'; split_ifs; rfl; rfl
   have hZ(i:ι): constantCoeff (A i)=0:=by rw [← coeff_zero_eq_constantCoeff_apply,hA,if_neg (by omega),coeff_zero_eq_constantCoeff_apply,P.param]
   have hu:Costy L q A (l+1):=by
        intro i b; simp_rw [hA]; by_cases h : i=l+1; · simp_rw [if_pos h]; exact Billed.const _
        simp_rw [if_neg h]; exact v.zen i (by omega)
   have hx(i'): earCost U i z Y (l+1) i' (p i') = coeff (l+1) (exam (Tape.composed (Y i' i) (z i')) (fun _=> U i') (p i'))-coeff (l+1) (tabular (Tape.composed (Y i' i) (A i')) ( D i' )):=by
        change _= coeff (l+1) (tabular (Tape.composed (Y i' i) (z i')) (B i')) -_; rw [treads (P.param _) (hZ _) (fun j hj=> by rw [hA,if_neg (Nat.ne_of_lt hj)]) _ (B i') (D i') (by omega) (fun j m p=> by rw [Hv,if_neg (Nat.ne_of_lt p)]),topStep, show paused ( D i' )=(U i' 0 ∘ p i') from (funext fun j=>by unfold paused; rw [Hv,if_neg (by omega)]; rfl)]; rw [hA,if_pos rfl, sub_zero]; unfold earCost; refine congr_arg (_ + ·) (Finset.sum_congr rfl (fun j _=>?_)); rw [Hv,if_pos rfl,sub_zero]; rfl
   apply Billed.via (Billed.diff P.allowed (P.floors i u p s (l+1) b) (comp_bill P.allowed (P.mem_book i) A hu D ?_ (l+1) le_rfl)) (Eventually.of_forall hx); intro j m h; simp_rw [Hv]; by_cases u:m=l+1 <;> simp_rw [u] -- not good by cases
   · exact Across.solid _
   exact Across.linearAt P.allowed (v.older m (by omega)) (s j)
structure NoteS (P:Faculty W K F U z Y L q a k)(X:ι→ Sec G d→ₗ[ℂ] Labels.Label G d) : Prop where
    receive : ∀ᶠ i in L,∀ p, U i 0 (X i p)=p
    gifts : ∀ᶠ i in L, Gift (X i)
    ledger: Across L q ℂ X
include M
lemma projection_t (w:6≤d) (u : ( (Query.resident h T S W K M d w).image Sigma.fst )⊆ a) (v:Before L (l+1) P)(i:l<k)(p: NoteS P X) : Billed L q (fun i=> coeff (l+1) (z i))∧ Across L q ℂ (fun i=> U i (l+1) ∘ₗ X i):=by
    let f(i'):= U i' (l+1) ∘ₗ X i'; let V(i'):Change G d:= if h:f i'∈ Change G d then ⟨f i',h⟩ else 0; let Y'(i'):ℂ:= coeff (l+1) (z i'); let B(i'):TPoint G d:=(V i',(Y' i').re)
    have he(i'): (↑(Y' i').re:ℂ)= Y' i':= by obtain ⟨t,h⟩:= Complex.conj_eq_iff_real.mp (realLevel _ (P.natural i') (l+1)); unfold Y'; rw [h]; rfl
    have H:∀ᶠ i in L,(B i).1.val=f i:=by filter_upwards [p.gifts] with i h; have hx:f i∈ Change G d:= (h.calls ( show Trustee (U i (l+1)) 0 from (by simpa using P.blessed i (l+1)) ) ).member; change (V i).val=_; unfold V; rw [dif_pos hx]
    have hZ: Across L q ℝ B:=by
       apply Query.tangent_stock h T S W K M Y P.reads w P.allowed; intro i' t; let x:= i'.1; let y:= i'.2; let U' (i) := X i ∘ y; apply Billed.via (P.auditions v x (u (Finset.mem_image_of_mem Sigma.fst t)) i U' (fun j=> Across.linearAt P.allowed p.ledger (Across.solid _)))
       filter_upwards [p.receive,H] with i b z'; change ( (B i).2:ℂ )* _ + _= _; change ((↑(Y' i).re:ℂ)* Y i x 1 y+ ∑ j, Y i x 0 (update y j ((B i).1.val (y j))))=_; rw [he i,z']; unfold earCost; rw [show (U i 0 ∘ U' i)= y from funext fun j=> b _]; rfl
    constructor
    · exact Billed.via (Billed.ofRealB (hZ (LinearMap.snd ..))) (Eventually.of_forall (fun i=> (he i).symm ))
    have hK:Across L q ℝ (fun i=>(B i).1.val):=by let K:TPoint G d →ₗ[ℝ] Module.End ℂ (Sec G d):= (Change G d).subtype ∘ₗ (LinearMap.fst ..); exact Across.arrow (F:=Module.End ℂ (Sec G d)) hZ K
    letI : Module.Finite ℝ (Module.End ℂ (Sec G d)):=Module.Finite.trans ℂ _
    exact (Across.realComplex P.allowed (P:=fun i=>(B i).1.val) hK).via H
end Faculty
end YM.SignedWilsonExpansion.Commission.Method
