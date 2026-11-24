import YM.SignedWilsonExpansion.F9.Coliphon
/-!
# Price every coefficient through booked orders by the same stories

Using nearby sampled rooms and *positioned* customer's stocks.Virt.Step πT budget across,
including when only coordinate prepared.Just assessed (Cost).For `Faculty`
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 550000
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
variable {W K} {a:Finset Query}{F:Labels.Frame G d}{U:ι→ StaffG G d}{z:ι→ InkQ}{Y:ι→magazine G d}
local notation "XY"=> Measure.start W K d
variable (P:Faculty W K F U z Y L q a k) {X:ι→ Sec G d→ₗ[ℂ] Labels.Label G d}
lemma duo (h:Maxer L q){E:Type*}[AddCommGroup E][Module ℂ E](P:ι→Fin 2→ E)(u:Across L q ℂ (fun j=> P j 0))(v:Across L q ℂ (fun j=> P j 1)): ∀ i:Fin 2,Across L q ℂ (fun j=> P j i):=by intro i; fin_cases i <;> assumption
include P h M
lemma adjustT (w:6≤d)(t:Axis)(hp: Query.crew h T S W K M t d w ⊆ a) (v:Before L (l+1) P)(v0:l<k)(p:P.NoteS X): Before L (l+1+1) P:=by
    let L':= Query.crew h T S W K M t d w; let x:= Query.anchor t; have hx:=P.allowed; have hw:x∈a:= hp (Finset.mem_insert_self ..); obtain ⟨u,H⟩:= P.projection_t M w (fun x b=> hp ( Finset.mem_insert_of_mem b )) v v0 p; let z'(i:ι):= U i (l+1) ∘ₗ X i; let D (i:ι):= U i (l+1)
    refine ⟨fun i u'=>?_ , fun a' u'=>?_⟩
    · exact if h : i=l+1 then h.symm ▸ u else v.zen i (by omega)
    by_cases zz:a'=l+1; swap; · exact v.older a' (by omega)
    subst a';   -- inspect
    apply Across.actEnough hx F.basis D; intro i'; let a':= F.basis i'; let Y'(i:ι)(e:ℕ):Gram.BI (Normalize.Sec G d):= Y i x e; let T'(i:ι):= U i 0 a'; let V(i:ι):= D i a'; have hB:Knows L q Y' 1:= P.mem_book x; have hv':Across L q ℂ T':= Across.linearAt P.allowed (v.older 0 (by omega)) (Across.solid _)
    apply gram_lock t (fun i=> Y' i 0) (fun i=>P.hook (h:=h) M t i) P.allowed V; intro t'; let K(i:ι): Fin 2→ Labels.Label G d:=![a',X i t']; let u'(i:ι)(v:ℕ):= U i v ∘ K i; let A(i'):ℂ:= earCost U x z Y (l+1) i' (K i') -- `z` shadow
    have H₀(i):u' i 0 1= U i 0 (X i t'):=rfl; have he : Billed L q A:= P.auditions v x hw v0 K (duo hx K (Across.solid _) (Across.linearAt P.allowed p.ledger (Across.solid _)))
    have h₁:Across L q ℂ (fun i=> z' i t'):= Across.linearAt hx H (Across.solid _); let P₁(i): Fin 2→ Sec G d:=![T' i,t']; let P₂(i): Fin 2→ Sec G d:=![T' i,z' i t']; have hv:= paidSlots hx hB (le_refl 1) P₁ (duo hx P₁ hv' (Across.solid _)); have hp':= paidSlots hx hB (show 0≤1 from (by omega)) P₂ (duo hx P₂ hv' h₁); refine Billed.via (Billed.diff hx he (Billed.add hx (Billed.mul hx u hv) hp')) ?_; filter_upwards [p.receive] with i he
    unfold A earCost; have hF:u' i 0= P₁ i:= by ext1 c; fin_cases c; rfl; exact he _
    let f(i':Fin 2):=Y' i 0 (update (P₁ i) i' ((U i (l+1)) (K i i'))); let C:= coeff (l+1) (z i)*Y' i 1 (P₁ i); rw [show (U i 0 ∘ K i)=P₁ i from hF]; change _= C+(∑ v:Fin 2,f v) - (C+Y' i 0 (P₂ i)); rw [Fin.sum_univ_two f]; rw [show f 0=Y' i 0 ![V i,t'] from (congr_arg _ (Gram.swap0 (T' i) t' (V i))), show f 1= Y' i 0 (P₂ i) from (congr_arg _ (Gram.swap1 (T' i) t' (z' i t')))]; abel
lemma defined_first (a':Axis)(u:Query.anchor a'∈ a): Before L 1 P:=by
    refine ⟨fun j v=>?_, fun j v=>?_⟩
    · rw [show j=0 by omega]; simp_rw [coeff_zero_eq_constantCoeff_apply,P.param]; exact Billed.const _
    rw [show j=0 by omega]; exact P.firstQ (h:=h) M a' u
lemma seasonal (w:6≤d)(t:Axis)(u:Query.crew h T S W K M t d w ⊆ a)(p:P.NoteS X) : Before L (k+1) P:=by
    suffices H' : ∀ i≤k,Before L (i+1) P from H' k le_rfl; intro i v; induction i with
    | zero=> exact defined_first h T S M P t (u (Finset.mem_insert_self ..))
    | succ i ih=> exact P.adjustT h T S M w t u (ih (by omega)) v p -- order
end Faculty
end YM.SignedWilsonExpansion.Commission.Method
