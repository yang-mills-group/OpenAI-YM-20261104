import YM.FVA2.Speed.Cells
import YM.FVA2.XReg.Sight
/-!
# Propagate order-by-order power savings through the frame solve

It's on the `Resin` data. See `controller` using the actual near-free
hypotheses, `Speed/Hearth` for obtaining the bounds for the concrete
postings. No need to use uniform estimates prior to the posting/reset.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Speed
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries
open Normalize.Fray Reg Reg.Point Reg.Unique CoverTest Photo Higher
open scoped Topology ContDiff BigOperators Classical
open Speed.Star Asymptotics Finset
variable {I:Type*}{F:Filter I}{G:Gauge}{d n:ℕ}
local notation "Z"=> XSpace.Structure1.Point G d n
local notation "L"=> guide G d
variable {τ:I→Mesh}(h:Stretched F τ)
abbrev FFrame (F:Filter I)(τ:I→Mesh)(x:I→Pick G d)(b:Pick G d):= ∀ k:ℕ, Fast F τ (fun i=>guide G d ( x i k )) (fun _=>guide G d (b k))
abbrev NPoints (F:Filter I)(τ:I→Mesh)(x y:I→ℕ→Structure1.Point G d n):=∀ k (p:Tags G d n), Sharp F τ (fun i=>x i k p) (fun i=> y i k p)
include h
lemma process {x: I→ Sec G d}{p:Sec G d} (hP:Fast F τ (fun i=> tableD G d ( x i )) ( fun _=> tableD G d p )) (q:Toon G d): Fast F τ (fun i=> (Daylight ( Press.portDeck G ) d ).repr ( x i ) q) (fun _=> ( Daylight (Press.portDeck G) d ).repr p q):= by
    let B:=Daylight (Press.portDeck G) d; let U : RSpace G d →ₗ[ℝ] ℂ:= (( B.coord q ).restrictScalars ℝ) ∘ₗ (tableD G d).symm.toLinearMap
    have he(p:Sec G d): B.repr p q= U ( tableD G d p ):= by simp only [ U,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply ]; rfl
    change Fast F τ (fun i=> B.repr (x i) q) (fun _=> B.repr p q); simp_rw [he]; exact Fast.constant (w:=LinearMap.toContinuousLinearMap U ) h ( LinearMap.toContinuousLinearMap U ).differentiableAt hP -- notation extra args?
lemma prices {x:I→Pick G d}{u:Pick G d}(hp:FFrame F τ x u) (p:Sec G d) (n:ℕ): Fast F τ (fun i=> tableD G d ( coeff n ( deck (x i) ) p )) (fun _=> tableD G d ( coeff n (deck u) p )):= by
    let D : MoveSpace G d →ₗ[ℝ] RSpace G d:= { toFun s:= tableD G d (((guide G d).symm s).val p), map_add' s t:=by rw [map_add]; exact map_add (tableD G d) _ _, map_smul' s t:=by rw [map_smul]; exact map_smul (tableD G d) _ _ }
    have he (t:Normalize.Change G d): tableD G d (t.val p)= D (guide G d t):=by simp [D]
    simp_rw [ decked,pulling ]; split_ifs with hc; · simp_rw [ stood,map_add,he ]; exact Fast.add ( Fast.refl F τ (fun _=> tableD G d p) ) ( Fast.constant (w:=LinearMap.toContinuousLinearMap D) h ( LinearMap.toContinuousLinearMap D ).differentiableAt (hp n) )
    simp_rw [ he ]; exact Fast.constant (w:=LinearMap.toContinuousLinearMap D) h ( LinearMap.toContinuousLinearMap D ).differentiableAt (hp n)
lemma paints (w:I→Pick G d)(v:Pick G d)(hp:FFrame F τ w v) (x y:I→ℕ→Structure1.Point G d n)(he:NPoints F τ x y): NPoints F τ (fun i=> status (deck ( w i )) (x i)) (fun i=>status (deck v) (y i)):= by
    intro k p; simp_rw [seen, stencil_he ( x _ _ ) ( pulseU _ _ _ ), stencil_he ( y _ _ ) (pulseU _ _ _),sift ]; -- sum
    apply Sharp.sum; intro l hl; apply Sharp.sum; intro j _; refine Sharp.mul h (Sharp.prod _ h ?_) ( he _ _ ); intro i _; exact Sharp.above (process h (p:=coeff ( l ( some i ) ) ( deck v ) (p i)) ( prices h hp (p i) _ ) (j i) )
lemma satisfies (u:I→ Pick G d)(v:Pick G d)(hp:FFrame F τ u v)(x y:I→Reports G d)(he:Resin F τ x y): Resin F τ (fun i=> realm (deck (u i)) (x i)) (fun i=> realm (deck v) (y i)):= by intro k n t p; simp_rw [ ← restT ]; exact paints h u v hp (fun i j=> x i j n t) (fun i j=> y i j n t) (fun k p=> he k n t p) k p
variable {T: Screen G d} (D: Fray T)(H:T.Prepared) (P: Reports G d)(x:I→Reports G d)
lemma pension (hp:Resin F τ x (fun _=> P)) : HasAll F x P:= fun k n t p=> Fast.aims h _ ( hp k n t p ).sails
omit h in
lemma price (hp:Resin F τ x (fun _=> P)): Fast F τ (fun i=> D.purse (x i 0)) (fun _=> D.purse (P 0)):= isBigO_pi.mpr fun _=> isBigO_pi.mpr fun _=> ( hp 0 _ _ _ ).sails
local notation "Gζ"=> FFrame F τ
local notation "Θ"=> Formulas
variable (hP: P 0=reference G d) (hp:Resin F τ x (fun _=> P))
include hp hP
lemma fired : Fast F τ (fun i=> guide G d ( Lays D H (x i) 0)) (fun _=> guide G d ( Lays D H P 0 )):= by
    simp_rw [leads,guid]; have he:= price D P x hp; rw [ hP ] at he ⊢; exact Fast.constant h ( ( Fray.train D H ).differentiableAt (by simp) ) he
local notation "U"=> MoveSpace G d
set_option maxHeartbeats 350000 in
lemma controller : FFrame F τ (fun i=> Lays D H ( x i )) (Lays D H P):= by
    intro k; let Zc i:= Lays D H (x i);
    let t (p:Reports G d):= ( D.purse ( p 0 ), L ( Lays D H p 0 ) ); let f(p:Prediction G d):= L ( -( T.D p ) ); let X2(p:D.At):= (D.delta p).inverse;
    have h0 : t P=D.opening:= by unfold t opening; rw [ compass D H hP,hP,map_zero]; -- $
    have hm:= Fast.pair ( price D P x hp ) ( fired h D H P x hP hp ); change Fast F τ ( t ∘ x ) (fun i=> t P) at hm; rw [h0] at hm;
    have hZ: DifferentiableAt ℝ X2 D.opening:= by apply DifferentiableAt.comp D.opening ( (D.pin_inv H).contDiffAt_map_inverse (n:=1)|>.differentiableAt (by simp) ); unfold delta; exact ContDiff.differentiable (n:=1) ((D.fair.fderiv_right (by simp)).clm_comp contDiff_const) (by simp) D.opening -- check args
    have hN:FFrame F τ (fun i=> Lays D H (x i)) (Lays D H P):= by -- same goal recursion pattern wrong use strong_induction.Clean
       intro k; induction k using Nat.strong_induction_on with| h k ih=>
        by_cases hv:k=0; · subst k; exact fired h D H P x hP hp
        let C (i:I):= Screen.blind (Zc i) k; let A(i:I):= realm (deck (C i)) (x i); let Zp:= Lays D H P; let B:= realm (deck ( Screen.blind Zp k )) P
        have ht : FFrame F τ C (Screen.blind Zp k):= by
           intro n; by_cases ht:n<k; · simp_rw [C,Screen.blind_low _ _ n ht]; exact ih _ ht
           unfold C Screen.blind; simp only [ht, ↓reduceIte]; exact Fast.refl F τ _
        have hh: Bills F τ (fun i=> A i k) (fun i=> B k):= satisfies h _ _ ht _ _ hp k -- inference under A etc.
        have hT : Fast F τ (fun i=> f (A i k)) (fun i=> f (B k)):= by
           have he(p:Prediction G d): f p= -(D.stamps (fun i=> watch (D.scope i) p)):= by unfold f; rw [map_neg,crux]
           simp_rw [he]; apply Fast.neg; refine Fast.constant ( w:=D.stamps ) h D.stamps.differentiableAt ?_; exact isBigO_pi.mpr fun i=> ( hh _ _ _ ).sails
        have ha:= Fast.pair (Fast.constant h hZ hm) hT; have hx: Fast F τ (fun i=> X2 (t (x i)) (f (A i k))) (fun i=> X2 D.opening (f ( B k ))) := Fast.constant (w:=fun i:(U→L[ℝ]U)× U=> i.1 i.2) h (differentiableAt_fst.clm_apply differentiableAt_snd) ha
        have he:= cost_est D P hP x ( pension h P x hp ); refine Fast.tee hx ?_ ( Eventually.of_forall fun i=>?_ ); -- left eventual, right slope. static slope at f.B.Per n.
        · filter_upwards [(D.happy H he), show ∀ᶠ i in F,(D.delta (t (x i))).IsInvertible from (Fast.aims h _ hm).eventually ( D.unhit H )] with i hi hh; apply hh.inverse_apply_eq.mpr; unfold t; rw [D.order, align,LinearEquiv.symm_apply_apply,T.bare_price (R:=x i) (T:=Zc i) hv hi.2.1]
        have hz:= T.bare_price (T:=Zp) (l:=k) P hv (force_title D H P hP).2.1; have ht': Zp 0=0:= compass D H hP; rw [ht',hP, XSpace.Normalize.regular T H] at hz; change X2 D.opening (f ( B k ))= L ( Zp k ); rw [hz]; unfold X2; rw [D.unpin H, (show ContinuousLinearMap.inverse (1:U→L[ℝ]U)=1 from ContinuousLinearMap.inverse_equiv (.refl ℝ _))]; rfl -- order orientation
    exact hN k
end YM.FVA2.Speed
