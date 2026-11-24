import YM.FVA2.Scale.Running
/-!
# Polynomial dependence of Check and MS frame flow at ALL orders

No powering comparisons presumed. Derive from polynomial shape dependence
from actual MS and Wilson identification. Even when arity varies, we can
pay differences through the REAL finite tangent mask because of genuine
NormStab (with H covariance). -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Reg.Token Reg.Unique Reg.Choice Facets Equator Measure Jury
namespace Rhythm
open Polynomial
variable {I:Type*}{f:ℝ→ℂ}
lemma prod {H:I→ℝ→ℂ}(s:Finset I)(h:∀ i∈s,Rhythm (H i)): Rhythm (fun t=>∏ j∈s, H j t):= by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact const _
    | insert i s hi ih=> simp only [Finset.prod_insert hi]; exact mul ( h i (Finset.mem_insert_self ..)) (ih fun j hj=> h _ ( Finset.mem_insert_of_mem hj ))
lemma star_h (h: Rhythm f): Rhythm (fun i=> (starRingEnd ℂ) (f i)):= by
    obtain ⟨p,rfl⟩:= from_poly.mp h; apply from_poly.mpr; refine ⟨ p.map (starRingEnd ℂ),funext fun i=>?_ ⟩; rw [ Polynomial.eval_map, ← Polynomial.eval₂_at_apply (starRingEnd ℂ), Complex.conj_ofReal ]
lemma re (h: Rhythm f): Rhythm (fun i=> ( ( f i ).re:ℂ )):= by simp_rw [Complex.re_eq_add_conj, div_eq_mul_inv]; exact mul (add h h.star_h) ( const _ )
lemma im (h: Rhythm f): Rhythm (fun i=> ( ( f i ).im:ℂ )):= by simp_rw [Complex.im_eq_sub_conj, div_eq_mul_inv]; exact mul (sub h h.star_h) ( const _ )
lemma axis (F:ℂ→ₗ[ℝ]ℂ) (h:Rhythm f) : Rhythm (fun i=> F (f i)):= by
    have hq (g:ℂ): F g=(g.re:ℂ)*F 1+(g.im:ℂ)*F Complex.I:= by
        conv_lhs=> rw [← Complex.re_add_im g, _root_.map_add]; lhs; rw [show (g.re:ℂ)= g.re • (1:ℂ) from by simp [Complex.real_smul], _root_.map_smul];
        rw [← Complex.real_smul, _root_.map_smul ]; rfl
    conv => arg 1; ext x; rw [hq]
    exact add (mul h.re (const _)) (mul h.im (const _))
lemma usage [ Fintype I ] (F:(I→ℂ)→ₗ[ℝ]ℂ) (p:ℝ→I→ℂ) (H:∀ i, Rhythm (fun t=> p t i)): Rhythm (fun i=> F ( p i )):= by
    let y (t:I):=(LinearMap.single (R:=ℝ) (φ:=fun _:I=>ℂ) t); -- name
    have he (t:I→ℂ): t=∑ i, y i (t i):= by ext i; simp only [Finset.sum_apply]; exact (Fintype.sum_pi_single ..).symm
    have hh(t:I→ℂ): F t=∑ i:I,F (y i (t i)):= by rw [← _root_.map_sum]; exact congr_arg F (he t)
    -- conv to replace only once
    conv => arg 1; ext i; rw [hh]
    exact Rhythm.sum _ (fun i _=> axis (F ∘ₗ y i) ( H i ))
-- linear map END interpretation. P.light
end Rhythm
namespace Meter
variable {G:Gauge}{d n:ℕ}
abbrev Clear (T:ℝ→Cn): Prop:= Pace.formal (fun (_:Unit) t=> T t)
def Tracks (F:ℝ→ Guard G d) (k:ℕ): Prop:= ∀ p: Sec G d,∀ v: Sec G d→ₗ[ℂ] ℂ, Rhythm (fun t=> v (coeff k (F t) p))
variable (h:G.Simple)
local notation "E"=> XSpace.Normalize.Change G d
include h
private abbrev Pot (G:Gauge)(d:ℕ):= Σ n:ℕ,(Stage n × Tags G d n)
local notation "K"=> Pot G d
private def Look (p:Pot G d) : XSpace.Normalize.Change G d →ₗ[ℝ] ℂ := ( ( Manifest.response p.2.1 p.2.2 ).restrictScalars ℝ ) ∘ₗ ( XSpace.Normalize.Change G d ).subtype
-- Forecast.finalists variant
private theorem determining (d:ℕ): ∃ (J:Finset (Pot G d)), LinearMap.ker ( LinearMap.pi (fun i:J=> Look i.val))=⊥:= by
    let U (s:Finset (Pot G d)):= LinearMap.ker (LinearMap.pi fun i:s=> Look i.val); have he : ∃ n:ℕ, ∃ s:Finset (Pot G d),Module.finrank ℝ (U s)=n:= ⟨_,∅,rfl⟩; obtain ⟨s,hs⟩:= Nat.find_spec he
    have hh (s: Finset (Pot G d)) (x:↥(XSpace.Normalize.Change G d)): x∈ U s ↔ ∀ i∈s, Look i x=0:= by unfold U; simp [LinearMap.mem_ker,funext_iff]
    refine ⟨s,show U s=⊥ from le_antisymm ?_ bot_le⟩; intro x hx; apply (Submodule.mem_bot ..).mpr; apply Subtype.ext; change x.val=0; refine Manifest.sure h x.val x.property (fun n e y=>?_ ); let p:Pot G d:=⟨n,e,y⟩
    have hL: U (insert p s)≤ U s:= fun x hx=> ( hh s _ ).mpr (fun i hi=> ( hh _ _ ).mp hx i ( Finset.mem_insert_of_mem hi )); have hu:= Submodule.eq_of_le_of_finrank_le hL (hs ▸ Nat.find_min' he (show ∃ t:Finset (Pot G d),Module.finrank ℝ (U t)=Module.finrank ℝ (U (insert p s)) from ⟨_,rfl⟩)); exact ( hh ( insert p s ) _ ).mp (hu.symm ▸ hx) p (Finset.mem_insert_self ..)
lemma gone (T:ℝ→ Guard G d) (hb:∀ i,Base (T i))(k:ℕ)(h0:k≠0)(he:∀ n p (a:Tags G d n), Rhythm (fun t=> Manifest.response p a (coeff k (T t)))): Tracks T k:= by
    intro p v; obtain ⟨u,H⟩:= determining h d; let Y:= LinearMap.pi ( fun i:u=> Look i.val ); let V:= Y.leftInverse
    let U:ℝ → E:= fun t=> ⟨ coeff k (T t),( hb t ).high k h0 ⟩; let Z: E →ₗ[ℝ]ℂ:= ( v.restrictScalars ℝ ).comp ((( LinearMap.applyₗ (R:=ℂ) p ).restrictScalars ℝ) ∘ₗ ( XSpace.Normalize.Change G d ).subtype ) -- LinearMap apply
    have hx(t): v (coeff k (T t) p)=Z ( V ( Y ( U t ) ) ):= by rw [LinearMap.leftInverse_apply_of_inj H]; rfl
    simp_rw [hx]; exact Rhythm.usage ( Z ∘ₗ V ) (Y ∘ U) (fun i=> he ..)
variable (P:ℝ→ Way G d)(T:ℝ→ Guard G d)(k:ℕ)
omit h
def Gets (P:ℝ→ Way G d): Prop:= ∀ n (x:Stage n) k (v:Tags G d n), Rhythm (fun t=> P t n x k v)
lemma rides (F:Gets P)(H:∀ i,Tracks T i) : Gets (fun t=> actMark (T t) ( P t )):= by
    intro n x k v; unfold actMark; simp_rw [ seen, stencil_he (P _ _ _ _) (pulseU _ _ _), sift ]; refine Rhythm.sum _ fun j _=> Rhythm.sum _ (fun i _=> Rhythm.mul ?_ (F ..)); exact Rhythm.prod _ (fun z _=> H ( j (some z) ) (v z) ( (MS.Theater.Daylight (Press.portDeck G) d).coord (i z) ))
def clip (T:Guard G d) (k:ℕ): Guard G d:= PowerSeries.mk (fun j=> if j < k then coeff j T else 0)
lemma clipped {T:Guard G d} {k:ℕ}(h:Base T)(hp:k≠0): Base (clip T k):= by
    refine ⟨ ?_,fun i hi=>?_ ⟩; · rw [ ← coeff_zero_eq_constantCoeff_apply,clip,coeff_mk, if_pos (Nat.pos_of_ne_zero hp), h.zero ]
    rw [clip, coeff_mk ]; split; exact h.high i hi; exact Submodule.zero_mem (Normalize.Change G d)
lemma together (H:Gets P)(q:ℝ→ Cn)(hp:Clear q): Gets (fun t=> couple (q t) (P t)):= by
    intro n x k v; unfold couple; simp_rw [ Dframe.translate,rules,smul_eq_mul ]; exact Rhythm.sum _ (fun a _=> Rhythm.mul ( Rhythm.unit.mpr ( Pace.formal.pow ( f:=fun (_:Unit) t=> q t ) hp a k ) ) ( H .. ))
include h
theorem walks (hp:∀ t,Equator.StarGround (P t))(H:Gets P)(hT:∀ t,Base (T t))(he:Gets (fun t=> actMark (T t) (P t))): Tracks T k:= by
    induction k using Nat.strong_induction_on with
    | _ k ih=>
       by_cases h0:k=0; · subst k; intro p v; simp_rw [Base.zero (hT _) ]; exact Rhythm.const _
       let K':= fun t:ℝ=> clip (T t) k; have hz:= rides P K' H ( fun i p v=> ( by unfold K' clip; simp only [coeff_mk]; split; apply ih i ‹_›; exact Rhythm.const _ ) ); -- `next` issue
       refine gone h T hT k h0 (fun n p a=>?_ ); have hL(t:ℝ): actMark (T t) ( P t ) n p k a-actMark ( K' t ) ( P t ) n p k a= Manifest.response p a ( coeff k (T t) ):= by
          rw [Manifest.exhibits _ _ (K' t) (hp t) h0 ( clipped (hT t) h0 ) ]; swap; · intro i hi; unfold K'; rw [clip, coeff_mk, if_pos hi]
          unfold K'; rw [clip,coeff_mk,if_neg (lt_irrefl _)]; exact congr_arg ( Manifest.response p a ) ( sub_zero ( ( coeff k (T t)): FieldEnd G d ) )
       replace he:= ( he n p k a ).sub ( hz n p k a ); simp_rw [hL] at he; exact he
-- inverses.Maybe solve via same walks with Phase and tilt. after.
end Meter
end YM.FVA2.Scale
