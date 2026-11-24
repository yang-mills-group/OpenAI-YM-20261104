import YM.QuadraticLocal.Fk.Game
import YM.QuadraticLocal.Fk.Star
import YM.QuadraticLocal.Fk.Keep
/-! # Finite superposition of the dependent cluster powers

For each given internal height. Jumps on outside colors propagated ONLY if allowed
and using the spectral output referenced.Aura positions after pullback require future
spacing when establishing norm receipts. This uses exactly `birth` for kernel analytic
model. Genuinely connected, no supposition that bigger arrays are admissible than the
order symbol previously bought.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
variable (F: Finset ι) (L:Layout G) (T:Finset Age)
namespace ScatterR
set_option quotPrecheck false
local notation "R₀"=> Focus.census ι
open Comparison.RG02
open Marker Multi
-- ℝ colors are powered mark functions for Fk, have denominator.
section mix
variable {V₁:Type} [DecidableEq V₁](J:Census V₁)(e:ι→Multi.Hot J)(q:ι→ℂ) (w:V₁→ℕ)
local notation "Yₐ"=> Launch.index J w

local notation "Pℓ"=> ScatterR.colors M F L T J e q w
variable {c' : Side} {S:StepData c' n} {B₀:Clip} {D':PathData G}{O:ChartRatio G}
open Comparison.RG02.Bulk
variable (K:Comparison.RG02.Bulk.Kernel S B₀ D' O)(X:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c' 1)
set_option quotPrecheck false
open Comparison.RG02.Order
local notation "FCb"=> Colors C -- no
local notation "π" v:max=> Bulk.Fk K X t v x k
local notation "C'"=> (R)
variable (i j:ℕ)
-- finite pullback. Need equality for Colors stamp through.P.Trace.M.State.Com.Worker.` preserve all n memberships.
local notation "δ"=> (fun i':↥F=> (M i'.val).lamp.toll)
local notation "α'"=> (Subtype.val:↥F→ι)
lemma via : ScatterR.colors M F L T J e q w= ScatterR.colors (M ∘ (Subtype.val:↥F→ι)) univ L T J (e ∘ Subtype.val) (q ∘ Subtype.val) w:= by
 refine ScatterR.extC J _ _ ?_ rfl rfl; funext j; rw [markEq,markEq]; simp_rw [Finset.sum_filter]; exact ( Finset.sum_attach F (fun i:ι=> if j.val=(e i).val then familyAt M q i else 0)).symm -- RHS univ=F.attach
end mix
open Comparison.RG02
section sampled
variable {c' : Side} {S:StepData c' n} {B₀:Clip} {D':PathData G}{O:ChartRatio G}
open Comparison.RG02.Bulk
variable (K:Comparison.RG02.Bulk.Kernel S B₀ D' O)(X:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c' 1)
set_option quotPrecheck false
def actor (i:ι) : Multi.Hot R:= ⟨(M i).mode, (Comparison.RG02.Cumulants.hot_iff_ne (M i).mode).2 (M i).binder.live⟩
variable (q:ι→ℂ)(w:V→ℕ)(H: ∀i∈F,(M i).lamp.toll=Launch.index R w (M i).mode)
local notation "J"=> (R)
local notation "P'"=> (F)
local notation "e"=> ScatterR.actor M
local notation "W"=> ScatterR.colors M F L T J (actor M) q w
local notation "Hℓ"=> ( univ : Finset ↥F)
local notation "C"=> Focus.census ↥F
local notation "τ"=> Bulk.Fk K X t
local notation "ν"=> ScatterR.edition ( M ∘ (Subtype.val:↥F→ι)) univ L T
local notation "Π'" A:max x:max=> Comparison.RG02.Order.observe A k ( Comparison.RG02.Order.logMarked x)
variable (cT: Club M)
local notation "af"=> (Subtype.val:↥F→ι)
variable [DecidableEq ι] -- F before instance; `mem` from props.B`. reindex.
local notation "Υ" A:max=> Finset.image (Subtype.val:↥F→ι) A
local notation "f₀" i:max=> ((Π' C ( (τ) ν x k) ) d).part (Focus.onto i)
def history (d k:ℕ):ℂ:= (Comparison.RG02.Order.observe (Focus.census (Club.Keys M cT)) k (Comparison.RG02.Order.logMarked (Bulk.Fk K X t (ScatterR.birth M L T cT) x k)) d).part (Focus.onto (univ:Finset (Club.Keys M cT)))
local notation "Cx" c':max=> ScatterR.history M L T K X t x c'
local notation "μ₀"=> history M L T K X t x cT d k
variable (A: Finset ↥F)
include q w H
local notation "U" i:max=> ( f₀ i )
local notation "ζ" i:max=> (U i) • ∏ j∈ i, Poly.send (M j.val).mode (q j.val) -- args
local notation "ζ₀" i:max=> (∏ j∈ i, Poly.send (M j).mode (q j))
omit H q w in
lemma repo (he: (Finset.image Subtype.val A)=cT.val)(hx:d≤k): ((Π' C ((τ) ν x k) ) d).part (Focus.onto A) = history M L T K X t x cT d k:= by
 let z := Club.Keys M cT
 let H(i:z): Club.stamp M cT i∈F:=by
      obtain ⟨p,hp,hP⟩:= mem_image.mp (he ▸ Club.attends M cT i); exact hP ▸ p.prop
 let f (i:z):↥F:= ⟨Club.stamp M cT i,H i⟩; let u:z↪↥F:= ⟨f, fun i j h=> Club.troop_inj M cT (congr_arg (Subtype.val : ↥F→ι) h)⟩
 have hp:A=(Finset.univ.image u):= by apply (Finset.image_injective (Subtype.val_injective («p»:=fun i:ι=> i∈F))); rw [he,image_image]; ext1 i; simp only [mem_image,mem_univ,true_and]; exact ⟨fun hi=> Club.attends_rev M cT i hi,fun ⟨a,ha⟩=> ha ▸ Club.attends M cT a⟩
 rw [hp]; exact ScatterR.transfer_part ( M ∘ (Subtype.val:↥F→ι)) L T u (Club.troops M cT) rfl K X t x univ hx
local notation "φ"=> (Finset.powerset F)
variable [Fintype V]
local notation "υ"=> (Runway.Core.Shape) -- no
-- sums finite via `selected`
abbrev lounge : Finset (Club M):= Finset.preimage (Finset.powerset F) Subtype.val Subtype.val_injective.injOn
local notation "Ω'"=> ScatterR.lounge M F
variable (hw: ∀ i∈F,¬(M i).clear)(he:d≤k)
local notation "Πr" c:max=> ( (ScatterR.history M L T K X t x c d k)*(∏ i∈c.val,q i))
local notation "g'" c:max=> Poly.send ( Club.alliance M c) ( (ScatterR.history M L T K X t x c d k)*(∏ i∈(Club.members M c),q i))
def unitTerm (d k:ℕ)(v:Club M): Poly R:= Poly.send (Club.alliance M v) ((ScatterR.history M L T K X t x v d k)*(∏ i∈v.val,q i))
-- Maintain type t. each lens positions mapping hp.
local notation "G'"=> ScatterR.unitTerm M L T K X t x q d k -- order arg q check.
omit q H w in
lemma quietT : ( f₀ (∅:Finset ↥F))=0:= by
 let hx:= Bulk.fk_unit K X t ν x k; let he:= Order.log_marked hx; let p:= Order.logMarked (τ ν x k); have hg : p= Order.logMarked (τ ν x k):= rfl; let f:= Order.observe C k p d; change f.part _=0;
 have hz: Order.observe C k 0 d=0:= (Order.observeL (R:=C) (r:=k) d).map_zero; have h : Order.blanked C f=0:= ((Order.observe_bottom p d)).symm.trans ((congr_arg (fun x=> Order.observe C k x d) he).trans hz); change f.part (Focus.census ↥F|>.quiet)=0; have hm:= Order.pure_marks f (Focus.census ↥F|>.quiet); rw [if_pos rfl,h] at hm; exact hm.symm
-- f₀ j terms product.Prop. for nonex lens bind.P.
include hw he
-- important complete unmasked Fk. form Price Estimate uses l_learner.Certificate.L.State.Region.
lemma participates : Comparison.RG02.Order.observe R k (Comparison.RG02.Order.logMarked (Bulk.Fk K X t (ScatterR.colors M F L T R (actor M) q w) x k)) d= ∑ v∈ ScatterR.lounge M F, ScatterR.unitTerm M L T K X t x q d k v := by
 let A0:= M ∘ (af); let e₀:= (e) ∘ af; let q':= q ∘ (af); let H₀ (i:↥F) (_:i∈( univ:Finset ↥F)): (A0 i).lamp.toll= Launch.index R w (e₀ i).val:= H _ i.prop
 rw [ScatterR.via M F L T R (ScatterR.actor M) q w]; rw [ ScatterR.transmission (M∘ (Subtype.val:↥F→ι)) univ L T _ e₀ q' w K X t x H₀ d k]; rw [TableMap.pushes];
 -- tactics now gather, inspect trans sig. use index `univ powerset ↥F`. key injection into ι.
 let xf (v:Club M):= Finset.preimage v.val af (Subtype.val_injective.injOn); -- shadows root x.Mesh macro; ok?
 let f (C0:Club M):= xf C0;
 let g (u':Finset ↥F):= ( f₀ u' ) • (∏ j∈u', Poly.send (M j.val).mode (q j.val)); let U':= Ω';
 change (∑ i:Finset ↥F, g i)=_;
 have hV (c:Club M)(hv:c∈U') : Finset.image (Subtype.val:↥F→ι) (f c)= c.val:= by
    rw [show f c= xf c from rfl]; unfold xf; rw [image_preimage]; apply filter_true_of_mem; intro i hi; exact ⟨(⟨i,Finset.mem_powerset.mp (Finset.mem_preimage.mp hv) hi⟩:↥F),rfl⟩
 have hz : Function.Injective (Finset.image af):= Finset.image_injective Subtype.val_injective
 calc
   _ = ∑ i∈ U'.image f,g i:= by
      symm; apply Finset.sum_subset (Finset.subset_univ _); intro i _ H; let s:= Finset.image af i; rcases Finset.eq_empty_or_nonempty i with h|h;
      · rw [h]; unfold g; rw [quietT, zero_smul] -- implicit
      have hv : ¬∃ v:Club M,v.val=s:= by rintro ⟨j,v⟩; have hu:j∈ U':= Finset.mem_preimage.mpr (Finset.mem_powerset.mpr (fun k h=> by obtain ⟨ei,he,ht⟩:= Finset.mem_image.mp (v ▸ h); exact ht ▸ ei.prop)); exact H (Finset.mem_image.mpr ⟨j,hu,hz ((hV j hu).trans v)⟩)
      have hH : ∀ j∈s,¬(M j).clear:= fun j hj=> by obtain ⟨i₁,hh,rfl⟩:=mem_image.mp hj; exact hw _ i₁.prop
      have hh : (∏ j∈ i,Poly.send (M j.val).mode (q j.val))=0:= Eq.trans ((prod_image (f:=fun i=>Poly.send (M i).mode (q i)) (s:=i) Subtype.val_injective.injOn)).symm (Game.omitted M s q (h.image Subtype.val) hH hv)
      unfold g; rw [hh,smul_zero]
   _ = _:= by
      rw [Finset.sum_image]; rotate_left
      · exact fun i hi j hj hg=> Subtype.ext ((hV i hi).symm.trans ((congr_arg (Finset.image af) hg).trans (hV j hj)))
      apply Finset.sum_congr rfl; intro i hi; let f₀_g:= f i; unfold g; rw [repo M F L T K X t x i f₀_g (hV i hi) he] -- q/w argument order
      let Q (i:ι):= Poly.send (M i).mode (q i); rw [show (∏ j∈ f₀_g,Q j.val) =∏ j∈i.val,Poly.send (M j).mode (q j) from (prod_image (f:=Q) (s:=f i) Subtype.val_injective.injOn).symm.trans (congr_arg (fun s:Finset ι=> (∏ i∈s,Q i)) (hV i hi))] -- replace sumEq
      rw [Game.club_price]; exact (send_scale ..).symm
end sampled
end ScatterR
end YM.QuadraticLocal.Earn
