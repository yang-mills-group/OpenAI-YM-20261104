import YM.OPE.Laying.Roll
/-! # Prior alternatives at landing -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup Float Drapery Playout.Rake
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d T :ℕ}{w x y α x':ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "μ'"=> (waybill C.path.levels)
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "ν"=> (fun i=> ((C.path.levels.budget i).supportExponent-3:ℝ))
variable {Θ: Playout C.path p b N V}{A:Fibers I J} {s:Ward (Names V I)} {s':Ward (Names V J)}{W₀:ℕ→I→ℝ}{φ:I→ℕ}
    {u:∀ i:ℕ,I→ Site (C.side i p)} {F:I→ Config G (C.side N p)→ℂ}
    {P:∀ i:ℕ,I→ Cup (C.path.rep N p i)} {z:Finset J}
namespace Mask
open Muster.Pigment Playout
-- pullback exclusive (used only when summing counters and marked after grouping)
def clash (G:I→J) (s:Ward (Names V J)) : Ward (Names V I) where
    ready p:= s.ready (Pigment.batch (Pigment.sweep V G) p) ∧ Set.InjOn (Pigment.sweep V G) p.val
    blank:=by
       constructor
       · rw [show Pigment.batch (Pigment.sweep V G) ((Names V I).quiet)=(Names V J).quiet from Subtype.ext (image_empty _)]; exact s.blank
       intro i hi; exact (Finset.notMem_empty i hi).elim
    down hv hh:= ⟨s.down (image_subset_image hv) hh.1, hh.2.mono (show _ from (fun i hi=>hv hi))⟩ -- subset implicit. edit
    fire a:=by
        constructor
        · rw [show Pigment.batch (Pigment.sweep V G) ((Names V I).fire a)=(Names V J).fire (Pigment.sweep V G a) from Subtype.ext (image_singleton ..)]; exact s.fire _
        exact fun i hi j hj h=> (mem_singleton.mp hi).trans (mem_singleton.mp hj).symm

local notation "q!"=> Pigment.sweep V
variable (G':I→J)
lemma crashTrials (h: Trial s') : Trial (clash G' s'):=by
    intro u p; let Q:= (nome (slotsZ:=I) u); have he: ManyCopies.drum u (Pigment.batch (q! G') p)= Pigment.batch (q! G') (ManyCopies.drum u p):= Subtype.ext (by unfold Pigment.batch ManyCopies.drum; simp only [pares,image_image]; rfl) -- namespace
    have ht: ∀ i:V×I,(q! G') (Q i)=(nome (slotsZ:=J) u) (q! G' i):=fun _=> rfl
    have hp : Set.InjOn (q! G') p.val ↔ Set.InjOn (q! G') (ManyCopies.drum u p|>.val):=by
       rw [ManyCopies.drum,pares]; change Set.InjOn _ _ ↔ Set.InjOn _ ((p.val.image Q:Set (V×I)))
       constructor
       · intro h i hi j hj hh; obtain ⟨i,hx,rfl⟩:= mem_image.mp hi; obtain ⟨j,he,rfl⟩:= mem_image.mp hj; rw [ht,ht] at hh; exact congr_arg _ (h hx he ((nome (slotsZ:=J) u).injective hh))
       intro h i hi j hj hz; exact Q.injective (h (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) (by rw [ht,ht,hz]))
    exact and_congr ((h u (Pigment.batch (q! G') p)).trans (by rw [he])) hp

-- One location per cell.Yield needed for projecting exactly.Prove BEFORE any extraction planning.
def Pitch (s:Ward (Names V I)) : Prop:=∀ (i:I)(p:(Names V I).Mode), (∀ a:V×I,a∈p.val→ a.2=i)→ s.ready p
lemma Pitch.clashAt (h:Pitch s'): Pitch (clash G' s'):=by
    intro k p hh; refine ⟨?_,fun i hi j hj hv=> Prod.ext (show (Pigment.sweep V G' _).1=(Pigment.sweep V G' _).1 from congr_arg Prod.fst hv) ((hh _ hi).trans (hh _ hj).symm)⟩
    refine h (G' k) _ ?_; intro j hj; obtain ⟨v,hv,rfl⟩:= mem_image.mp hj; exact congr_arg G' (hh v hv)
lemma Pitch.all : Pitch (Ward.all (Names V I)):= fun _ _ _=> trivial
lemma Pitch.group (h:Pitch s'): Pitch (pullback A s'):=by
    intro k p hh; refine h (A.bunch k) ((partialGroup V A).span p) ?_; intro j hj; obtain ⟨v,hv,rfl⟩:= mem_image.mp hj; exact congr_arg A.bunch (hh _ hv)

@[simp] lemma Cup.oneS (p:Cup (C.path.rep N p i)): (1:ℂ) • p=p:= Cup.same (by simp) (by simp)
@[simp] lemma Cup.zeroS (p:Cup (C.path.rep N p i)): (0:ℂ) • p=0:=Cup.same (by simp) (by simp)
-- isolate ONE marker at time with equal Stake.Transport leg later.
def filterC (x:I)(u:I):ℂ:=if x=u then 1 else 0
variable (K:I)
include h
lemma holdOneField (he:Pitch s)(hx:i≤N)(hr: Θ.Market s (u i) (P i) (Θ.intention F i hx) (W₀ i) x)(hf:∀ i,Continuous (F i)) : Θ.Market (Ward.all (Names V Unit)) (fun _:Unit=> u i K) (fun _=>P i K) (Θ.intention (fun _=>F K) i hx) (fun _=> W₀ i K) x:=by
    let f (_:I):= (Unit.unit); let x':= filterC K; let w':=(fun _ : Unit=> W₀ i K)
    have hξ{u:I} (h:x' u≠0): K=u:= not_not.mp (fun hp=>h (if_neg hp))
    have hm : Θ.Market (Ward.all (Names V Unit)) (fun _:Unit=>u i K) (linear f x' (P i)) (Θ.intention (linear f x' F) i hx) w' x:= by
        apply hr.changeChannels Θ F f x' hx h.wilson hf (fun i hi=> by rw [hξ hi]) ?_ (fun _=>hr.width K) ?_
        · intro k; by_cases hk:k=K
          · rw [hk,show x' K=1 from if_pos rfl]; simp [w']
          rw [show x' k=0 from if_neg (Ne.symm hk)]; simp [hr.width k|>.le]
        intro p _ _ ht; exact he K p (fun a ha=> (hξ (ht a ha)).symm)
    have hL : residents f ()=univ:= Finset.filter_true_of_mem (fun i _=>rfl) -- inspect
    have hK' : linear f x' (P i) = (fun _:Unit=>P i K):=by
       funext v; cases v; unfold linear; rw [hL,sum_eq_single K]; · rw [show x' K=1 from if_pos rfl]; exact Cup.oneS _
       · intro b _ hh; rw [show x' b=0 from if_neg hh.symm]; exact Cup.zeroS _
       simp
    have hF : linear f x' F=(fun _:Unit=>F K):=(by funext v;cases v;unfold linear; rw [hL]; simp [x',filterC,eq_comm])
    rw [hK',hF] at hm; exact hm
end Mask
end YM.OPE.Log.Book
