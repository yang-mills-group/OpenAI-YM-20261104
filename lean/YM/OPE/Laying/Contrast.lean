import YM.OPE.Laying.Sign
/-! # Linear contrast at merge of a cluster with counters -/
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
open Playout Muster.Pigment Extra.Histories.Relay
variable (K:I) (u':ℕ)
-- use basis at the LAST summand (forest planners arrange their names in this order)
abbrev recognize (K:I) (x:I ⊕ J): I:= Sum.elim id (fun _=>K) x
abbrev inkC (I:Type)(f:J→ℂ) (x:I ⊕ J) := Sum.elim (fun _=>1) f x
variable {U:Type*}[AddCommMonoid U][SMul ℂ U](p':I⊕J→ U)
    (f:J→ℂ)
lemma intensity (i':I)(he:i'≠K) (ht:(1:ℂ) • p' (.inl i')=p' (.inl i')) : linear (recognize (J:=J) K) (inkC I f) p' i'= p' (.inl i'):=by
    simp only [linear,residents,sum_filter,Fintype.sum_sum_type]; simp [recognize,inkC,ht,Ne.symm he] -- `resident` lemma?
lemma saturation (hp:(1:ℂ) • p' (.inl K)=p' (.inl K)) : linear (recognize (J:=J) K) (inkC I f) p' K=p' (.inl K)+∑ i,f i • p' (.inr i):=by
    simp only [linear,residents,sum_filter,Fintype.sum_sum_type]; simp [recognize,inkC,hp]

-- Ledger mixture.After Right Mint scheduled with any new clock and width exactly same at blend
variable {φS:(I⊕J)→ℕ}{P':∀ i:ℕ,I⊕J→Cup (C.path.rep N p i)}{F': (I⊕J)→ Config G (C.side N p)→ℂ}{W' : ℕ→I⊕J→ℝ}{u'' : ∀ i:ℕ,I⊕J→Site (C.side i p)}{C':∀ i:ℕ,Cup (C.path.rep N p i)} (S:Ledger Θ i (clash (recognize K) s) F' P' u'' φS W' x (D:(∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))))
local notation "p!"=> (linear (recognize (J:=J) K) (inkC I f))
local notation "v!"=> fun i=>(u'' i ∘ Sum.inl)
include S h
lemma blendLedger {W₁:ℕ→ I→ℝ}{φ₁:I→ℕ} (hP:Trial s)(hi:b ≤ φ₁ K)(hj:φ₁ K ≤ i)(hφ:∀ i',i'≠K→φ₁ i'= φS (.inl i')) (hr:Lenient η₀ φ₁ W₁) (hW:∀ i',W₁ i i'= W' i (.inl i')) (hw:∀ i',i'≠K→∀ j', W₁ j' i'= W' j' (.inl i'))
    (hy:0<y)(h_y:y≤x) (hc: ∀ k,y*W' i (.inl K) *‖f k‖≤ x*W' i (.inr k))(hZ:∀ k,u'' i (.inl K)=u'' i (.inr k))(he: C' i=p! (P' i) K)(hX:Program C.path N p (φ₁ K) i (fun i=>u'' i (.inl K)) C' (fun i=>lifted W₁ y i K) D S.limit) : ∃ Q:∀ i:ℕ,I→ Cup (C.path.rep N p i), Ledger Θ i s (p! F') Q (v!) φ₁ W₁ y D ∧ (∀ i'≠K,∀ j',Q j' i'=P' j' (.inl i'))∧∀ j',Q j' K=C' j':=by
    let V':=p! F'; let P₀:=p! (P' i); let m(x:I):=Sum.inl (β:=J) x; let Q(j:ℕ) := Function.update (P' j ∘ m) K (C' j); have ht(j):Q j K=C' j:=update_self ..
    have hv(j)(k:I)(h:k≠K): Q j k=P' j (.inl k):= update_of_ne h ..
    have hF(k):Continuous (V' k):=by change Continuous (fun a=> (∑ i∈ residents (recognize K) k,inkC I f i • F' i) a); simp_rw [Finset.sum_apply]; exact continuous_finsetSum _ fun i _=>(S.terms i).const_smul _
    have hz: Θ.Market s ((v!) i) P₀ (Θ.intention V' i S.limit) (lifted W₁ y i) (ν i):=by -- notation needs parentheses
       refine S.market.changeChannels Θ F' (recognize K) (inkC I f) S.limit h.wilson S.terms ?_ ?_ (fun i' => mul_pos hy (hr.ready ..)) (fun i' h k _=>⟨h,k⟩)
       · rintro (i'|j') h; rfl; exact hZ _
       rintro (j|j)
       · unfold lifted; rw [show recognize K (Sum.inl (β:=J) j)=j from rfl, show inkC I f (Sum.inl j)=1 from rfl, norm_one, mul_one, hW]; exact mul_le_mul_of_nonneg_right h_y (S.clock.ready ..|>.le)
       change y* W₁ i K*‖f j‖ ≤ _; rw [hW]; exact hc j
    have hκ:P₀=Q i:=funext fun j=>by by_cases p':j=K; subst j; exact (he.symm.trans (ht i).symm); exact (intensity K (P' i) f _ p' (by simp)).trans (hv i j p').symm
    refine ⟨Q,⟨S.time,S.limit,hP,fun i hi ht j=> S.slots i hi ht _, hF, fun j=>?_,⟨hy,h_y.trans S.rate.2⟩,hr,hκ ▸ hz,fun j=>?_⟩, fun i hi k=>hv k i hi,ht⟩
    · by_cases he:j=K
      · subst j; exact ⟨hi,hj⟩
      rw [hφ _ he]; exact S.stock _
    by_cases he:j=K
    · subst j; rw [show (fun i=>Q i K) = C' from funext ht]; exact hX
    rw [hφ _ he,show (fun i=> Q i j)=(fun i=> P' i (.inl j)) from funext (fun i=>hv i j he)]
    apply (S.progress (.inl j)).within le_rfl le_rfl (fun _ _ _=> (hr.scaleRight hy|>.ready ..).le) (fun _ _ _=> ?_); unfold lifted; rw [hw _ he]; exact mul_le_mul_of_nonneg_right h_y (S.clock.ready ..|>.le)
end Mask
end YM.OPE.Log.Book
