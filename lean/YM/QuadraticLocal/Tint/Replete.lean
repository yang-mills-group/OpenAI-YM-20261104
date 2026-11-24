import YM.QuadraticLocal.Tint.Patrol
/-! # Recognize REAL short candidate Page at populated orientations -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tint.Patrol
open Function Filter Finset Lattice RG Wilson Marker Ac Push Push.AbsoluteSums Paths Animals
open QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder AllOrder.Ink
open Push.SectorMeasure ConnectedActivityE6 RemainderComparison Trigger
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V α ι J: Type}[DecidableEq V]{G:Gauge}{n c:Side}
variable {P:Passport n V} {R:Census V} {g a e r b :ℝ} {k i' j u i h : ℕ}
variable (X:ι→Row P R G α) (C:Club X)
open Travel Club Typeface Lyric
variable {U:RG.Rep G n} (T:Incoming P U α J R) (w:V→ℝ)(hw:∀ i,0<w i)
set_option quotPrecheck false
local notation "L"=> Tint.Patrol.Shift X T
local notation "K"=> Club.Keys X C

abbrev Masks := {i:ι//¬(X i).clear}
local notation "Z₀"=> (fun (i:Masks X × Bool)=> enter X T i)
local notation "f₁"=> (stakeholder X T)

lemma catalogue (S:Finset (Tint.Patrol.Shift X T))(h:Clash.lit (Patrol.stakeholder X T) (way X T w) S) (hv:↑S⊆ Set.range (Patrol.enter X T)) : ∃ i: Club X,∃ v,pulp X i T v=S := by
    obtain ⟨r,hr,hx⟩:= h; obtain ⟨h,hF,hP⟩:= Clash.permits _ _ S hx hr; choose p hp using fun i:↥S=> (show i.val∈ Set.range (Patrol.enter X T) from hv i.prop); let f i:= (p i).fst.val; let u(i:↥S):=(p i).snd; let fz:=f
    have hh(i:↥S): ¬(X (f i)).clear:= ((p i).fst.prop); have he(i:↥S): f₁ i.val=(X (f i)).mode:= by
       unfold f; nth_rw 1 [← hp i]; rfl
    have hg : Injective f:= by
       intro i k h'; by_contra hj; have hK:= h i.prop k.prop (Subtype.val_injective.ne hj); dsimp only at hK; rw [he i,he k,h'] at hK; exact (X _|>.binder.live) (Subtype.ext (disjoint_self.mp hK))
    let Q:Finset ι:= univ.image f
    have hi : (Q:Set ι).Pairwise (fun i j=> Disjoint (X i).mode.val (X j).mode.val):=by
       intro i hi j hj ht; obtain ⟨x,_,rfl⟩:= mem_image.mp hi; obtain ⟨y,_,rfl⟩:= mem_image.mp hj; rw [← he x,←he y]; exact h x.prop y.prop fun hx=> ht (congr_arg f (Subtype.ext hx))
    have hQ : Q.biUnion (fun i=> (X i).mode.val)= Clash.issued f₁ S:=by
       ext1 i; unfold Clash.issued; constructor
       · intro he'; obtain ⟨k,hk,hy⟩:=mem_biUnion.mp he'; obtain ⟨v,_,rfl⟩:= mem_image.mp hk; rw [← he v] at hy; exact mem_biUnion.mpr ⟨_,v.prop,hy⟩
       intro he'; obtain ⟨k,hk,h'⟩:=mem_biUnion.mp he'; let b:↥S:= ⟨k,hk⟩; exact mem_biUnion.mpr ⟨f b,mem_image_of_mem _ (mem_univ _), (he b) ▸ h'⟩
    obtain ⟨i,hh'⟩:= hP; let z:↥S:=⟨i,hh'⟩; let V₀:Club X:=⟨Q,⟨f z,mem_image_of_mem _ (mem_univ _)⟩,hi,⟨r,(hQ.trans hF).symm⟩,fun i hi=>by obtain ⟨k,_,rfl⟩:= mem_image.mp hi; exact hh k⟩
    have hv (i:Club.Keys X V₀):∃ p:↥S, f p= Club.stamp X V₀ i:= by obtain ⟨i',_,h⟩:=mem_image.mp (show _∈ Q from Club.attends X V₀ i); exact ⟨_,h⟩
    choose K0 hK0 using hv; let v:= u ∘ K0; let Vp:= out X V₀ T v
    have ht(i: Club.Keys X V₀): Vp i=(K0 i).val:=by
       rw [← hp]; unfold Vp Patrol.out; apply congr_arg; exact Prod.ext (Subtype.ext (hK0 i).symm) rfl
    refine ⟨V₀,v,Subset.antisymm ?_ ?_⟩; intro x hx; obtain ⟨i,_,rfl⟩:=mem_image.mp hx; change Vp i∈S; rw [ht i]; exact (K0 i).prop
    intro i hi; let j:↑S:=⟨i,hi⟩; obtain ⟨k,hk⟩:= Club.attends_rev X V₀ _ (mem_image_of_mem f (Finset.mem_univ j)); exact Finset.mem_image.mpr ⟨k,mem_univ _,(ht k).trans (congr_arg Subtype.val (hg ((hK0 k).trans hk)))⟩
-- REAL clinker, eligibility and forecasts before Heal.Art.t Memo. no threshold Meta unused safety.St.
end YM.QuadraticLocal.Tint.Patrol
