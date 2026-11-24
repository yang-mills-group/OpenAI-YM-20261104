import YM.Qlocal.Gauges.Mastery
/-! Leaf ontology. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Gauges.Atlas
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload YM.Qlocal.Gauges.Atlas
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner Parabola
open RGComparison01 RGComparison01.Pledge Quipu Quipu.Sonnet Atlas Planet
variable {Ω ι J V I : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n c:Side}{P: RG.Rep G n}
    {o:V→Site n}{s s':V→Support n}{q:R.Mode→ℝ}{a b v t δ C A B θ ρ ζ:ℝ}
variable (o) {k:ℕ} (i:Notice R) (s)
variable (hP : ∀ s∈i.val,Tale.Live o s k)
abbrev Safe (o:V→Site n)(i:Notice R)(k:ℕ):= ∀ s∈i.val,Tale.Live o s k
noncomputable def arrival : ↥i.val ↪ (Live o R k):= ⟨fun j=>⟨j.val,hP j.val j.prop⟩,fun i j he=>Subtype.ext (congr_arg (fun v:Live o R k=> v.val) he)⟩
noncomputable def window : ↥i.val ↪ Stakeup R o s k:= (arrival o i hP).trans (Function.Embedding.inr)
local notation "κ✶"=>intoK R s o k
local notation "Ω₀"=>window o s i hP
variable [Fintype V]
lemma booked : Planet.book (intoK R s o k) (univ.map (window o s i hP))= Atlas.tag R s i:= by
 apply Subtype.ext; ext p; change p∈ _root_.Finset.map _ _ ↔ p∈ Finset.map _ _
 constructor
 · intro h; obtain ⟨j,h₁,rfl⟩:=mem_map.mp h; obtain ⟨j,h,rfl⟩:= mem_map.mp h₁; exact mem_map_of_mem (core R s) j.prop
 intro h; obtain ⟨j,h₁,rfl⟩:=mem_map.mp h; exact mem_map_of_mem (intoK R s o k) (mem_map_of_mem (window o s i hP) (mem_univ (⟨j,h₁⟩ : ↥i.val))) -- definitional coercion
lemma tickets (p:Finset (Stakeup R o s k))(hx: book (intoK R s o k) p= tag R s i) : ¬Safe o i k → False:= by
 intro he; apply he
 intro s' hs; have hv : (core R s) s'∈ p.map (intoK R s o k):= (show p.map κ✶=i.val.map (core R s) from congr_arg Subtype.val hx).symm ▸ mem_map_of_mem (core R s) hs
 obtain ⟨j,hj,h⟩:=mem_map.mp hv; rcases j with j|j; change Sum.inl j=Sum.inr (α:=Payload.deck R s) s' at h; cases h; exact Eq.mp (congr_arg (fun i=> Tale.Live o i k) (Sum.inr.inj (show Sum.inr (α:=Payload.deck R s) j.val= .inr s' from h))) j.prop
lemma tickets_iff (p:Finset (Stakeup R o s k)) : Planet.book κ✶ p=tag R s i ↔ ∃ hP:Safe o i k,p=univ.map (window o s i hP):= by
 constructor; intro he; have ht:= Classical.byContradiction (tickets o s i p he); exact ⟨ht,Palace.Moon.book_inj κ✶ (he.trans (booked o s i ht).symm)⟩
 rintro ⟨h',rfl⟩; exact booked ..
-- correspondence for projections. Frame.O.Ans.U.
end YM.Qlocal.Gauges.Atlas
