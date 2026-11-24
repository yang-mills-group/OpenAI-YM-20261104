import YM.Qlocal.Gauges.Mouth
import YM.Qlocal.Canopy.Port
import YM.Qlocal.Reckoner.Couch
/-!
# Choosing enrollment interactions. Temp library ↪ full physical region
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Gauges
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Reckoner Parabola
open RGComparison01 RGComparison01.Pledge
open Quipu Quipu.Sonnet
variable {Ω ι J V I : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n c:Side}{P: RG.Rep G n}
    {o:V→Site n}{s s':V→Support n}{q:R.Mode→ℝ}{a b v t δ C A B θ ρ ζ:ℝ}
    {Y:Taste Ω o P R}{dcl:Set (ℕ ×ℕ)}
-- census.Temp tags include inactive analytics. Mapper.Photo.Pay.States. Decidable.FI via classical.Mask.World
namespace Atlas
open Planet
variable {k m: ℕ} [Fintype V]
abbrev Loft (R:Census V) (d: V→Support n) := Payload.deck R d ⊕ Senses R
abbrev Live (o:V→Site n)(R:Census V) (k:ℕ) := {i:Senses R // Sonnet.Tale.Live o i k}
scoped instance alive (V:Type) [Fintype V][DecidableEq V]{n:Side}(R:Census V)(o:V→Site n)(k:ℕ): Fintype (Live o R k):= inferInstanceAs (Fintype {i:Senses R// Sonnet.Tale.Live o i k})
noncomputable abbrev living (o:V→Site n)(R:Census V)(k:ℕ) : Live o R k ↪ Senses R:= Function.Embedding.subtype _
set_option quotPrecheck false
local notation "B!"=> Live o R k
local notation "A!"=>Loft R s
local notation "D!"=>Payload.deck R s
local notation "Ψ"=>Planet.Whole (A!)
noncomputable abbrev slate (R:Census V)(s:V→Support n)(v:Loft R s):R.Mode:= Sum.elim Payload.kind Subtype.val v
local notation "q★"=> slate R s
lemma hot0 (i:A!) :((q★) i).val.Nonempty:= by cases i; exact Emissions.nextkind _; exact (by rename_i a; exact a.prop)
-- slate.Sum.
abbrev Stakeup (R:Census V)(o:V→Site n)(s:V→Support n)(k:ℕ):=Payload.deck R s⊕ Live o R k
noncomputable abbrev intoK (R:Census V)(d:V→Support n)(o:V→Site n)(k:ℕ) : Stakeup R o d k ↪ Loft R d:=
  (Embedding.refl (deck R d)).sumMap (living o R k)
local notation "Ω!"=> Stakeup R o s k
noncomputable def core (R:Census V)(s:V→Support n) : Senses R↪ Loft R s:= Function.Embedding.inr
local notation "Hl"=> living o R k
local notation "Dc"=> core R s
local notation "ℓ"=> intoK R s o k
local notation "q2"=> Plant -- template
-- need through n sensor all arity. payment per-coordinate Frame.Estat. fit criterion.Route
noncomputable abbrev ticket (R:Census V) : Senses R→ R.Mode:= Subtype.val
abbrev Notice (R:Census V) := {u:Finset (Senses R)// u.Nonempty∧Fits (ticket R) u}
scoped instance foreset (R:Census V): Fintype (Notice R):= inferInstanceAs <| Fintype {u:Finset (Senses R)// u.Nonempty∧Fits (ticket R) u}
noncomputable abbrev tag (R:Census V)(s:V→ Support n)(i:Notice R): (Planet.Whole (Loft R s)).Mode:= Planet.book (core R s) i.val
local notation "τ" => tag R s
lemma tag_unique (R:Census V)(s:V→ Support n): Injective (tag R s) := (Palace.Moon.book_inj (core R s)).comp Subtype.val_injective
variable (B0:Finset (Senses R))
noncomputable abbrev grade (R:Census V) (i:Notice R) := unionTag (ticket R) i.val i.prop.2
abbrev parcel (R:Census V)(i:Notice R): Senses R:= ⟨grade R i, by obtain ⟨v,hv⟩:= i.prop.1; obtain ⟨a,ha⟩:= v.prop; exact ⟨a,mem_biUnion.mpr ⟨v,hv,ha⟩⟩⟩
lemma used (p:Notice R) (j:Senses R)(hp:j∈p.val): essence j⊆ (grade R p).val:= subset_biUnion_of_mem _ hp
lemma covers (v:V) (p:Notice R) (hz:v∈(grade R p).val) : ∃ i∈p.val,v∈essence i:= mem_biUnion.mp hz
-- fit rank controls γ.Operator estimates. Loom requires ≤ count picks.
lemma grade_hunger (X:J→R.Mode)(h:∀ i,(X i).val.Nonempty) (u:Finset J)(hp:Fits X u): u.card ≤ (unionTag X u hp).val.card:= by
 unfold unionTag; dsimp only; rw [Finset.card_biUnion hp.1, ← show (∑ _∈u, (1:ℕ))=u.card from by simp]; exact Finset.sum_le_sum fun i _=> card_pos.mpr (h _)
lemma guards (p:Notice R): p.val.card ≤ Fintype.card V:= (grade_hunger _ (fun i=>i.property) p.val p.prop.2).trans (Finset.card_le_univ _)
lemma excellent (p:Notice R) : Fits (slate R s) ((tag R s p).val):= by
 constructor
 · intro i hi j hj h; obtain ⟨i,ha,rfl⟩:=mem_map.mp hi; obtain ⟨j,hb,rfl⟩:=mem_map.mp hj; exact p.prop.2.1 ha hb (mt (fun he=>congr_arg (Dc) he) h)
 change (p.val.map Dc).biUnion _ ∈ _
 refine (?_: (p.val.map Dc).biUnion (fun i=> ((q★) i).val)= p.val.biUnion (fun i=>(ticket R i).val)).symm ▸ p.prop.2.2
 · rw [map_eq_image,Finset.image_biUnion];rfl -- edit
-- ^ .tag equals pack; inverse g map
lemma sieve (p:Notice R): Translation.stamp (slate R s) (τ p)= grade R p:= by
 unfold Translation.stamp; rw [dif_pos (excellent p)]; apply Subtype.ext; unfold unionTag; dsimp only [tag,book,Planet.pack]; rw [map_eq_image,Finset.image_biUnion]; rfl
abbrev pure (p:(Ψ).Mode): Prop:= ∀ i∈p.val,i∈ Set.range (Dc)
lemma excellent_only (p:(Ψ).Mode)(hp:Fits (slate R s) p.val)(he:p.val.Nonempty) : p∈Set.range (tag R s) ↔ pure (s:=s) (R:=R) p:= by
 constructor
 · rintro ⟨z,rfl⟩ i hi; obtain ⟨i,hi,rfl⟩:= mem_map.mp hi; exact ⟨_,rfl⟩
 intro hr; let Q:= p.val.preimage (Dc) (core R s).injective.injOn; have hh: Q.map (Dc)=p.val:= by unfold Q; rw [map_eq_image, Finset.image_preimage]; exact Finset.filter_true_of_mem (fun _i hi=> hr _ hi) -- edit.
 have hQ: Q.Nonempty:= Finset.map_nonempty.mp (hh.symm ▸ he)
 have hu : Fits (ticket R) Q:= ?_
 · exact ⟨⟨Q,hQ,hu⟩,Subtype.ext hh⟩
 constructor
 · intro i hi j hj h; refine hp.1 (hh ▸ mem_map_of_mem _ hi) (hh ▸ mem_map_of_mem _ hj) (show Dc i ≠ Dc j from mt (fun he=> (core R s).injective he) h)
 have ht:= hp.2; rw [← hh, map_eq_image,Finset.image_biUnion] at ht; exact ht
lemma rough (p:(Ψ).Mode)(hp:p∉ Set.range (τ))(he:p.val.Nonempty)(hr:Fits (slate R s) p.val): ∃ i: Payload.deck R s, Sum.inl i∈ p.val:= by
 by_contra h; refine hp ((excellent_only p hr he).2 ?_); rintro (i|i) hi; exact (h ⟨i,hi⟩).elim; exact ⟨i,rfl⟩
-- equality of Tag p Act.Real.S emit and B_Ph model proof.M.Geometry.Res.We.Scene.
open Canopy
variable (d:Notice R)
local notation "Q0"=> (fun (i: d.val)=> (i.val))
lemma chance_univ : Finset.univ.biUnion (fun i:↥d.val=>(ticket R i.val).val)=(d.val.biUnion (fun i=>(ticket R i).val)):=by
 ext a; constructor
 · intro h; obtain ⟨j,hj,hi⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨j.val,j.prop,hi⟩
 intro h; obtain ⟨j,hj,hi⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨⟨j,hj⟩, mem_univ _,hi⟩
lemma pupil : Button.Ideal (fun (i:↥d.val)=> i.val) Finset.univ := by
 refine ⟨?_,?_⟩; · intro i hi j hj h; exact d.prop.2.1 i.prop j.prop (mt Subtype.ext h) -- maybe syntax Fits etc
 change Finset.univ.biUnion (fun i:↥d.val=>(ticket R i.val).val)∈ R.choices; rw [chance_univ]; exact d.prop.2.2 -- edit
lemma pathway : Button.pin (fun i: ↥d.val=>i.val) Finset.univ (pupil d)= grade R d:= by apply Subtype.ext; exact chance_univ d
end Atlas
end YM.Qlocal.Gauges
