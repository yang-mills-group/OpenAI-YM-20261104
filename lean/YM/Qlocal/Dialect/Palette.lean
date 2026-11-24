import YM.Qlocal.Dialect.Swatch
import YM.Comparison.RG02.Symmetry.Code
/-!
 # Print formula for full conditional Fk in **this registration**. Use Keeper.Book.Lookups REAL orientation from Loom roster. Expose one conflict-free p interaction at a time (can have gaps, or unused Phys marks before Opportunity.State.Scope.Memory.Cookie.Policy). This enables sum to one family `Φ.out` at each timestamp incl positions. Uses same-vac re-expression.We.Tag.Meta.Price.Auth.B. -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Dialect
open Function Finset Set
open Marker MeasureTheory Extra.Trajectories
open Comparison Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Assembly
open Function Filter Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Next.Fluctuations Next.SectorChange Multi PertExtension.Series
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V I J K : Type} [DecidableEq I] [DecidableEq J] [DecidableEq K] [Fintype I][Fintype J][Fintype K]
variable {G:Gauge} {c f:Side}
variable {R:Census I}{X:Census K}
namespace Exhibit
open Join Bulk Keeper
open Reckoner Reckoner.Planet
variable (δ:J→Multi.Hot R) (χ: Colors R G f)
variable (f₀:J→ℝ→ Config G f→ℂ)(v:J→ℂ)
set_option quotPrecheck false
local notation "Φ"=>Multi.Hot R
local notation "Λ"=>Planet.Whole J
local notation "Δ"=>fun i:J=> (δ i).val
local notation "r0"=> Exhibit.room δ
local notation "W"=> shadow δ χ f₀
local notation "F"=> sheets δ χ f₀ v
local notation "τ"=>Translation.morph (fun i:J=>(δ i).val) v (fun i: J=> (δ i).prop)
variable {S:StepData c f}{π:Clip}{L:PathData G}{O:ChartRatio G}
    (K0:Kernel S π L O)(H:Forest S.ratio)(T':S.Choices)
variable (hf:∀ i,ContDiffAt ℝ ω (posed S H (f₀ i)) 0) (x:Exterior.fieldDir G c 1){i r :ℕ}
local notation "F0"=>fun c'=> Order.logMarked (Fk K0 H T' c' x r)
abbrev aperture (p:Finset J)(j:J) :ℂ:= if j∈p then 1 else 0
local notation "K'"=> (indices r)
local notation "τ★"=> morph (τ) K'
local notation "Ψ"=>fun c'=> Order.observe R r (Order.logMarked (Fk K0 H T' c' x r)) i
local notation "Ο"=> Order.observe (Whole J) r
local notation "G!"=> Ο (Order.logMarked (Fk K0 H T' W x r)) i
local notation "f★"=> Symmetry.Orbit.words
include hf
lemma canon (i:ℕ) : morph (τ) (indices i) (Fk K0 H T' W x i)= Fk K0 H T' F x i:=
 Keeper.Fk_natural τ (fun s => Translation.preserveQ (Δ) v (fun i: J=>(δ i).prop) s) K0 H T' x W (Exhibit.sheets δ χ f₀ v) rfl (fun x i he=> transported δ χ f₀ v H hf i x)
-- confirm `.detail` eq. formula. Cursor Ω proof below
noncomputable abbrev page (p : (Whole J).Mode):ℂ:= (G!).part p -- parameters including i r
local notation "tag"=> Translation.stamp (Δ)
local notation "D0"=> Translation.falls (Δ)
local notation "Bp"=> page (i:=i) (r:=r) δ χ f₀ K0 H T' x
local notation "Game"=> f★ K0 H T' -- needs Contact.RG02 universes
lemma optic (he:i≤r) (p:R.Mode) : f★ K0 H T' (sheets δ χ f₀ v) r p i x = ∑ t:(Λ).Mode, if p= Translation.stamp (Δ) t then (page (i:=i) (r:=r) δ χ f₀ K0 H T' x t)* Translation.falls (Δ) v t else 0:= by
 change ((Ψ) (F)).part p=_; dsimp only; rw [← canon δ χ f₀ v K0 H T' hf x r,← Keeper.log τ (Translation.preserveQ (Δ) v (fun i: J=>(δ i).prop)) _ (fk_unit ..), Keeper.take_orders (T:=τ) _ he,Translation.part (Δ) v]
-- Policy for injecting one input p with mask.Deferral
abbrev relevant (s:R.Mode)(t:(Whole J).Mode):Prop:= Fits (fun i=> (δ i).val) t.val∧ Translation.stamp (Δ) t=s
omit hf
lemma shuffled (z:(Λ).Mode)(y:(Λ).Mode)(hp: y.val⊆ z.val)(ht:Fits (fun i=>(δ i).val) z.val) (hq: Translation.stamp (Δ) y=Translation.stamp (Δ) z): y=z:=by
 have h: Fits (Δ) y.val:= ht.subset _ hp; unfold Translation.stamp at hq; rw [dif_pos h,dif_pos ht] at hq; apply Subtype.ext; apply Finset.Subset.antisymm hp; intro i hi; by_contra hV; obtain ⟨a,ha⟩:= (δ i).property; have hv:a∈(unionTag (Δ) y.val h).val:= hq.symm ▸ (show a ∈(unionTag (Δ) z.val ht).val from Finset.mem_biUnion.mpr ⟨i,hi,ha⟩)
 obtain ⟨j,hj,hv'⟩:= Finset.mem_biUnion.mp hv; exact Finset.disjoint_left.mp (ht.1 hi (hp hj) (fun he=>hV (he.symm ▸ hj))) ha hv'
lemma darken (u:(Λ).Mode)(s:R.Mode)(h:¬ relevant δ s u)(p:ℂ) : (if s=tag u then p*D0 v u else 0) = 0:= by
 split
 next h'=> rw [Translation.falls,if_neg (fun he=> h ⟨he,h'.symm⟩),mul_zero]
 next => rfl
lemma splinter (z:(Λ).Mode)(s:R.Mode)(t:(Λ).Mode)(hu:relevant δ s z)(h:t≠z)(p:ℂ): (if s=tag t then p * D0 (aperture z.val) t else 0)=0:= by
 by_cases hp:relevant δ s t; swap; · exact darken δ (aperture z.val) t s hp p
 have he:¬ t.val⊆ z.val:= fun hh=> h (shuffled δ z t hh hu.1 (hp.2.trans hu.2.symm)); obtain ⟨i,hv,hi⟩:=Finset.not_subset.mp he; unfold Translation.falls; rw [if_pos hp.2.symm,if_pos hp.1, Finset.prod_eq_zero hv (show aperture z.val i=0 from if_neg hi),mul_zero] -- `if_pos` order
include hf
noncomputable abbrev wake (s:R.Mode)(z:(Whole J).Mode) := f★ K0 H T' (sheets δ χ f₀ (aperture z.val)) r s i x
local notation "R0"=> wake (r:=r) (i:=i) δ χ f₀ K0 H T' x
lemma readership (z:(Λ).Mode)(s:R.Mode)(he:i≤r)(hz:relevant δ s z): R0 s z= Bp z:= by
 unfold Exhibit.wake; rw [optic δ χ f₀ (aperture z.val) K0 H T' hf x he s,Finset.sum_eq_single z,if_pos hz.2.symm]; unfold Translation.falls; rw [if_pos hz.1, Finset.prod_eq_one (fun y hy=>?_),mul_one]; exact if_pos hy
 · intro x hx hv; exact splinter δ z s x hz hv _
 simp
noncomputable abbrev circuit (s:R.Mode):= univ.filter (fun v=>Exhibit.relevant δ s v)
lemma switch (s:R.Mode) (he:i≤r) : Symmetry.Orbit.words K0 H T' (sheets δ χ f₀ v) r s i x= ∑ z∈(circuit δ s), (Exhibit.wake (r:=r) (i:=i) δ χ f₀ K0 H T' x s z)* (∏ j∈z.val,v j):= by
 unfold circuit; rw [optic δ χ f₀ v K0 H T' hf x he s,Finset.sum_filter]; refine Finset.sum_congr rfl fun t _=>?_; by_cases hz: relevant δ s t; · rw [if_pos hz, readership δ χ f₀ K0 H T' hf x t s he hz, if_pos hz.2.symm,Translation.falls, if_pos hz.1]
 rw [if_neg hz]; exact Exhibit.darken δ v t s hz _
-- use as kernel truth.Binder.Actor.Meta.Work.Manuscript. PanoramaHe
end Exhibit
end YM.Qlocal.Dialect
