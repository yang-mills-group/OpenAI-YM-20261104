import YM.OPE.Laying.Contrast
/-! # Reindex preserving EVERY replicated term -/
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
def accreditation (e:I≃J): Fibers I J:=⟨e,e.symm,e.apply_symm_apply⟩
namespace Mask
open Playout Muster.Pigment
variable (e':I≃J)
private lemma fareID (T:Type*)[AddCommMonoid T][SMul ℂ T] (x:I→T)(h:∀ i,(1:ℂ) • x i=x i) : linear e' (fun _=>1) x=x ∘ e'.symm:=by
    funext j; unfold linear; rw [show residents e' j={e'.symm j} from ?_,sum_singleton,h]; rfl
    ext; simp [residents,Equiv.eq_symm_apply]
include h in
lemma alteration (U: Ledger Θ i (pullback (accreditation e') s') F P u φ W₀ x D) (hh : Trial s') : Ledger Θ i s' (F ∘ e'.symm) (fun i=> P i ∘ e'.symm) (fun i=> u i ∘ e'.symm) (φ ∘ e'.symm) (fun i=> W₀ i ∘ e'.symm) x D:=by
   
    refine ⟨U.time,U.limit,hh,fun k hk ht j=> U.slots k hk ht _,fun i=>U.terms _,fun i=> U.stock _, U.rate, ⟨fun i=>U.clock.ready _,fun j i=>U.clock.early _ _,fun j k=>U.clock.paid ..⟩,?_,fun k=>U.progress _ ⟩
    rw [← fareID e' _ F (fun i=>by simp), ← fareID e' _ (P i) (fun i=>by simp)]; refine U.market.changeChannels Θ F e' (fun _=>1) U.limit h.wilson U.terms ?_ ?_ (fun i=>U.market.width _) ?_
    · intro i ht; simp
    · intro j; simp [lifted]
    intro i hi hh hp; apply hi -- defeq
end Mask
end YM.OPE.Log.Book
