import YM.QuadraticLocal.Shelter.Shadows
import YM.QuadraticLocal.Arrow
/-!
 # Field-independent post-global terms, REAL exactly appending
 No support movement in masks needed. If changing to DIFFERENT
 stencils or paths, pay the full new footprint with all required
 addresses (see Earn.Invoice). Kernel costs here on projected old
 footprint. Support/priority through projections ok.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spire
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n c:Side}{V ι μ: Type}{α:Type}[DecidableEq V] {R:Census V}{o:V→Site n}{P:BudgetPoint}
variable (L:Lamps α ι G P o R) (Q:Lamps α μ G P o R)(w: V→ℝ) {b b₀ d:ℝ} {B:ℕ}
variable (S:StepData c n)(P':BudgetPoint)
def inl (i:Waves L) : Waves (L.join Q):=⟨ Sum.inl i.val,i.prop⟩
def inr (i:Waves Q) : Waves (L.join Q):=⟨ Sum.inr i.val,i.prop⟩
def separate : (Waves L ⊕ Waves Q)≃ Waves (L.join Q):= by
    let f := Sum.elim (inl L Q) (inr L Q); refine Equiv.ofBijective f ⟨?_,?_⟩
    · rintro (i|i) (j|j) h
      · exact congr_arg Sum.inl (Subtype.ext (Sum.inl_injective (congr_arg Subtype.val h)))
      · have hv : Sum.inl i.val=Sum.inr j.val:=congr_arg (fun i:Waves (L.join Q)=>i.val) h; cases hv
      · have hv : Sum.inr i.val=Sum.inl j.val:=congr_arg (fun i:Waves (L.join Q)=>i.val) h; cases hv
      exact congr_arg Sum.inr (Subtype.ext (Sum.inr_injective (congr_arg Subtype.val h)))
    rintro ⟨i|i,h⟩; exact ⟨Sum.inl ⟨i,h⟩,rfl⟩; exact ⟨Sum.inr ⟨i,h⟩,rfl⟩
local notation "Φ"=> convertGlobal L S P'
local notation "Ψ"=> convertGlobal Q S P'
lemma split_log (t:α)(v:Config G c)(hs:Summable (fun i=>(convertGlobal (L.join Q) S P').frame i t v)) : (convertGlobal (L.join Q) S P').log t v = (Φ).log t v+ (Ψ).log t v:=by
   classical
   have he:= Lamps.separate (convertGlobal (L.join Q) S P') (separate L Q) (inl L Q) (inr L Q) (fun _=>rfl) (fun _=>rfl) t v hs; exact he
end YM.QuadraticLocal.Spire
