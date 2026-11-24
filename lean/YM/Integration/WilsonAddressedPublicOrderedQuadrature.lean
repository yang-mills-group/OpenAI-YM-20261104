import YM.Integration.WilsonAddressedPublicSelfFence
import YM.Integration.WilsonMeasuredPublicEntranceOrderedPins
import YM.Integration.WilsonMeasuredPublicEntranceOrderedRoster
import YM.Integration.WilsonMeasuredPublicEntranceOriginalPair

/-! The true reflected Wilson quadrature and its cutoff-dependent continuum field labels in the two regulator limits. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
namespace YM.Integration.WilsonAddressedPublicOrderedQuadrature
open Function Filter Finset Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonAddressedPublicSelfPurchase (source)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,Bool→S.Field (d i).val)
local notation "C" => R.family
local notation "caps" => grades (d 0).val (d 1).val

theorem at_grid {site N per:ℕ}(later:site ≤ N)(o:Fin 2→ Cover)(Y:(C).book.Vector caps):
    (C).omega N per (word R caps site N per later o Y)=physical caps site o N per Y:=by
  unfold word physical
  simp only [Cells.location,dif_pos later]
  rfl

theorem original {L:Type}[Fintype L](site:ℕ)(o:L→Fin 2→ Cover)
    (generic:∀a,Extraction.Order.grid (C) site (o a)∈YM.generic 2){ε:ℝ}(ep:0<ε):
    ∀ᶠ w:ℕ×ℕ in f.fuse,∀(ax:Axis)(b:Fin 2→Bool)(μ:L→ℂ)(live:site ≤ w.1),
    let Y:=source R F B d (fun i=>v i (b i)) b ax w
    ‖(∑a,μ a*(C).omega w.1 w.2 (word R caps site w.1 w.2 live (o a) Y))-
       ∑a,μ a*publicValue (S:=S) caps site (o a) Y‖ ≤ (∑a,‖μ a‖)*ε:=by
  classical
  obtain ⟨first,cost,_,offered,_,_⟩:=WilsonMeasuredPublicEntranceOrderedRoster.original F B d v
  have ready:∀ᶠ w:ℕ×ℕ in f.fuse,first ≤ w.1:=by
    rw [Extraction.Order.fused]
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop _
  have read (ax:Axis)(b:Fin 2→Bool)(a:L):
      ∀ᶠ w:ℕ×ℕ in f.fuse,
      let Y:=source R F B d (fun i=>v i (b i)) b ax w
      ‖physical caps site (o a) w.1 w.2 Y-publicValue (S:=S) caps site (o a) Y‖≤ε:=by
    let H₀:=WilsonMeasuredPublicEntranceOriginalPair.bounds R ax (d 0).val (cost 0 (b 0)) (cost 1 (b 1))
    obtain ⟨release⟩:=WilsonMeasuredPublicEntranceOrderedPins.original F caps site (o a) (generic a) H₀
    have received:∀ᶠ w:ℕ×ℕ in f.fuse,∀y:(C).book.Vector caps,(∀i,‖y i‖≤H₀ i) →
        ‖physical caps site (o a) w.1 w.2 y-publicValue (S:=S) caps site (o a) y‖≤ε:=by
      rw [Extraction.Order.fused]
      exact WilsonMeasuredPublicEntranceOrderedPins.ordered caps site (o a) release ep
    filter_upwards [ready,received] with w early paid
    apply paid
    exact WilsonMeasuredPublicEntranceOriginalPair.bounded R ax (d 0).val (d 1).val
      (offered w.1 w.2 early 0 (b 0)) (offered w.1 w.2 early 1 (b 1))
  have whole:=eventually_all.mpr fun ax=>eventually_all.mpr fun b=>eventually_all.mpr (read ax b)
  filter_upwards [whole] with w earned ax b μ live Y
  let old:=fun a=>physical caps site (o a) w.1 w.2 Y
  let named:=fun a=>publicValue (S:=S) caps site (o a) Y
  simp_rw [at_grid R d live]
  calc
    ‖(∑a,μ a*old a)-∑a,μ a*named a‖ = ‖∑a,μ a*(old a-named a)‖:=by simp only [mul_sub,sum_sub_distrib]
    _ ≤ ∑a,‖μ a*(old a-named a)‖:=norm_sum_le .. 
    _ ≤ ∑a,‖μ a‖*ε:=sum_le_sum fun a _=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (earned ax b a) (norm_nonneg _)
    _ = _:=by rw [sum_mul]

end YM.Integration.WilsonAddressedPublicOrderedQuadrature
end
