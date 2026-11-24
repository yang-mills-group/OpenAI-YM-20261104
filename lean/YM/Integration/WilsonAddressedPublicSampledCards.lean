import YM.Integration.WilsonAddressedPublicSelfRoom

/-! The signed, finite physical quadrature with both original reflected cards. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonAddressedPublicSampledCards
open Filter Finset Function Lattice RG Wilson Source Labels OPE Cells Extraction Spec
open PhysicalNext.Repeat.Legato Table Climb GapsContact GapsContact.Ascent Trace Trace.Terrace
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicSelfCards (width fee)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Arch R.family}
    {I:Type}[Fintype I]{D T:ℕ}{r:I→ℝ}
    (B:∀i,Book F (l:=l) H z D T (r i))(d:I→Fin (D+1))(v:∀i,S.Field (d i).val)(b:I→Bool)
local notation "C" => R.family
local notation "widths" => (fun i=>width F (B i) (d i) (v i) (b i))
local notation "fees" => (fun i=>fee F (B i) (d i) (v i) (b i))

def leaf (w:ℕ×ℕ)(i:I) := (C).O w.1 w.2 ((((B i).rows (d i)).arm (b i) (v i)).source w) 0

theorem original : ∀ᶠ w:ℕ×ℕ in f.fuse,
    ∀(j m:ℕ),j ≤ m → m ≤ w.1 → (∀i,m ≤ widths i) →
    (Fintype.card I:ℝ)*(2*(3*(C).S.a m))<(C).S.a j →
    ∀(L:Type)[Fintype L](u:L→I→Site ((C).side w.1 w.2))(μ:L→ℂ)
      (conj:L→I→Bool)(motion:L→I→Signed), (∀a i,Push.RelayDifference.diag (motion a i)) →
    (∀a i i',i≠i' → (C).S.a j < (C).S.a w.1*(separation (u a i) (u a i'):ℝ)) →
    ‖∑a,μ a*moment ((C).beta w.1 w.2) (fun U=>∏i,Push.RelayDifference.oriented
      (leaf F B d v b w i) (conj a i) (motion a i) (u a i) U)‖ ≤
    (∑a,‖μ a‖)*∏i,fees i:=by
  filter_upwards [eventually_all.mpr (fun i=>WilsonAddressedPublicSelfCards.original
    F (B i) (d i) (v i) (b i))] with w cards
  intro j m before fresh later money L inst u μ conj motion diag apart
  rw [Finset.sum_mul]
  apply (norm_sum_le ..).trans
  refine Finset.sum_le_sum fun a _=>?_
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  obtain ⟨board⟩:=WilsonAddressedPublicSelfRoom.original (R:=R) widths (u a)
    before fresh later (fun i=>(cards i).live) money (apart a)
  exact WilsonAddressedPublicSelfCards.placed F widths fees (leaf F B d v b w) cards
    board.tile (conj a) (motion a) (diag a) (u a) (fun i=>board.tile.which (u a i))
    board.distinct board.divides board.sits

end YM.Integration.WilsonAddressedPublicSampledCards
end
