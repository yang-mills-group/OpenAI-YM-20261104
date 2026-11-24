import YM.Integration.WilsonPhysicalWeakWallBooks

/-! The genuine signed weak home change acts uniformly on bounded finite public coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakWallBounded
open Extraction Lattice RG Wilson Trace.Physical Trace.Physical.Germ
open Function Set Filter Finset Table Spec Climb Spin Trace Trace.Pilot Next.UVStress
open MergeProof.East Next.Rank Next.Rank.East Maxwell PhysMS PhysMS.Frame
open WilsonPhysicalWeakWallStaff WilsonPhysicalWeakWallBooks WilsonPositionThermometerCapStation
open scoped Topology Classical BigOperators

theorem atBasis {I V:Type}[Fintype I][NormedAddCommGroup V][NormedSpace ℂ V]
    (b:Module.Basis I ℂ V)(A:V ≃ₗ[ℂ] V)(r:ℝ)(held:∀i,‖A (b i)-b i‖≤r)(v:V):
    ‖A v-v‖≤(∑i,‖b.repr v i‖)*r:=by
  have named:(∑i,(b.repr v i) • A (b i))=A v:=by
    calc
      _=∑i,A ((b.repr v i) • b i):=sum_congr rfl fun i _=>(A.map_smul _ _).symm
      _=A (∑i,(b.repr v i) • b i):=(map_sum A _ _).symm
      _=A v:=congrArg A (b.sum_repr v)
  have join:A v-v=∑i,(b.repr v i) • (A (b i)-b i):=by
    simp only [smul_sub,sum_sub_distrib,named,b.sum_repr]
  rw [join,sum_mul]
  exact (norm_sum_le _ _).trans (sum_le_sum fun i _=>by
    rw [norm_smul];exact mul_le_mul_of_nonneg_left (held i) (norm_nonneg _))

abbrev slot {G:Gauge}(C:Family G)(D:ℕ):Type:=
  Σj:Fin (D+1),Fin (Module.finrank ℂ ((Bel C.book).Field j))

def head {G:Gauge}(C:Family G){D:ℕ}(i:slot C D):(Bel C.book).Field i.1:=
  Module.finBasis ℂ _ i.2

def cost {G:Gauge}(C:Family G){d:ℕ}(v:(Bel C.book).Field d):ℝ:=
  ∑i,‖(Module.finBasis ℂ _).repr v i‖

variable {G:Gauge}{R:PhysicalNext.Repeat.Legato.Run G}{f:Extraction.Order}{S:Table R.family.book}
    {l:Ultrafilter (ℕ×ℕ)}{arch:Trace.Terrace.Arch R.family}
    (simple:G.Simple)(F:Final R.family f S)(H:(Bel R.family.book).Hierarchy)
    (bliss:Bliss F l arch H)(D:ℕ)
include bliss in
theorem original:∃w:ℝ→Seats R.family S D,
    (∀m:ℕ,∀ᶠr in trail,Booked (Y:=l) simple F H (fun i:slot R.family D=>i.1) (head R.family) (w r) r m ∧
      ∀j:Fin (D+1),∀v:(Bel R.family.book).Field j,
      ‖((w r).turn j).symm ((w r).frame j v)-v‖≤cost R.family v*costHint m) ∧
    ∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ//0<s ∧ s<δ})→WilsonOriginalTwoFlatPublicBooks.Book F
      (l:=l) H arch D T s.val,∀s,Shared F (books s) (w s.val):=by
  obtain ⟨w,paid,sale⟩:=WilsonPhysicalWeakWallBooks.original F simple bliss D
    (fun i:slot R.family D=>i.1) (head R.family)
  refine ⟨w,fun m=>?_,sale⟩
  filter_upwards [paid m] with r receipt
  refine ⟨receipt,fun j v=>?_⟩
  have priced:=((receipt.2.2 m le_rfl).2).2.2.2.2.2
  have near(i:Fin (Module.finrank ℂ ((Bel R.family.book).Field j))):
      ‖(w r).room.change j (Module.finBasis ℂ _ i)-Module.finBasis ℂ _ i‖≤costHint m:=
    priced ⟨j,i⟩
  have bought:=atBasis (Module.finBasis ℂ _) ((w r).room.change j) (costHint m) near v
  rw [receipt.2.1 j] at bought
  exact bought

end YM.Integration.WilsonPhysicalWeakWallBounded
