import YM.Integration.WilsonMovingForkWindowBooks
import YM.OPE.Cards.Literal

/-! The two original reflected cards on the received weak and pooled fields. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonAddressedPublicSelfCards
open Filter Finset Function Lattice RG Wilson Source Labels OPE Cells Extraction
open PhysicalNext.Repeat.Legato Table Climb GapsContact GapsContact.Ascent Trace Trace.Terrace
open PhysicalNext.Repeat MergeProof.East Next.UVStress Trace.Pilot
open Spec GapsContact.Stamps GapsContact.Seams
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolShell (radius)
open scoped Classical BigOperators

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Arch R.family}
    {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H z D T r)(e:Fin (D+1))(v:S.Field e.val)
local notation "sl" => ((B.stock.department e.val (Nat.le_of_lt_succ e.isLt)).print v)
local notation "C" => R.family

def width (b:Bool) := if b then purchaseWidth B.W else (sl).m
def fee (b:Bool) := if b then dock r*‖(B.V e).symm v‖
  else dock (radius z T r)^T*cost F e.val (radius z T r) v

theorem original (b:Bool) : ∀ᶠ w:ℕ×ℕ in f.fuse,
    Cards.PaidAt (C).S w.1 w.2 (width F B e v b) ((C).beta w.1 w.2) (fee F B e v b)
      ((C).O w.1 w.2 (((B.rows e).arm b v).source w) 0):=by
  cases b
  · rw [(B.rows e).pooled]
    exact (sl).reflected
  · exact (B.rows e).reflected v

theorem weak (priced:WilsonMovingForkWindowBooks.Priced F B)(pos:0≤ dock r) :
    fee F B e v true ≤ dock r ^ 2 * cost F e.val r v := by
  change dock r * ‖(B.V e).symm v‖ ≤ _
  rw [pow_two,mul_assoc]
  exact mul_le_mul_of_nonneg_left (priced e v) pos

variable {I:Type}[Fintype I]{N p:ℕ}

include F in
/-- Each occupied cell has its own original width, test and signed orientation. -/
theorem placed (k:I→ℕ)(A:I→ℝ)(col:I→ Config G ((C).side N p)→ℂ)
    (card:∀i,Cards.PaidAt (C).S N p (k i) ((C).beta N p) (A i) (col i))
    (T:Tiling ((C).side N p))(b:I→Bool)(s:I→Signed)(ds:∀i,Push.RelayDifference.diag (s i))
    (o:I→Site ((C).side N p))(cell:I→T.Cell)(ind:Injective cell)
    (div:∀i,span (C).S (card i).live p ∣ T.side.val)
    (near:∀i,o i∈T.margin (cell i) (3*span (C).S (card i).live p)) :
    ‖moment ((C).beta N p) (fun U=>∏i,Push.RelayDifference.oriented (col i) (b i) (s i) (o i) U)‖
      ≤∏i,A i:=by
  have law:=Cells.seamless F.room.cutoff N p
  choose u χ σ hu point hd he interior price using
    fun i=>(card i).at_cell T (b i) (s i) (ds i) (div i) (near i) law
  simp_rw [←he]
  exact (T.planted law cell ind _ interior).trans
    (Finset.prod_le_prod (fun i _=>T.root_nonneg _ _) (fun i _=>price i))

end YM.Integration.WilsonAddressedPublicSelfCards
end
