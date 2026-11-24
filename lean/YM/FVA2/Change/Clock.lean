import YM.FVA2.Change.Series
import YM.FVA2.Slice.Source
import YM.MS.Swirl.Resolute
/-!
# The allowed reparametrization into bare Wilson g

The input of `PhysicalSum` uses the Stripped team, retaining all orders of the coupling but
undoing the canonical changes of field, as literal substitution before performing Wick.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Change
open Function Set Filter Finset
open MS MS.Koszul MS.Plane MS.Orbit Cog MS.Swirl MS.Book Convolve Program
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open MS.Swirl.Near MS.Fleet MS.Native Wilsonian
open Lattice Slice
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{n:Side}
local notation "F" => before G n
variable (t : Team) (x : ℝ)
local notation "κ" => Program.shift t x

lemma literal_clock : NRG (Stripped t) x n G true=substitute κ F := by
  let X:=SendB G n true
  funext i; by_cases hp:i=0; · rw [hp,pay0,nil_before,τ_nil]
  unfold NRG; rw [if_neg hp, style, strip_wobble];
  change promote X (substitute κ (Wilsonian.core G)) i=_
  rw [Program.comm,rules,rules]; refine Finset.sum_congr rfl (fun j _=>?_); by_cases he:j=0
  · rw [he,Program.cut,pow_zero,PowerSeries.coeff_one,if_neg hp, zero_smul,zero_smul]
  rw [before,if_neg he]; rfl

local notation "W" => Master G n true
local notation "p" => σbranch (G:=G) (n:=n)
local notation "N" => NRG (Stripped t) x n G true
lemma end_clock {V : Wick.Formal.Table (FixedMode G n)}{v:Ser} (he:Endμ W p F V v) : Endμ W p N (substitute κ V) (substitute κ v) := by rw [literal_clock]; exact sub_views _ (share t x) p W nil_before he
lemma real_shift : Ren (Program.shift t) := shiftR t
lemma near_identity : Rooted κ ∧ PowerSeries.coeff 1 κ=1 := ⟨share .., ann ..⟩
end YM.FVA2.Change
