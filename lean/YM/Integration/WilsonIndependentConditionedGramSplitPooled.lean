import YM.Integration.WilsonIndependentConditionedGramSplitFields
import YM.Integration.WilsonIndependentConditionedGramPooledHome

/-! The two actual physical inputs of a priced Gram may be selected
from any appointed finite roster. Each occurrence retains its own colour. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramSplitPooled
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato GapsContact Climb Maxwell Maxwell.Free Next.Rank Next.Rank.Station
open RG16 RG16.Literal OPE Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReflectedPublicStationFare (station fee)
open WilsonMovingForkOpticalBook (reporter)
open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonIndependentConditionedBankRawUnits (home)
open WilsonIndependentConditionedGramRawHome (fixed)
open WilsonIndependentConditionedGramSplitAward (homeLow homeHigh)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I]
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "J" => Fin 2

def marked {D T:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(ρ:I→{s:ℝ // 0<s ∧ s<δ})
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)(flag:Bool)(η:ℝ)(α:ℂ)(i:I):ℝ:=
  let L:=(books (ρ i)).rows (d i)
  home R (d i).val (station F L flag) (reporter F books ρ) η α
    (fee F L flag (field i (ρ i) flag))

theorem on_book {D T:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(ρ:I→{s:ℝ // 0<s ∧ s<δ})
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)(M:I→ℝ)(E:I→ℕ)
    (paid:Paid F D T d books field M E ρ (reporter F books ρ))
    (flag:J→Bool)(η:ℝ)(small:η ≤ 1)(α:J→ℂ)(dose:∀i,‖α i‖ ≤ 1)
    (choose:J→I)(c:J→ℝ)(colour:∀s,0 ≤ c s)(q:ℕ)(U inv V:ℝ)(P:J→ℝ)
    (uP:0 ≤ U)(iP:0 ≤ inv)(vP:0 ≤ V)(registered:∀s,0 ≤ P s):
    let f:=reporter F books ρ
    let raw:=fun s=>marked F books ρ field (flag s) η (α s) (choose s)*c s
    let cap:=fun s=>M (choose s)*fixed R (d (choose s)).val*c s
    let E₀:=E (choose 0);let E₁:=E (choose 1)
    homeLow q U inv raw ≤ homeLow q U inv cap*(β f)^(E₀+E₁) ∧
    homeHigh q U P raw V ≤ homeHigh q U P cap V*(β f)^(E₀+E₁+max E₀ E₁):=by
  intro f raw cap E₀ E₁
  have priced (s:J):=(WilsonIndependentConditionedGramPooledHome.on_book F D T d books ρ field M E paid
    (fun _=>flag s) η small (fun _=>α s) (fun _=>dose s) (fun _=>1) (fun _=>zero_le_one)).1 (choose s)
  have source (s:J):raw s ≤ cap s*(β f)^(E (choose s)):=calc
    _ ≤ (M (choose s)*fixed R (d (choose s)).val*(β f)^(E (choose s)))*c s:=
      mul_le_mul_of_nonneg_right (priced s).2 (colour s)
    _=_:=by dsimp only [cap];ring
  exact WilsonIndependentConditionedGramSplitFields.original q U inv V (β f) P raw cap _
    uP iP vP (R.family.path.levels.fits.delayed f).le registered
    (fun s=>mul_nonneg (priced s).1 (colour s)) source

end YM.Integration.WilsonIndependentConditionedGramSplitPooled
