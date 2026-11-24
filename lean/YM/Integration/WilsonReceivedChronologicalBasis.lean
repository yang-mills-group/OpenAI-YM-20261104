import YM.Integration.WilsonReceivedChronologicalPlant
import YM.Integration.WilsonReceivedCanonicalVersePosterior

/-! Each independently commissioned canonical socket enters the original complete K source once. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalBasis
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker
open PhysicalNext.Repeat.Legato WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open MergeProof.Accent Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
open WilsonOriginalMicroscopicGuardedTrial (raw)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){h:Fin 3→ℕ}
variable (κ:(j:Fin 3)→Knob (h j))(pt:Fin 3→Chamber)
variable {N per f n:ℕ}(o:Fin 3→Site (R.family.side f per))(v:∀a:Fin 3,R.family.label (d a))(c:Fin 3→ℂ)
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
local notation "J" => Stock.census (Fin 3)

def fare (N per day:ℕ)(s:(J).Mode)(choice:Selection R d s.val):ℂ:=
  (mass c s*units R d day s)*weight R d N per day v s.val choice

/-- This is an equality before integration at the actual unaliased lifted sites, including the blank. -/
theorem top (active:f+n≤N)(s:(J).Mode)(U:Config G (R.family.side K per)):
    (WilsonReceivedChronologicalPlant.top R d (N:=N) (n:=n) o v c U).part s=
      ∑q:Selection R d s.val,fare R d v c N per K s q*
        ((R.family.path.rep N per K).eval U*
          WilsonReceivedCanonicalVersePosterior.word R d κ pt (regulatorRun R.family N per K) (pin R fk o) s.val q U):=by
  have expanded:=WilsonReceivedCanonicalVerseBasis.faces R d κ pt N per K active v (pin R fk o) s.val U
  change mass c s*(((R.family.path.rep N per K).eval U:ℝ) • (units R d K s*
    ∏a∈s.val,WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K ((pin R fk o) a) (v a) U))=_
  rw [←prod_coe_sort,expanded,Complex.real_smul]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro q _
  unfold fare WilsonReceivedCanonicalVersePortfolio.weight WilsonReceivedCanonicalVersePosterior.word
  ring

theorem priced (N per day:ℕ)(active:day≤N)(s:(J).Mode)(cap:Fin 3→ℝ)
    (paid:∀a∈s.val,(R.family.labels.level (d a)).coeffSize (v a) ≤ cap a):
    (∑q:Selection R d s.val,‖fare R d v c N per day s q‖) ≤
      ‖mass c s*units R d day s‖*wallet R d cap s.val:=by
  simp only [fare,norm_mul,←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (WilsonReceivedCanonicalVersePortfolio.priced R d N per day active v s.val cap paid) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
end YM.Integration.WilsonReceivedChronologicalBasis
end
