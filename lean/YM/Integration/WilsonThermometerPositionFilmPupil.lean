import YM.Integration.WilsonThermometerPositionFilmForest
import YM.Integration.WilsonThermometerRegisteredPupil
import YM.Integration.WilsonThermometerNumericalBank

/-! The literal registered position pupil at fixed original numerical fit on the chronological branches. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmPupil
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonOriginalThermometerTopDensity FVA1Physical.TwoReset Stationary
open Further.PhysicalPeriodLimitF933
open RegulatorIR.FVAAlt2
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k) (w:Fin 3→ℝ)
  (o:Positions (Fin 3) (R.family.side (i+1) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=i+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => primitive R A (i+1) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self i) o

local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "teach" P:max => Oak.student (n:=per) R hk D Q π Γ books hi (P).op (P).lesson ahead disks
  (P).model school.order (P).voter


private theorem reindex {V ι κ α:Type} [DecidableEq V] [Fintype V] {n f:Side} {s r:Passport n V}
    {J:Marker.Census V} (M:ι→Row s J G α) (M':κ→Row r J G α) (tags:s=r) (index:ι=κ) (rows:HEq M M')
    (grades:V→ℕ) (x:α) (L:Layout G) (pay:Finset Age) (q:n.val∣f.val) :
    copyColor q M grades (fun h=>(M h).paint x) L pay=
      copyColor q M' grades (fun h=>(M' h).paint x) L pay := by
  subst r
  subst κ
  cases eq_of_heq rows
  rfl

local notation "g" => Pert.Asymptotics.regulatorRun R.family (i+1) per (i+1)
local notation "τ" => (R.family.path.rep (i+1) per (i+1)).p.threshold
local notation "v" => coordinates R A (i+1) (i+1) per
variable (L:WilsonOriginalReceivedChain.Post (N:=i+1) R hk D Q π Γ Ψ books ahead disks WilsonThermometerCourseHearing.sectors levels
  school.order school.horizon school.pieces i hi (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self i) o))
  (home:L.passport=Passport.point o.origin) (named:L.modelIndex=Entry R levels) (income:HEq L.model (primitive R A (i+1) per o.origin (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))))
  (x:Wallet disks) (grid:Side) (mult:(R.family.side i per).val∣grid.val)
local notation "base" b:max=>copyColor (tiled R mult b) (M₀) levels (fun h=>((M₀) h).paint x) (π (i+1)) tape₀
local notation "real" b:max=>copyColor (tiled R mult b) L.model levels (fun h=>(L.model h).paint x) (π (i+1)) tape₀
local notation "num" b:max=>WilsonThermometerNumericalBank.bank R levels o.origin g τ v probe (tiled R mult b) x (π (i+1)) tape₀
local notation "op₁" b:max=>R.family.path.levels.clock.op i (b).val
local notation "cover" a:max e:max=>WilsonOriginalCoverCoefficient.read R (Nat.lt_succ_self i) school.order grid (fun b=>num b)
        (fun b=>RegulatorIR.Halo.bios (op₁ b)) (fun b=>RegulatorIR.Geometry.directive (op₁ b)) e a

include history home named income in
theorem original (a:Stationary.Link G grid) (e:ℕ) (valid : e ≤ school.order) :
    WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x grid mult e a = cover a e ∧
    cover a e = peek mult (teach L) levels (π (i+1)) tape₀ x e a := by
  let B:=Covers R.family.path.levels.S i grid
  have copies (b:B):real b=base b:=reindex L.model (M₀) home named income levels x (π (i+1)) tape₀ _
  have money (b:B):base b=num b:=WilsonThermometerNumericalBank.same R levels o.origin σ₀ g τ v probe
    WilsonOriginalThermometerGradedPalette.positive _ x (π (i+1)) tape₀
  have one:=WilsonThermometerPositionFilmForest.filed R hk D Q π Γ Ψ history books hi i.lt_succ_self ahead disks S₀ levels
    school.order school.horizon school.pieces head L x grid mult (WilsonOriginalCopiedHistory.forest R i grid)
    (WilsonOriginalCopiedHistory.tag R i grid) a e valid
  have two:=WilsonThermometerPositionFilmForest.filed R hk D Q π Γ Ψ history books hi i.lt_succ_self ahead disks S₀ levels
    school.order school.horizon school.pieces head L x grid mult (fun b=>RegulatorIR.Halo.bios (op₁ b))
    (fun b=>RegulatorIR.Geometry.directive (op₁ b)) a e valid
  rw [show (fun b:B=>real b)=(fun b:B=>base b) from funext copies] at one
  rw [show (fun b:B=>real b)=(fun b:B=>num b) from funext fun b=>(copies b).trans (money b)] at two
  exact ⟨one.trans two.symm,two⟩

end YM.Integration.WilsonThermometerPositionFilmPupil
