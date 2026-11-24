import YM.Integration.WilsonReceivedChronologicalMaterialEndpoint
import YM.Integration.WilsonReceivedChronologicalLedger
import YM.Integration.WilsonReceivedChronologicalSocketMix

/-! Evaluate the last ordinary record of the public fixed-site portfolio on the received nonbare group field. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalLastRecord
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Filter MintClock Multi
local notation "H" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))

open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedChronologicalMaterialEndpoint (submitted word)
open WilsonReceivedChronologicalBasis (fare)
open WilsonOriginalMicroscopicEntranceGridRow (pin)
variable {f n:ℕ}(d:Fin 3→ℕ)(o:Fin 3→Site (R.family.side f per))
  (v:∀a:Fin 3,R.family.label (d a))(c:Fin 3→ℂ)
local notation "age" => i+1
local notation "J" => Stock.census (Fin 3)
local notation "X" j:max => Config G (R.family.side j per)
local notation "A" => WilsonOriginalMixedBlockRows.room (Fin 3)
variable {ι:∀s:(J).Mode,Selection R d s.val→Type}
  [∀s y,Fintype (ι s y)]
  (ports:∀(s:(J).Mode)(_y:Selection R d s.val),Earn.Passport (R.family.side (i+1) per) (Fin 3))
  (B:∀s y,ι s y→Earn.Binder (ports s y) (J))
  (q:ℕ)(M:∀s y,WilsonOriginalCensusDatedMaterial.Material R N (i+1) q d
    (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) (B s y))
  (x:∀(s:(J).Mode)(_y:Selection R d s.val),Wallet (A))
  (previous:∀(s:(J).Mode)(_y:Selection R d s.val),∀ j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)))

local notation "records" => fun (s:(J).Mode)(y:Selection R d s.val)=>
  WilsonReceivedChronologicalMaterialEndpoint.submitted R (N:=N) (i:=i) (per:=per) (k:=k) (n:=3) (I:=ι s y) D Ψ (φ:=φ) (ports s y) (B s y) d q (M s y) (x s y)
local notation "rows" => WilsonReceivedChronologicalSocketMix.stock R d (day:=i+1) (records) previous
local notation "wallet" => fare R d v c N per (f+n)
local notation "stamped" => WilsonReceivedChronologicalMixture.mix R (wallet) (rows)
local notation "programme" => WilsonReceivedChronologicalPlant.rows R d (n:=n) (N:=N) o v c (stamped)

include course cut in
theorem original (old:age<f+n)(order shelf:ℕ)(income:Fin 3→ℝ)(tol:ℝ)
    (paid:∀s y,WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson ahead
      (ports s y) (B s y) d order shelf q income (M s y) tol)
    (s:(J).Mode)(U:X (age)):
    WilsonReceivedChronologicalReadout.face R N per (programme) s (age) U =
      ∑y:Selection R d s.val,(wallet) s y*(word R (N:=N) (i:=i) (per:=per) (k:=k) (n:=3) (I:=ι s y) D Ψ (φ:=φ) (ports s y) (B s y) d q (M s y) (x s y) U).part s:=by
  rw [WilsonReceivedChronologicalReadout.face,WilsonReceivedChronologicalPlant.lower R d o v c (stamped) old]
  change ((R.family.path.rep N per (age)).eval U:ℂ)⁻¹*
    (∑y:Selection R d s.val,(wallet) s y*((rows) s y (age) U).part s)=_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  obtain ⟨Z,_ballot,_grades,_location,heard⟩:=WilsonReceivedChronologicalMaterialEndpoint.original
    R hk D Q π Γ Ψ course books hi cut op lesson ahead (ports s y) (B s y) d order shelf q income
      (M s y) tol (paid s y) (x s y)
  rw [WilsonReceivedChronologicalSocketMix.stock,WilsonReceivedChronologicalSocketMix.branch,Function.update_self,mul_left_comm,heard U s]

end YM.Integration.WilsonReceivedChronologicalLastRecord
end
