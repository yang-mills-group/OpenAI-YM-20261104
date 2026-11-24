import YM.Integration.WilsonReceivedChronologicalTwoStops
import YM.Integration.WilsonOriginalTwoFlatRoseNominated

/-! The connected thermometer on a common finite Wilson board, with both signed date sums. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalConnected
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open Extra.Histories PhysicalNext.Repeat.Legato Planned.GuardedAtom
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonOriginalTwoFlatRoseIdentity (cross)
open WilsonOriginalMicroscopicEntranceDoseBoard (Board source)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicEntranceTwoExits (originalRead)
open WilsonOriginalMicroscopicEntrancePooledBoard (actual)
open WilsonMaxwellThermometerNominatedSecant (bill signed)
open WilsonPositionThermometerConnected (value)
open WilsonThermometerCenteredScalar (face)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f n t:ℕ}
variable {o:Fin 3→Site (R.family.side f per)}(B:Board R d N per f o t)
variable (v:∀a:Fin 3,R.family.label (d a))(c:Fin 3→ℂ)

def moment (s:Finset (Fin 3)):ℂ:=R.family.omega N per (actual R d B (face s) c)

variable (past:∀j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)))
local notation "table" => WilsonReceivedChronologicalPlant.rows R d (n:=n) (N:=N) o v c past
local notation "atW" s:max => WilsonReceivedChronologicalReadout.face R N per (table) (face s)
local notation "owed" i:max => WilsonOriginalJointTrialHearing.fee R N per (v:=i) 1 (table)

def line {u b a:ℕ}(uf:u≤f)(ua:u≤a)(ba:b≤a)(aK:a≤f+n)(active:f+n≤N)
    (s:Finset (Fin 3))(target:ℂ):ℂ:=
  gap R N per u ((ua.trans aK).trans active) (actual R d B (face s) c)+
  mass c (face s)*originalRead R d (p:=per) (f:=f) (n:=n) active (source R B) o v (face s) uf 1+
  (∑j∈Ico a (f+n),(owed u) j (face s))+cross R (N:=N) ua ba (atW s)+
  (∑j∈Ico b a,(owed b) j (face s))+((atW s) b 1-target)

/-- All occupied and proper terms use the same original finite partition function. -/
theorem original {u b a:ℕ}(uf:u≤f)(ua:u≤a)(ba:b≤a)(aK:a≤f+n)(active:f+n≤N)
    (income:∀j,min u b≤j→j<f+n→Integrable (past j) (prior G _))(target:Finset (Fin 3)→ℂ):
    value (moment R d B c)-value target =
      ∑s:Finset (Fin 3),bill (moment R d B c) target s*
          line R d B v c past uf ua ba aK active s (target s):=by
  rw [signed]
  refine sum_congr rfl fun s _=>congrArg (_*·) ?_
  exact WilsonReceivedChronologicalTwoStops.original R d B active v c past uf ua ba aK income (face s) (target s)
end YM.Integration.WilsonReceivedChronologicalConnected
end
