import YM.Integration.WilsonPositionProgramTrialHomeDose

/-! Reissue one accrued physical coordinate through the kinetic chart of a second vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialHomeReprint
open Function Finset Matrix Lattice Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Shard
open WilsonPositionProgramTrialAccrued (home returns)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramTrialFittedTable (change)
open WilsonPositionProgramTrialPublicSlope (grade)
open WilsonPositionProgramTrialReverseLens (received)
open scoped BigOperators Classical
variable {G:Gauge}{k u e:ℕ}{H:Hol G}(Q:SealR G){w:Rails Q.h k u e}{E W B V:Credit}
variable (X:CutsP H Q.ans Q.path w E W B V)

def print (M:ℕ):Q.Rider:=received X.ax X.tx Q X.m X.ceilC M (home Q X)

def row (M j:ℕ):Wall Q.F:=change X.ax X.tx Q M X.m X.ceilC j

theorem issued {M:ℕ}(live:X.ceilC ≤ M):
    ticket X.ax X.tx Q M X.m X.ceilC (print Q X M)=home Q X ∧
    print Q X X.N=X.tileP ∧ IsUnit (row Q X M 0).det ∧
    grade (print Q X M) 0=(row Q X M 0)⁻¹ *ᵥ grade (home Q X) 0 ∧
    grade (print Q X M) 1=(row Q X M 0)⁻¹ *ᵥ
      (grade (home Q X) 1-row Q X M 1 *ᵥ ((row Q X M 0)⁻¹ *ᵥ grade (home Q X) 0)):=by
  have before:X.m ≤ X.ceilC:=Nat.le_add_right X.m X.i
  exact ⟨WilsonPositionProgramTrialReverseLens.field H Q X.L.L X.ha before live (home Q X),
    (returns Q X).1,WilsonPositionProgramTrialInverseJet.regular H Q X.L.L X.ha before live,
    WilsonPositionProgramTrialInverseJet.solved H Q X.L.L X.ha before live (home Q X)⟩

theorem original {M:ℕ}(live:X.ceilC ≤ M):
    let z:=print Q X M
    let t:=X.tileP
    let A:=row Q X X.N 0
    let B:=row Q X X.N 1
    let C:=row Q X M 0
    let D:=row Q X M 1
    C *ᵥ (grade z 0-grade t 0)=(A-C) *ᵥ grade t 0 ∧
    C *ᵥ (grade z 1-grade t 1)=(A-C) *ᵥ grade t 1+
      (B-D) *ᵥ grade t 0-D *ᵥ (grade z 0-grade t 0):=by
  intro z t A B C D
  have before:X.m ≤ X.ceilC:=Nat.le_add_right X.m X.i
  have reads {P:ℕ}(hp:X.ceilC ≤ P):
      row Q X P 0 *ᵥ grade (print Q X P) 0=grade (home Q X) 0 ∧
      row Q X P 1 *ᵥ grade (print Q X P) 0+
        row Q X P 0 *ᵥ grade (print Q X P) 1=grade (home Q X) 1:=
    WilsonPositionProgramTrialPublicSlope.reported Q P X.m X.ceilC H X.L.L X.ha before hp
      X.L.L.V.hG X.L.L.V.green (home Q X)
  have old:=reads (X.hc.trans X.hn)
  rw [(issued Q X live).2.1] at old
  change A *ᵥ grade t 0=_ ∧ B *ᵥ grade t 0+A *ᵥ grade t 1=_ at old
  have fresh:=reads live
  change C *ᵥ grade z 0=_ ∧ D *ᵥ grade z 0+C *ᵥ grade z 1=_ at fresh
  constructor
  · rw [Matrix.mulVec_sub,Matrix.sub_mulVec,old.1,fresh.1]
  · have both:=fresh.2.trans old.2.symm
    rw [Matrix.mulVec_sub,Matrix.sub_mulVec,Matrix.sub_mulVec,Matrix.mulVec_sub]
    rw [show C *ᵥ grade z 1=(B *ᵥ grade t 0+A *ᵥ grade t 1)-D *ᵥ grade z 0 from by
      rw [←both]; abel]
    abel

end YM.Integration.WilsonPositionProgramTrialHomeReprint

