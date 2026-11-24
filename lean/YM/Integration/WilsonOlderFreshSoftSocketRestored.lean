import YM.Integration.WilsonOlderFreshSoftSocketHeard
import YM.Integration.WilsonOlderFreshSoftSocketRemainder
import YM.Integration.WilsonOlderFreshSoftSocketKinetic

/-! Retain the full original old scalar and every later feed, and pay the only remaining finite kinetic loss on the same N-quiet, K-born q. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketRestored
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice)
open WilsonOlderFreshSoftSocketHeard (during)
open WilsonOlderFreshSoftSocketFaces (raw)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonReceivedCanonicalVerseRegister (offer start)
open WilsonOlderFreshSoftSocketKinetic (kinetic reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonOlderFreshHybridClock (flat)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}
local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O
variable (κ:(i:I)→Knob (D i))(pt:I→Chamber)
def degree (S:Finset I)(q:(i:I)→Choice R d i):ℕ:=∑i∈S,WilsonOlderFreshSoftSocketPole.lag R d q i

def stopped (N K c v:ℕ)(cells:Digits L_ I)(y:I → Cover)(S:Finset I)(f:Pen D S→L[ℝ]ℝ)
    (Y:Outerm G D):Era G ℝ:=cruises L_ O_ N (mass d S) c v (during R d N K c cells y S f Y)

def coin (Z:Era G ℝ):Cost:=reading Z.2 Fin.elim0

theorem rated (Z:Era G ℝ)(p:ℕ)(x:ℝ):flat Z p x=value p (coin Z) x:=by
  simp only [flat,WilsonOlderFreshTerminalProgramme.series,value,coin,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]

theorem received (simple:G.Simple)(ratio:LocalRatio O_)(N K c v:ℕ)(cells:Digits L_ I)
    (S:Finset I)(vc:v≤c)(ck:c≤K)(live:K≤N)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)(q:(i:I)→Choice R d i):
    let h:=degree R d S q
    let C:Cost:=X^h*(kinetic L_ O_ N K v)^h
    let H:=stopped R d N K c v cells y S f (raw R d κ pt q)
    let Z:=stopped R d N K c v cells y S f (start R d κ pt q)
    (∀n,H.1 n=affix C (Z.1 n)) ∧ H.2=affix C Z.2 ∧ coin H=X^h*((kinetic L_ O_ N K v)^h*coin Z):=by
  intro h C H Z
  have same:c+(K-c)=K:=Nat.add_sub_of_le ck
  have cut:c+(K-c)≤N:=by omega
  let M:=during R d N K c cells y S f
  let Y:=raw R d κ pt q
  let X₀:=start R d κ pt q
  have high:Wellness d Y:=(OriginalCoverReanchoring.deposited (WilsonOlderFreshSoftSocketPole.raw R d κ pt q)
    (fun _ _=>Nat.le_add_left _ _)).1
  have low:Wellness d X₀:=(OriginalCoverReanchoring.deposited (offer R d κ pt q)
    (fun i _=>WilsonReceivedCanonicalVerseBasis.grade R d κ pt i (q i))).1
  have fresh (W:Outerm G D)(well:Wellness d W):Auth (mass d S) (M W):=
    (placedO _ ((sound L_ O_ d N cells simple ratio W well (K-c) c cut).level' y) S).tuft f
  let b:=clock L_ O_ N K c (X^h)
  have first:∀n,(M Y).1 n=affix b ((M X₀).1 n):=by
    have t:=(WilsonOlderFreshSoftSocketCourse.original R d κ pt q L_ O_ simple ratio N cells S f (K-c) c cut y).1
    rw [same] at t
    exact t
  have total:clock L_ O_ N c v b=C:=by
    rw [show clock L_ O_ N c v b=clock L_ O_ N K v (X^h) from
      WilsonOlderFreshSoftSocketKinetic.combine L_ O_ N K c v vc ck _,
      WilsonOlderFreshSoftSocketKinetic.pole _ _ _ _ _ _ (vc.trans ck)]
  have fin:=WilsonOlderFreshSoftSocketHistory.finite L_ O_ simple ratio N (mass d S) c v vc (ck.trans live)
    (M Y) (M X₀) b (fresh X₀ low) first
  have cov:=WilsonOlderFreshSoftSocketHistory.original L_ O_ simple ratio N (mass d S) c v vc (ck.trans live)
    (M Y) (M X₀) b (fresh Y high) (fresh X₀ low) first
  rw [total] at fin cov
  refine ⟨fin,cov,?_⟩
  change reading H.2 Fin.elim0=_
  rw [show H.2=affix C Z.2 from cov,WilsonOlderFreshSoftSocketKinetic.valued]
  exact mul_assoc _ _ _

theorem original (simple:G.Simple)(ratio:LocalRatio O_)(N per K c v:ℕ)(cells:Digits L_ I)
    (S:Finset I)(vc:v≤c)(ck:c≤K)(live:K≤N)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)
    (q:(i:I)→Choice R d i)(p:ℕ)(kept:degree R d S q≤p){θ:ℝ}(θ0:0≤θ)(θ1:θ≤1):
    let h:=degree R d S q
    let g:=Pert.Asymptotics.regulatorRun R.family N per K
    let A:=kinetic L_ O_ N K v
    let H:=stopped R d N K c v cells y S f (raw R d κ pt q)
    let Z:=stopped R d N K c v cells y S f (start R d κ pt q)
    |(g^h)⁻¹*flat H p θ-flat Z p θ|≤(g^h)⁻¹*
      (θ^(p+1)*((h:ℝ)+2)*(WilsonReportingAbsoluteInletForecastBooks.mass p A)^h+
        |(θ*value p A θ)^h-g^h|)*WilsonReportingAbsoluteInletForecastBooks.mass p (coin Z):=by
  intro h g A H Z
  rw [rated,rated,(received R d κ pt simple ratio N K c v cells S vc ck live y f q).2.2]
  exact WilsonOlderFreshSoftSocketRemainder.original kept A (coin Z) (ActualRunKernelPackets.regulator_pos R N per K live) θ0 θ1

end YM.Integration.WilsonOlderFreshSoftSocketRestored
end
