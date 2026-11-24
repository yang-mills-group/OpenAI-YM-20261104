import YM.Integration.WilsonOriginalAlternativeTrialSource
import YM.Integration.WilsonOriginalMicroscopicEntranceSockets
import YM.Integration.WilsonOriginalMicroscopicEntranceGridRow
import YM.Integration.WilsonOriginalMicroscopicEntranceEarlier

/-! The complete signed ordinary entrance on the actual embedded reporters.
The previously issued signed rows keep both of their actual companion functions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceTrialScale
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent Marker
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalMicroscopicGuardedTrial (guarded)
open WilsonOriginalMicroscopicEntranceDeposits (mean reading funded)
open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicEntranceFiling (units supplied)
open WilsonOriginalMicroscopicEntranceGridRow (pin factor entered old signed)
open WilsonThermometerSolitaryExchange (share)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f n:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "X" i:max => Config G (R.family.side i p)
local notation "K" => f+n
local notation "k₀" => Nat.le_add_right f n
variable (live:f+n≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
   (v:∀a:Fin 3,R.family.label (d a))
local notation "raw₀" => old R d ((k₀).trans live) Y o
local notation "seat" => entered R d (N:=N) (n:=n) o v
local notation "mask" => guarded R d N p K (pin R k₀ o) v

local notation "active" => WilsonOriginalAlternativeTrialSource.arm
local notation "fired" => WilsonOriginalAlternativeFiniteSource.fired (V:=Fin 3)
local notation "trialMode" => WilsonOriginalAlternativeTrialSource.mode

def dose (a:Fin 3):ℂ:=(R.family.S.a f/R.family.S.a (f+n):ℝ)^(d a)

theorem arm (a:Fin 3)(U:X K):
    seat a U=factor R d f a*active R d N p K (pin R k₀ o) v (dose R d (f:=f) (n:=n)) a U:=by
  have nz:(R.family.S.a f:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (R.family.S.a_pos f).ne'
  change ((R.family.S.a (f+n):ℂ)^d a)⁻¹*_=((R.family.S.a f:ℂ)^d a)⁻¹*(dose R d (f:=f) (n:=n) a*_)
  simp only [dose,Complex.ofReal_div,div_pow]
  field_simp [nz]
  rfl

theorem face_at (s:(J).Mode)(U:X K):
    face seat s U=units R d f s*trialMode R d N p K (pin R k₀ o) v (dose R d (f:=f) (n:=n)) fired s U:=by
  simp only [face,arm R d (N:=N) (n:=n) o v,Finset.prod_mul_distrib,WilsonOriginalAlternativeTrialSource.mode,
    WilsonOriginalAlternativeFiniteSource.fired,one_mul,units,WilsonOriginalMicroscopicEntranceGridRow.factor]

include live in
theorem original (s:(J).Mode) {u:ℕ}(uk:u≤K)(W:X u):
    actualTransport R.family (N:=N) (face seat s) uk W=units R d f s*
      actualTransport R.family (N:=N) (trialMode R d N p K (pin R k₀ o) v (dose R d (f:=f) (n:=n)) fired s) uk W:=by
  let F:=trialMode R d N p K (pin R k₀ o) v (dose R d (f:=f) (n:=n)) fired s
  have law:face seat s=fun U=>units R d f s*F U:=funext (face_at R d (N:=N) (n:=n) o v s)
  obtain ⟨m,b⟩:=WilsonOriginalAlternativeTrialSource.bounded R d N p K (pin R k₀ o) v (dose R d (f:=f) (n:=n)) fired s
  rw [law]
  exact WilsonOriginalMicroscopicEntranceSockets.scaled R live uk F ⟨m,_,b⟩ _ W

end YM.Integration.WilsonOriginalMicroscopicEntranceTrialScale
end
