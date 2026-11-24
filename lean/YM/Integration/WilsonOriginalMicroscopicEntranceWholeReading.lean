import YM.Integration.WilsonOriginalMicroscopicEntranceMaskDebt
import YM.Integration.WilsonOriginalMicroscopicEntranceCropFields
import YM.Integration.WilsonOriginalMicroscopicEntranceResidualStock

/-! The remaining genuine mixed income and the fully heard masked field terms
share a single physical older conditional and its actual positive denominator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceWholeReading
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
open WilsonOriginalMicroscopicEntranceGridStock (debt peer Filed account old_paid entered_paid panel)
open WilsonOriginalMicroscopicEntranceResidualStock (remainder)
open WilsonOriginalMicroscopicEntranceSockets (read)
open WilsonOriginalMicroscopicGuardedTrial (gap raw)
open Analysis Table Extraction GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open WilsonCoeffUV.Embroider
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


variable (B:Fin 3→ℝ)(Z:∀a:Fin 3,store R.family (d a) p f)

open WilsonOriginalMicroscopicEntranceMaskDebt (debit)

def filedTable (first second:X f→Fin 3→ℂ)(s:(J).Mode)(U:X f):ℂ:=
  let E:=fun a W=>share (first W) (second W) a s
  debit R (N:=N) raw₀ ((k₀).trans live) first E s U-debit R (N:=N) seat k₀ second E s U+
    ∑a:Fin 3,signed R d (N:=N) a (o a) (Z a) U*E a U

theorem original {h:Fin 3→ℕ}(κ:(a:Fin 3)→Knob (h a))(pt:Fin 3→Chamber)
    (mature:∀a,R.family.ref (d a)≤f)(filed:Filed R d (N:=N) (n:=n) Y o v B Z)
    (first second:X f→Fin 3→ℂ)(s:(J).Mode){u:ℕ}(uf:u≤f)(W:X u):
    let upper:=pin R ((k₀).trans live) o
    let sites:=pin R k₀ o
    let observed:=actualTransport R.family (N:=N) (filedTable R d live Y o v Z first second s) uf W
    read R d Y upper live (uf.trans k₀) mask s W=observed ∧
    read R d Y upper live (uf.trans k₀) (raw R d N p K sites v) s W-observed=
      -(units R d K s*actualTransport R.family (N:=N) (gap R d N p K sites v s.val) (uf.trans k₀) W):=by
  intro upper sites observed
  let E:=fun a W=>share (first W) (second W) a s
  have tab:account R d live Y o v Z s=filedTable R d live Y o v Z first second s:=by
    funext U
    rw [WilsonOriginalMicroscopicEntranceResidualStock.total R d live Y o v Z s E U,
        WilsonOriginalMicroscopicEntranceMaskDebt.original R d live Y o v B Z mature filed first second s U]
    rfl
  have original:=WilsonOriginalMicroscopicEntranceGridStock.original R d live Y o v B Z mature filed s uf W
  rw [tab] at original
  have correction:=WilsonOriginalMicroscopicEntranceSockets.correction R d κ pt Y upper sites v live (uf.trans k₀) s W
  rw [original] at correction
  exact ⟨original,by dsimp only [observed];linear_combination correction⟩

end YM.Integration.WilsonOriginalMicroscopicEntranceWholeReading
end
