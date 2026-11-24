import YM.Integration.WilsonOriginalMicroscopicEntranceFiling
import YM.Integration.WilsonReflectedTwoGridFields
import YM.Integration.WilsonReflectedPlacedArm
import YM.Integration.WilsonOriginalMicroscopicGuardedGridSchool
import YM.Integration.WilsonOriginalMicroscopicEntranceSockets

/-! A previously filed signed germ on a translated common physical site measures
the two true normalized source means at the actual upper and restart ages. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceGridRow
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalMicroscopicGuardedGridSchool WilsonOriginalMicroscopicGuardedPage
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonOriginalMicroscopicGuardedTrial (guarded)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f n:ℕ}
local notation "X" i:max => Config G (R.family.side i p)
local notation "K" => f+n
local notation "P" => R.family.path.rep N p f

def pin {b:ℕ}(high:f≤b)(o:Fin 3→Site (R.family.side f p))(a:Fin 3):Site (R.family.side b p):=
    (R.family.S.toDepth high p).embed (o a)

def old (cut:f≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))(a:Fin 3):X N→ℂ:=
    R.family.O N p (Y a) (pin R cut o a)

def factor (age:ℕ)(a:Fin 3):ℂ:=((R.family.S.a age:ℂ)^(d a))⁻¹

def entered (o:Fin 3→Site (R.family.side f p))(v:∀a:Fin 3,R.family.label (d a))(a:Fin 3)(U:X (f+n)):ℂ:=
    factor R d K a*guarded R d N p K (pin R (Nat.le_add_right f n) o) v a U

def signed (a:Fin 3)(o:Site (R.family.side f p))(z:store R.family (d a) p f)(U:X f):ℂ:=
    -(z.density o (R.family.localSection (d a)) P U)/((R.family.S.a f:ℂ)^(d a)*((P).eval U:ℂ))

theorem original (live:f+n≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
    (v:∀a:Fin 3,R.family.label (d a))(a:Fin 3)(ready:R.family.ref (d a)≤f)(B:ℝ)(z:store R.family (d a) p f)
    (own:WilsonAddressedRestartedFiled.Filed R (d a) N p f (o a)
      (track R (d a) N p K (numerator R (d a) N p K 0 (v a)) f-
        calValues (C:=R.family) (d a) N p f ((R.family.factory (d a) N p).terminal.symm (Y a))) B z)(U:X f):
    actualTransport R.family (N:=N) (old R d ((Nat.le_add_right f n).trans live) Y o a) ((Nat.le_add_right f n).trans live) U-
    actualTransport R.family (N:=N) (entered R d (N:=N) (n:=n) o v a) (Nat.le_add_right f n) U=signed R d (N:=N) a (o a) z U:=by
  let k:=Nat.le_add_right f n
  let G₀:=guarded R d N p K (pin R k o) v a
  have fee:=WilsonOriginalMicroscopicEntranceFiling.supplied R d (N:=N) (pin R k o) v a
  have scaled:=WilsonOriginalMicroscopicEntranceSockets.scaled R live k G₀ fee.1 (factor R d K a) U
  have first:=WilsonReflectedTwoGridFields.raw R (d a) (k.trans live) ready (o a) (Y a) U
  have last:=WilsonReflectedTwoGridFields.restarted R (d a) n live (o a) (v a) U
  have obs:=congrFun own.field U
  simp only [Function.comp_apply,Pi.sub_apply] at obs
  rw [first,last] at obs
  have pow:((R.family.S.steps f n).val:ℂ)^(d a)=(R.family.S.a f:ℂ)^(d a)*factor R d K a:=by
    have hk:(R.family.S.a K:ℂ)≠0:=by exact_mod_cast (R.family.S.a_pos K).ne'
    apply (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hk)).2
    rw [←mul_pow];congr 1;exact_mod_cast WilsonReflectedPlacedArm.spacing R f n
  have af:(R.family.S.a f:ℂ)≠0:=by exact_mod_cast (R.family.S.a_pos f).ne'
  have quiet:((P).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson (k.trans live) U).ne'
  rw [pow] at obs
  unfold entered
  rw [scaled]
  unfold signed
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ af) quiet)).2
  rw [obs]
  change (_-_ * actualTransport R.family (N:=N) G₀ k U)*_=
    -(_*_*_*actualTransport R.family (N:=N) G₀ k U-_*_*actualTransport R.family (N:=N) (old R d (k.trans live) Y o a) (k.trans live) U)
  ring

end YM.Integration.WilsonOriginalMicroscopicEntranceGridRow
end
