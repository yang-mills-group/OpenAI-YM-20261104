import YM.Integration.WilsonOriginalMicroscopicEntranceDoseGrid
import YM.Integration.WilsonOriginalMicroscopicEntranceDoseWallet

/-! Restore the N-born full public source after its direct comparison with the actual lower ordinary product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePooledCutoff
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address WilsonOriginalNullCorridor Marker
open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicEntranceGridRow (pin old)
open WilsonOriginalMicroscopicEntranceGridStock (old_paid)
open WilsonOriginalMicroscopicEntranceTwoExits
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f n u:ℕ}
  (live:f+n≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
  (s:(Stock.census (Fin 3)).Mode)(c:Fin 3→ℂ)(nz:∀a,c a≠0)
local notation "fk" => Nat.le_add_right f n
local notation "X" i:max => Config G (R.family.side i p)

def sourced (U:X N):ℂ:=∏a∈s.val,c a*R.family.O N p (Y a) (pin R ((fk).trans live) o a) U

include nz in
theorem original (b:X f→ℂ)(uf:u≤f)(W:X u){fee:ℝ}
    (finite:Integrable (fun U=>(R.family.path.rep N p f).eval U • b U) (prior G _))
    (paid:‖actualTransport R.family (N:=N) (sourced R d live Y o s c) (uf.trans ((fk).trans live)) W-
           actualTransport R.family (N:=N) b uf W‖≤fee):
    ‖actualTransport R.family (N:=N) (cutoffFace R d live Y o s-(fun U=>(mass c s)⁻¹*b U)) uf W‖≤
      ‖(mass c s)⁻¹‖*fee:=by
  let a:=old R d ((fk).trans live) Y o
  have name:sourced R d live Y o s c=fun U=>mass c s*face a s U:=by
    funext U
    unfold sourced mass face
    rw [←Finset.prod_mul_distrib]
    rfl
  have nonzero:mass c s≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>nz i)
  have restored:=WilsonOriginalMicroscopicEntranceDoseWallet.integrable _ b (mass c s)⁻¹ finite
  obtain ⟨meas,_,bound⟩:=salary a (old_paid R d live Y o) s
  have left:=actualTransport_weighted_integrable R.family R.makes (le_refl N) meas.aestronglyMeasurable bound ((fk).trans live)
  have sub:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes ((fk).trans live) left restored uf) W
  simp only [actualTransport_tower R.family R.makes (le_refl N)] at sub
  rw [name,WilsonMeasuredPublicEntranceGridCurrency.transport] at paid
  change ‖actualTransport R.family (N:=N) (fun U=>actualTransport R.family (N:=N) (face a s) ((fk).trans live) U-(mass c s)⁻¹*b U) uf W‖≤_
  rw [sub,WilsonMeasuredPublicEntranceGridCurrency.transport]
  calc
    _=‖(mass c s)⁻¹*(mass c s*actualTransport R.family (N:=N) (face a s) (uf.trans ((fk).trans live)) W-
        actualTransport R.family (N:=N) b uf W)‖:=by rw [mul_sub,←mul_assoc,inv_mul_cancel₀ nonzero,one_mul]
    _≤_:=by rw [norm_mul]; exact mul_le_mul_of_nonneg_left paid (norm_nonneg _)
end YM.Integration.WilsonOriginalMicroscopicEntrancePooledCutoff
end
