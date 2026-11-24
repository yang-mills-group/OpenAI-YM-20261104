import YM.Integration.WilsonOriginalMicroscopicEntrancePurchasedField
import YM.Integration.WilsonMeasuredPublicEntranceGridCurrency

/-! Restore the dose shared by the physical column and its fitted K trial on the actual earlier Wilson law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceDoseGrid
open Finset MeasureTheory Lattice Wilson RG Marker PhysicalNext PhysicalNext.Repeat.Legato
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open OPE.Therm WilsonCoeffUV.Embroider WilsonOriginalMicroscopicEntranceTwoExits
open WilsonOriginalMicroscopicEntranceEarlier WilsonOriginalMicroscopicEntranceGridRow
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f n:ℕ}(o:Fin 3→Site (R.family.side f p))
  (v:∀a,R.family.label (d a))
local notation "J" => Stock.census (Fin 3)
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
local notation "X" i:max => Config G (R.family.side i p)
local notation "slots" => pin R fk o
local notation "one_" => WilsonOriginalAlternativeFiniteSource.fired (V:=Fin 3)
variable (c:Fin 3→ℂ)(s:(J).Mode)
local notation "fee" => fun a=>c a*factor R d K a
local notation "program" => WilsonOriginalAlternativeTrialSource.mode R d N p K slots v fee one_ s

def mass:ℂ:=∏a∈s.val,c a

theorem payable (M:Fin 3→ℝ)(paid:∀a,‖(c a)⁻¹‖≤M a):‖(mass c s)⁻¹‖≤∏a∈s.val,M a:=by
  rw [mass,←Finset.prod_inv_distrib,norm_prod]
  exact prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>paid a)

theorem entered (X₀:X K):program X₀=mass c s*face (WilsonOriginalMicroscopicEntranceGridRow.entered R d (N:=N) (n:=n) o v) s X₀:=by
  unfold WilsonOriginalAlternativeTrialSource.mode mass face
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  simp only [WilsonOriginalAlternativeFiniteSource.fired,one_mul,WilsonOriginalAlternativeTrialSource.arm,
    WilsonOriginalMicroscopicEntranceGridRow.entered,WilsonOriginalMicroscopicGuardedTrial.guarded]
  ring

theorem filed (U:X f):actualTransport R.family (N:=N) program fk U=mass c s*trialFace R d (N:=N) (n:=n) o v s U:=by
  simp_rw [funext (entered R d o v c s)]
  exact WilsonMeasuredPublicEntranceGridCurrency.transport R _ _ fk U

theorem original (nonzero:∀a,c a≠0) (b:X f→ℂ) {u:ℕ}(uf:u≤f)(W:X u)(error:ℝ)
    (paid:‖actualTransport R.family (N:=N) (fun U=>actualTransport R.family (N:=N) program fk U-b U) uf W‖≤error):
    ‖actualTransport R.family (N:=N) (trialFace R d (N:=N) (n:=n) o v s-(fun U=>(mass c s)⁻¹*b U)) uf W‖≤
      ‖(mass c s)⁻¹‖*error:=by
  have nz:mass c s≠0:=Finset.prod_ne_zero_iff.mpr (fun a _=>nonzero a)
  have eq:(trialFace R d (N:=N) (n:=n) o v s-(fun U=>(mass c s)⁻¹*b U))=
      fun U=>(mass c s)⁻¹*(actualTransport R.family (N:=N) program fk U-b U):=by
    funext U
    rw [filed]
    simp only [Pi.sub_apply]
    field_simp [nz]
  rw [eq,WilsonMeasuredPublicEntranceGridCurrency.transport,norm_mul]
  exact mul_le_mul_of_nonneg_left paid (norm_nonneg _)

theorem switch {b k:X f→ℂ}{u:ℕ}(uf:u≤f)(W:X u){e:ℝ}
    (paid:‖actualTransport R.family (N:=N) b uf W-actualTransport R.family (N:=N) k uf W‖≤e):
    ‖actualTransport R.family (N:=N) (fun U=>(mass c s)⁻¹*b U) uf W-
      actualTransport R.family (N:=N) (fun U=>(mass c s)⁻¹*k U) uf W‖≤‖(mass c s)⁻¹‖*e:=by
  rw [WilsonMeasuredPublicEntranceGridCurrency.transport,WilsonMeasuredPublicEntranceGridCurrency.transport,←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left paid (norm_nonneg _)

end YM.Integration.WilsonOriginalMicroscopicEntranceDoseGrid
end
