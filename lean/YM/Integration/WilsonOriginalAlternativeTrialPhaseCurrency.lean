import YM.Integration.WilsonOriginalAlternativeTrialSource
import YM.Integration.WilsonMeasuredPublicEntranceGridCurrency

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialPhaseCurrency
open Finset MeasureTheory Lattice Wilson RG Marker QuadraticLocal.Affinity MergeProof.Accent
open PhysicalNext.Repeat.Legato WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable {V:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V

def amount (r:V→ℝ)(d:V→ℕ)(c:V→ℂ)(a:V):ℂ:=(r a:ℂ)^(d a)*(c a)⁻¹
def mass (c:V→ℂ)(s:(J).Mode):ℂ:=∏a∈s.val,c a
def units (r:V→ℝ)(d:V→ℕ)(s:(J).Mode):ℂ:=∏a∈s.val,(r a:ℂ)^(d a)

theorem restored (r:V→ℝ)(d:V→ℕ)(c:V→ℂ)(s:(J).Mode):
    ∏a∈s.val,amount r d c a=units r d s*(mass c s)⁻¹:=by
  simp only [amount,units,mass,Finset.prod_mul_distrib,Finset.prod_inv_distrib]

theorem cost (r:V→ℝ)(d:V→ℕ)(c:V→ℂ)(positive:∀a,0≤r a)(p:ℂ)(s:(J).Mode):
    ‖p*∏a∈s.val,amount r d c a‖=‖p‖*∏a∈s.val,((r a)^(d a)*‖(c a)⁻¹‖):=by
  simp only [norm_mul,norm_prod,amount,norm_pow,Complex.norm_real,Real.norm_of_nonneg (positive _)]

variable {G:Gauge}(R:Run G)(d:V→ℕ)(N p K:ℕ)(o:V→Site (R.family.side K p))(v:∀a,R.family.label (d a))
    (base c:V→ℂ)
local notation "D" => WilsonOriginalAlternativeFiniteSource.disks (V:=V)
local notation "X" j:max => Config G (R.family.side j p)

theorem entered (x:Wallet D)(s:(J).Mode)(W:X K):
    WilsonOriginalAlternativeTrialSource.mode R d N p K o v (fun a=>c a*base a) x s W=mass c s*WilsonOriginalAlternativeTrialSource.mode R d N p K o v base x s W:=by
  unfold WilsonOriginalAlternativeTrialSource.mode mass
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  unfold WilsonOriginalAlternativeTrialSource.arm
  ring

theorem field {f:ℕ}(fk:f≤K)(x:Wallet D)(s:(J).Mode)(W:X f):
    actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.mode R d N p K o v (fun a=>c a*base a) x s) fk W=
     mass c s*actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.mode R d N p K o v base x s) fk W:=by
  rw [funext (entered R d N p K o v base c x s)]
  exact WilsonMeasuredPublicEntranceGridCurrency.transport R _ _ fk W

theorem signed {f:ℕ}(fk:f≤K)(x:Wallet D)(s:(J).Mode)(r:V→ℝ)(nonzero:∀a,c a≠0)
    (ordinary:X f→ℂ)(W:X f):
    (∏a∈s.val,amount r d c a)*(actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.mode R d N p K o v (fun a=>c a*base a) x s) fk W-ordinary W)=
    units r d s*(actualTransport R.family (N:=N) (WilsonOriginalAlternativeTrialSource.mode R d N p K o v base x s) fk W-(mass c s)⁻¹*ordinary W):=by
  have nz:mass c s≠0:=Finset.prod_ne_zero_iff.mpr (fun a _=>nonzero a)
  rw [restored,field R d N p K o v base c fk x s W]
  field_simp [nz]

end YM.Integration.WilsonOriginalAlternativeTrialPhaseCurrency
end
