import YM.Integration.WilsonOriginalAlternativeFiniteSource
import YM.Integration.WilsonOriginalMicroscopicGuardedTrial

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialSource
open Finset MeasureTheory Lattice Wilson RG Marker QuadraticLocal.Affinity MergeProof.Accent
open PhysicalNext.Repeat.Legato
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] [DecidableEq V] (d:V→ℕ) (N p K:ℕ)
  (o:V→Site (R.family.side K p)) (v:∀j,R.family.label (d j)) (z:V→ℂ)
local notation "J_" => Stock.census V
local notation "D_" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "P_" => R.family.path.rep N p K
def arm (j:V) (U:Config G (R.family.side K p)):ℂ:=
  z j*Extra.Histories.part (R.family.localSection (d j)) (o j) (P_) U (v j)
def cap (j:V):ℝ:=‖z j‖*WilsonOriginalMicroscopicGuardedTrial.cap R (fun _:Fin 3=>d j) N p K (fun _=>v j) 0
def mode (x:Wallet D_) (s:(J_).Mode) (U:Config G (R.family.side K p)):ℂ:=
  ∏j∈s.val,(x j).val*arm R d N p K o v z j U
def source (x:Wallet D_) (U:Config G (R.family.side K p)):Poly J_:=
  ((P_).eval U:ℂ) • word J_ (fun j=>(x j).val*arm R d N p K o v z j U)

omit [Fintype V] [DecidableEq V] in
theorem salary (j:V):Measurable (arm R d N p K o v z j) ∧
    ∀U,‖arm R d N p K o v z j U‖≤cap R d N p K v z j:=by
  have h:=WilsonOriginalMicroscopicGuardedTrial.unary R (fun _:Fin 3=>d j) N p K (fun _=>o j) (fun _=>v j) 0
  refine ⟨measurable_const.mul h.1,fun U=>?_⟩
  rw [arm,norm_mul]
  exact mul_le_mul_of_nonneg_left ((h.2.2 U).1) (norm_nonneg _)

theorem bounded (x:Wallet D_) (s:(J_).Mode):Measurable (mode R d N p K o v z x s) ∧
    ∀U,‖mode R d N p K o v z x s U‖≤∏j∈s.val,cap R d N p K v z j:=by
  refine ⟨Finset.measurable_prod _ fun j _=>measurable_const.mul (salary R d N p K o v z j).1,fun U=>?_⟩
  rw [mode,norm_prod]
  apply prod_le_prod (fun _ _=>norm_nonneg _)
  intro j _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (x j).property).trans ((salary R d N p K o v z j).2 U)

theorem earlier (high:K≤N) (x:Wallet D_) (s:(J_).Mode) {f:ℕ} (lower:f≤K) (U:Config G (R.family.side f p)):
    ‖actualTransport R.family (N:=N) (mode R d N p K o v z x s) lower U‖≤∏j∈s.val,cap R d N p K v z j:=
  actualTransport_norm_le R.family R.makes high (bounded R d N p K o v z x s).2 lower U

theorem prior (high:K≤N) (x:Wallet D_) :Integrable (source R d N p K o v z x) (prior G _):=by
  apply integrable_pi_iff.mpr
  intro s
  obtain ⟨meas,po⟩:=bounded R d N p K o v z x s
  have merged:=actualTransport_weighted_integrable R.family R.makes high meas.aestronglyMeasurable po (le_refl K)
  rw [actualTransport_base R.family R.makes high] at merged
  exact merged

theorem part (x:Wallet D_) (s:(J_).Mode) (U:Config G (R.family.side K p)):
    ((source R d N p K o v z x U).part s)=((P_).eval U) • mode R d N p K o v z x s U:=rfl

end YM.Integration.WilsonOriginalAlternativeTrialSource
