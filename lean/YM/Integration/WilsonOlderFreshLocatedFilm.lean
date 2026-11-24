import YM.Integration.WilsonTrueProjectedLocatedHistory
import YM.Integration.WilsonOlderFreshPointOriginalReturn

/-! Interpret an original planted occupied push as the spatially located
finite-history density transfer, with its complete engineering normalization. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshLocatedFilm
open Filter MeasureTheory Lattice Wilson RG Extra.Histories Extra.Histories.Relay
open Source Labels Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Tree Marker QuadraticLocal LocalComparison PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open FormalBulk08 City Pose Primer Dawn Real PowerSeries
open WilsonTrueProjectedPointProgram WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {d D N p i : ℕ}
local notation "C₀" => R.family
local notation "ι" => Letter (R.family.labels.level d)
local notation "fine" => R.family.side (i+1) p
local notation "coarse" => R.family.side i p
local notation "phase" => (R.family.path.rep N p (i+1)).beta
local notation "kernel" => R.family.path.levels.clock.op i p
local notation "u" => (Stock.census Unit).fire ()

/-- Project the occupied face before the conditional integration, using the
same admitted full polynomial and the original coarse density normalization. -/
theorem single (k:ℕ) (g:ℝ) (V:Config G fine→ℝ) (F:Config G fine→Poly (Stock.census Unit))
    (word:Config G fine→ℂ) (face:∀U,(F U).part u=word U)
    (paid:Integrable (fun U=>(V U:ℂ) • F U) (prior G fine)) :
    Integrable (fun U=>(V U:ℂ)*word U) (prior G fine) ∧
    ∀W,transition (C:=C₀) d N p i (film V word g k) W=
      ((g^k:ℝ):ℂ)*((((R.family.S.block i).val:ℝ)^d:ℝ):ℂ)*
      (LocalComparison.actualPush R.family N p i (fun U=>(V U:ℂ) • F U) W).part u:=by
  let proj:=(Poly.get u).restrictScalars ℝ
  have revenue:=proj.integrable_comp paid
  have entry(U:Config G fine):proj ((V U:ℂ) • F U)=(V U:ℂ)*word U:=by
    change (V U:ℂ)*(F U).part u=_
    rw [face]
  constructor
  · simpa only [Function.comp_def,entry] using revenue
  intro W
  let slab(U:Config G fine):=(kernel).density phase U W • ((V U:ℂ) • F U)
  have room:Integrable slab (prior G fine):=
    StepData.push_slice (R.family.path.levels.transition_mass i p phase) W _ paid
  have run:(LocalComparison.actualPush R.family N p i (fun U=>(V U:ℂ) • F U) W).part u=
      ∫ U,proj (slab U) ∂prior G fine:=(proj.integral_comp_comm room).symm
  have held(U:Config G fine):proj (slab U)=((kernel).density phase U W:ℂ)*((V U:ℂ)*word U):=by
    dsimp only [slab]
    rw [proj.map_smul,Complex.real_smul,entry]
  rw [run]
  let α:ℂ:=(g^k:ℝ)
  have integrate(U:Config G fine):(kernel).density phase U W • film V word g k U=α • proj (slab U):=by
    rw [held,Complex.real_smul,smul_eq_mul]
    change _*(α*_)=α*(_*_)
    ring
  change (((R.family.S.block i).val:ℂ)^d)*(∫U,(kernel).density phase U W • film V word g k U ∂prior G fine)=_
  simp_rw [integrate]
  rw [integral_smul,smul_eq_mul]
  dsimp only [α]
  push_cast
  ring

/-- The dated real coefficients are exactly the coefficients heard by the
complex finite history, including every lag of the scalar basis element. -/
theorem lower (wood:Primer.Families R.family)(a:hue G)(depth:d<D)
    (digit:∀j,Site (R.family.S.block j))(Q:ℕ)(g:ℝ)(book : ι → Config G coarse → ℂ)
    (t:Fin (Q+1))(b:ι)(U:Config G coarse):
    nextWord R wood a depth digit N i Q g book t b U=
    ∑v:ι,(∑ν:Fin (Q-t.val+1),coeff ν.val (WilsonNeutralPointCourse.transfer R wood a depth digit N i v b)*g^ν.val) • book v U:=by
  change (∑v:ι,(∑ν:Fin (Q-t.val+1),((g^ν.val*coeff ν.val (WilsonNeutralPointCourse.transfer R wood a depth digit N i v b):ℝ):ℂ))*book v U)=_
  apply Finset.sum_congr rfl
  intro v _
  rw [Complex.real_smul]
  push_cast
  apply congrArg (fun z:ℂ=>z*book v U)
  exact Finset.sum_congr rfl (fun _ _=>mul_comm _ _)

end YM.Integration.WilsonOlderFreshLocatedFilm
end
