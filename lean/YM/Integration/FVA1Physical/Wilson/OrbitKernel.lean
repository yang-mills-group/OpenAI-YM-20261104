import YM.Integration.FVA1Physical.Wilson.OrbitQuotient

/-! Complete the orbit law by a unit point mass on empty fibres. Every regular
fibre has a positive independently computed normalizing mass. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {Q : StepData c f} {R : Rep G f} {out : Rep G c}
variable (F : Forest Q.ratio) (I : Finset F.Free) (A : Set (Config G f))
variable (P φ : Config G f → ℝ)
local notation "κ" => twirl F I
local notation "Ω" => IV F I G

def orbitKernel (U : Config G f) :=
  if angleMass F I (ink A P) U=0 then φ 1 else orbitQuotient F I A P φ U

theorem orbitKernel_unit (U : Config G f) : orbitKernel F I A P 1 U=1 := by
  unfold orbitKernel
  split
  · rfl
  rename_i nonzero
  unfold orbitQuotient
  simp only [Pi.one_apply,mul_one,div_self nonzero]

theorem orbitKernel_invariant (t : Ω) (U : Config G f) :
    orbitKernel F I A P φ (κ t U)=orbitKernel F I A P φ U := by
  unfold orbitKernel; rw [angle_mass_invariant,orbitQuotient_invariant]

theorem orbitKernel_envelope (ha : MeasurableSet A) (hP : Envelope P) (hf : Measurable φ)
    {b : ℝ} (hb : 0 ≤ b) (hφ : ∀ U, |φ U| ≤ b) :
    Measurable (orbitKernel F I A P φ) ∧ ∀ U, |orbitKernel F I A P φ U| ≤ b := by
  have mask : Envelope (spec A) := Envelope.piece ha (Envelope.const 1) (Envelope.const 0)
  have weight : Envelope (ink A P) := mask.mul hP.exp
  have mq := orbitQuotient_envelope F I A P φ ha hP hf hb hφ
  refine ⟨measurable_const.ite (measurableSet_eq_fun (angle_mass_meas F I weight.meas) measurable_const) mq.1,fun U=>?_⟩
  unfold orbitKernel; split
  · exact hφ 1
  exact mq.2 U

variable (W : ForestCell Q R out)
local notation "O" => represent (tint G (Exterior.Body 1 c) W.x)
local notation "area" => hotel W.F W.X W.Y W.J O W.center W.a W.b
local notation "T" => board W.F W.X
local notation "dθ" => fence W.F T G

theorem regular_angle_mass (P : Config G f → ℝ) (hP : Envelope P)
    (U : Config G f) (live : U∈area) : 0 < angleMass W.F T (ink area P) U := by
  let go := fun t : IV W.F T G=>twirl W.F T t U
  let D := go ⁻¹' area
  have mgo : Measurable go := ((twirlD W.F T G).comp (continuous_id.prodMk continuous_const)).measurable
  have ha : MeasurableSet area := (garden_main W.F W.X W.Y W.J O W.center W.voice W.posture.extendsX).from_here
  have mask : Envelope (spec area) := Envelope.piece ha (Envelope.const 1) (Envelope.const 0)
  have cost : Envelope (ink area P) := mask.mul hP.exp
  have integrable : Integrable (fun t=>ink area P (go t)) dθ := (backdrop cost mgo).integrable _
  have rp := W.garden.1
  have m : 0 < Posture.moss G W.radius (board W.F W.X).card := by unfold Posture.moss; positivity
  have chance : 0 < (fence W.F T G).real D :=
    m.trans_le (Posture.spruces W.voice W.posture live W.radius_le W.garden)
  have hit : 0 < (fence W.F T G) D := by
    apply pos_iff_ne_zero.mpr; intro none
    simp only [Measure.real,none,ENNReal.toReal_zero,lt_self_iff_false] at chance
  have support_eq : Function.support (fun t=>ink area P (go t))=D := by
    ext t; change ink area P (go t)≠0 ↔ go t∈area
    by_cases h:go t∈area
    · simp [ink,spec,h]
    simp [ink,spec,h]
  apply (integral_pos_iff_support_of_nonneg (fun t=>mul_nonneg
    (Set.indicator_nonneg (fun _ _=>zero_le_one) (go t)) (Real.exp_pos _).le) integrable).mpr
  change 0 < dθ (Function.support (fun t=>ink area P (go t)))
  rwa [support_eq]

theorem regular_kernel_indicator (P φ : Config G f → ℝ) (hP : Envelope P) :
    angularLaw W.F T area P φ=Set.indicator area (orbitKernel W.F T area P φ) := by
  rw [angularLaw_indicator]; funext U; by_cases live:U∈area
  · simp only [Set.indicator_of_mem live,orbitKernel,if_neg (regular_angle_mass W P hP U live).ne']
  simp only [Set.indicator_of_notMem live]
end YM.Integration.FVA1Physical.Wilson
