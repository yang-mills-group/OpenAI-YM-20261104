import YM.RG02.Flat.Lenses
import YM.RG02.Flat.Scalar

/-!
# Stochastic aperture

Restore the normalized *Markov kernel*, parameter powers and Haar
cost. The integrated push (on analytic inputs in flat projection) is
per-coarse-field, not a partition-function average. Gives also the unnormalized
scalar expansion with powers extracted. Use `v` scalar of History outside
this test. Does not give analytic expansion of the full masked/forced
answer nor a moving-window estimate (those remain separate, in
Actual partition/Task 1). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Fk
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories Volume
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries Profiles
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}{c f : Side}{S : StepData c f}

/-- Analytic part of the unmasked incoming WITHOUT scalar. At t=g contract
according to `Draw.formal`. t may be used both in A and W but these are not
functions of tuning offsets. Do not merely assume these reproduce full R! -/
def strip (p : Clip)(R : PathData G)(m : ℕ)(W : Space G f→Poly B)
    (A : Space G f→ℝ)(t : ℝ)(x : Config G f) := Real.exp (-(mainTerm p R x + A (t,x) + t^2* Precision.loop R x)/t^2) •
        Poly.pass (((t:ℂ)^m)⁻¹ • W (t,x))

def through (S : StepData c f) (p : Clip) (R : PathData G)(m : ℕ)(W : Space G f→ Poly B)(A : Space G f→ℝ)(x : Dir G c)(t : ℝ)(u : Config G f) :=
   S.density (t^2)⁻¹ u (Precision.represent (t • x)) • strip p R m W A t u

def atSet (S : StepData c f)(p : Clip)(R : PathData G)(m : ℕ)(W : Space G f→Poly B)(A : Space G f→ℝ)(x : Dir G c)(t : ℝ)(U : Set (Config G f)) :=
   Poly.inject (R:=B) fun s=> ∫ v in U,(through S p R m W A x t v).part s ∂prior G f

lemma actuator (p : Clip)(R : PathData G)(m : ℕ)(W : Space G f→Poly B)(A : Space G f→ℝ)(i : S.Choices)(x : Dir G c)(t : ℝ)(u : Config G f) :
    S.noise (t^2)⁻¹ (S.prediction u i) (represent (t • x)) • strip p R m W A t u =
      (YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G) • ion i p R x A m W t u := by
  open YM.RG02.Branch in
  rw [noise_factor,mul_smul]; unfold ion; congr 1
  dsimp only [Fk.strip]
  have he : Real.exp (-((t^2)⁻¹) * noiseTaylor S (represent (t • x)) u i)* Real.exp (-(mainTerm p R u+A (t,u)+t^2*Precision.loop R u)/t^2) = Real.exp (-field i p R x A (t,u)/t^2) := by
     rw [← Real.exp_add]; unfold field; dsimp only; ring_nf
  rw [← mul_smul,he]; rfl

private lemma same_ion (p : Clip)(R : PathData G)(m : ℕ)(W : Space G f→Poly B)(A : Space G f→ℝ)(x : Dir G c)(t : ℝ)(u : Config G f) (hs : YM.RG02.Branch.Inspected S u)(a b : S.Choices) :
    ion a p R x A m W t u=ion b p R x A m W t u := by
   dsimp only [ion,field,noiseTaylor]
   rw [YM.RG02.Branch.same_prediction S hs a b]

-- disjoint stochastic and formal marker arrays. kernel is actual. Pointwise on physical torus
lemma spends (p : Clip)(R : PathData G)(m : ℕ)(W : Space G f→Poly B)(A : Space G f→ℝ)(x : Dir G c)(t : ℝ)(u : Config G f) :
    through S p R m W A x t u=(YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G) • ∑ i:S.Choices,S.likelihood u i • ion i p R x A m W t u := by
   unfold through StepData.density; rw [Finset.sum_smul,Finset.smul_sum];
   apply Finset.sum_congr rfl; intro i _; rw [mul_smul, actuator,smul_comm]

lemma on_branch (p : Clip)(R : PathData G)(m : ℕ)(W : Space G f→Poly B)(A : Space G f→ℝ)(x : Dir G c)(t : ℝ)(u : Config G f) (hs : YM.RG02.Branch.Inspected S u)(hS : S.patch.Branches S.kernel G)(i : S.Choices) :
    through S p R m W A x t u=(YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G) • ion i p R x A m W t u := by
   have he j:= same_ion p R m W A x t u hs j i
   rw [spends]; simp_rw [he, ← Finset.sum_smul,S.chosen hS u,one_smul]

-- branch read sufficient on DRAPED slice. Transport *complete* rows by root invariance.
lemma slice_branch (T : Forest S.ratio){p : Clip}{R : PathData G}{m : ℕ}{W : Space G f→Poly B}{A : Space G f→ℝ}(x : Dir G c)(t : ℝ)(u : Config G f)
    {σ v Λ}(hW : R.Bounds p σ v Λ)(h : Ink m W)(ht : Ambient A)(hS : S.patch.Branches S.kernel G)(i : S.Choices)(hs : YM.RG02.Branch.Inspected S (T.drape (wick T u))) :
    through S p R m W A x t u=(YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G) • ion i p R x A m W t u := by
   have hu (j : S.Choices) : ion j p R x A m W t u=ion i p R x A m W t u := by
      ext s; rw [← congr_fun (attends T _ (ion_volume j hW hS x ht h t s)) u,← congr_fun (attends T _ (ion_volume i hW hS x ht h t s)) u]
      exact congr_arg (fun v:Poly B=>v.part s) (same_ion p R m W A x t (T.drape _) hs j i)
   rw [spends]; simp_rw [hu, ← Finset.sum_smul,S.chosen hS u,one_smul]

section
open Draw
variable (T : Forest S.ratio) {p : Clip}{R : PathData G}{A : Space G f→ℝ}{m : ℕ}{W : Space G f→ Poly B}
    {η : ChartRatio G} {w : ℝ}{ρ : Dir G c → AxisChart G T}(i : S.Choices)(hp : 0<w)(hr:PriceGap T p R w)(h : Critical T p R ρ)
variable {σ v Λ : ℝ}(hW : R.Bounds p σ v Λ)(ht : Ink m W)(hh : Ambient A)(hs : S.patch.Branches S.kernel G)(hη : LocalRatio η)(x : Dir G c)

include ht hh hs hW
lemma activated {t : ℝ}{U : Set (T.Slice G)}(hQ:MeasurableSet U)(H : ∀ u∈U,YM.RG02.Branch.Inspected S (T.drape u)) :
    atSet S p R m W A x t (wick T ⁻¹' U)= (YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G : ℂ) • Draw.raw i p R x A m W t (wick T ⁻¹' U) := by
   ext s
   rw [Poly.part_smul]; unfold atSet Draw.raw; change ∫ v in _ , _ ∂ _= _ * ∫ v in _,_ ∂ _
   rw [← integral_const_mul]; refine integral_congr_ae ?_
   filter_upwards [ae_restrict_mem ((continuous_wick T).measurable hQ)] with k hk
   rw [slice_branch T x t k hW ht hh hs i (H _ hk)]; rfl

-- positive factor all costs. charge posterior denominator after this.
def pref (G : Gauge)(K : ℝ)(t : ℝ) := YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G * t^(dim T G) * K
omit ht hh hs hW in
lemma pref_pays (G : Gauge)(K t : ℝ)(hk : 0<K)(ht : 0<t) : 0< pref T G K t:= mul_pos (mul_pos (YM.RG02.Branch.noisePrefactor_pos ..) (pow_pos ht _)) hk

def sweep (p : Clip)(R : PathData G)(m : ℕ)(W : Space G f→Poly B)(A : Space G f→ℝ)(x : Dir G c)(K : ℝ)(t : ℝ)(U : Set (Config G f)) :=
    ((pref T G K t:ℂ)⁻¹) • atSet S p R m W A x t U

lemma identity {t : ℝ}(_he : 0<t){U : Set (T.Slice G)}(hQ:MeasurableSet U)(H : ∀ u∈U,YM.RG02.Branch.Inspected S (T.drape u))(K : ℝ)(_hk : 0<K) :
     sweep T p R m W A x K t (wick T ⁻¹' U)=(K:ℂ)⁻¹ • Draw.cut T i p R x A m W t (wick T ⁻¹' U) := by
   rw [sweep,activated T i hW ht hh hs x hQ H]; unfold pref Draw.cut
   have hn : (Complex.ofReal (YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G)) ≠ 0 := Complex.ofReal_ne_zero.mpr (YM.RG02.Branch.noisePrefactor_pos S (t^2)⁻¹ G).ne'
   simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_inv_rev,mul_smul,inv_smul_smul₀ hn]

variable {Z : Bed} (hY : Comptroller T Z p R)
include hp hr h hη hY

/-- Genuine analytic projection by holding a fixed physical unmasked window
in the exact nonlinear kernel. Charges history projection weight (known
positive) *outside*. All-order is only along *this t* declaration, no statement
of evaluating real history for any other N or scale in the projection. -/
theorem focused :
    ∃ M∈𝓝 (1:T.Slice G), MeasurableSet M ∧ (∀ u∈M,YM.RG02.Branch.Inspected S (T.drape u)) ∧
     ∀ U∈𝓝 (1:T.Slice G), MeasurableSet U→ U⊆M →
       (∀ᶠ t in Tested.germ,∀ s:B.Mode, IntegrableOn (fun u=> (through S p R m W A x t u).part s) (wick T ⁻¹' U) (prior G f)) ∧
       Aims (fun t=> sweep T p R m W A x (multiplier T i hp hr h η x) t (wick T ⁻¹' U)) (formal T i hp hr h η x A m W) := by
    have hd : T.drape (1:T.Slice G) = 1 := by
       rw [← Work.F05.exposure_zero, Work.F05.drape_exposure,link_one,lifted,replica_one]
    obtain ⟨u,ha,hb,Q⟩:= target T i hp hr h hW ht hh hs hη x hY
    let M:= (T.drape) ⁻¹' {u : Config G f|YM.RG02.Branch.Inspected S u}
    have hM:= T.continuous_drape.measurable (YM.RG02.Branch.measurable_branch S hs)
    have hmu : M∈ 𝓝 1 := ((hd ▸ T.continuous_drape.tendsto (1:T.Slice G)) : Tendsto T.drape (𝓝 1) (𝓝 (1:Config G f))) (YM.RG02.Branch.center_germ S hs)
    refine ⟨u ∩ M, inter_mem ha hmu, hb.inter hM,fun i h=>h.2,fun U ho hU he =>?_⟩
    obtain ⟨hI,Ht⟩ := Q U ho hU (he.trans inter_subset_left)
    let V:= fun t=> Draw.cut T i p R x A m W t (wick T ⁻¹' U)
    have hy u (hu:u∈U) : YM.RG02.Branch.Inspected S (T.drape u):= (he hu).2
    let K := multiplier T i hp hr h η x
    have HE:= multiplier_pos T i hp hr h η x hη
    have hz : (K:ℂ)≠0 := Complex.ofReal_ne_zero.mpr HE.ne'
    constructor
    · filter_upwards [hI] with t ht'; intro s
      apply ((ht' s).const_mul (Complex.ofReal (YM.RG02.Branch.noisePrefactor S (t^2)⁻¹ G))).congr
      filter_upwards [ae_restrict_mem ((continuous_wick T).measurable hU)] with v hv
      rw [slice_branch T x t v hW ht hh hs i (hy _ hv)]; rfl
    apply Aims.same (x:=(K:ℂ)⁻¹ • V) ?_
    · intro s; filter_upwards [Tested.eventually_pos] with t he
      rw [identity T i hW ht hh hs x he hU hy K HE]
      rfl
    convert Ht.scaler (K:ℂ)⁻¹ using 1
    exact (inv_smul_smul₀ hz _).symm
end
end YM.RG02.Fk
