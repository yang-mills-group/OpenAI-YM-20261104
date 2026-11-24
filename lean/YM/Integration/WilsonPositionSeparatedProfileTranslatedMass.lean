import YM.RG05Readout.Harvest.Prices
import YM.Integration.ActualScalarTransport

/-! An entire translated degree-zero census has its original finite Wilson mean.
The coarse field is integrated with the actual density of the same history. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileTranslatedMass
open Function Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open OPE.Therm RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Harvest
open MergeProof Accent RG05Readout.Records
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) (hC : C.Makes) (N p : ℕ)

private theorem branch (k : ℕ) (F : Bin G (C.side (k+1) p)) (light : BLight F)
    {A : ℂ} (mass : ∀f : Body, (∫U,F f U ∂prior G _)=A) (g : Body) :
    (∫V,journey C p k N 0 F g V ∂prior G _)=A := by
  let H := Bud C p k
  let Z (i : H) := sailS C k p F g i
  let T := C.path.levels.clock.op k p
  let b := C.path.β N p (k+1)
  let J (i : H) := T.push b (Z i)
  have funds (i : H) : Integrable (Z i) (prior G _) := sail_lit F light g i
  have lives (i : H) : Integrable (J i) (prior G _) :=
    StepData.push_integrable (C.path.levels.transition_mass ..) _ (funds i)
  have filed (i : H) : (∫U,J i U ∂prior G _)=A := by
    rw [show (∫U,J i U ∂prior G _)=(∫U,Z i U ∂prior G _) from
      StepData.push_integral (C.path.levels.transition_mass ..) _ (funds i)]
    exact ((prior_pull (G:=G) (1:Signed) (child C p k i)).integral_comp
      (WardBin.Wheels.embedding_pull _ _) (F (Many.headFee C p k i g))).trans (mass _)
  unfold journey Address.average blast
  simp only [pow_zero,one_smul,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  change (∫V,(Fintype.card H:ℂ)⁻¹*(∑i : H,J i V) ∂prior G _)=A
  rw [integral_const_mul,integral_finsetSum _ (fun i _=>lives i)]
  simp_rw [filed]
  have nz : (Fintype.card H : ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀ nz,one_mul]

include hC in
theorem census {n u : ℕ} (top : n+1≤N) (span : u≤n)
    (X : C(Config G (C.side N p),ℂ)) (g : Body) :
    (∫V,pulls C p N n 0 top (fun _=>X) u span g V ∂prior G _)=
      ∫U,((C.path.rep N p N).eval U:ℂ)*X U ∂prior G _ := by
  let F : Bin G (C.side N p) := fun _=>X
  let A := ∫U,((C.path.rep N p N).eval U:ℂ)*X U ∂prior G _
  have timer : timely F := fun _=>X.continuous
  have UV (f : Body) : (∫V,arises C p N n top F f V ∂prior G _)=A :=
    gust_sum C.path N p N _ (dye_grow hC X.continuous) top
  have money : BLight (arises C p N n top F) := fun f=>dye_bold hC _ top (timer f)
  change (∫V,pulls C p N n 0 top F u span g V ∂prior G _)=A
  induction span using Nat.decreasingInduction generalizing g with
  | self =>
    rw [wakes top F]
    exact branch C N p n (arises C p N n top F) money UV g
  | of_succ k hk ih =>
    rw [down top F hk]
    exact branch C N p k _ (beacons hC top F hk timer) ih g

include hC in
theorem original {n u : ℕ} (top : n+1≤N) (span : u≤n)
    (X : C(Config G (C.side N p),ℂ)) (g : Body) :
    (∫V,pulls C p N n 0 top (fun _=>X) u span g V/((C.path.rep N p u).eval V:ℂ)
      ∂scene C.path N p u)=moment (C.beta N p) X := by
  have above : u≤N := span.trans ((Nat.le_succ _).trans top)
  have base : scene C.path N p N=law G (C.side N p) (C.beta N p) := by
    unfold scene law dose weight
    rw [(hC.wilson.starts N p).2]
  change _=(∫U,X U ∂law G (C.side N p) (C.beta N p))
  rw [←base,actualScene_formula C hC above,actualScene_formula C hC (j:=N) le_rfl]
  apply congrArg (_ • ·)
  have paid (V : Config G (C.side u p)) :
      (C.path.rep N p u).eval V •
        (pulls C p N n 0 top (fun _=>X) u span g V/((C.path.rep N p u).eval V:ℂ))=
      pulls C p N n 0 top (fun _=>X) u span g V := by
    rw [Complex.real_smul,←mul_div_assoc,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr
      (Multi.AxisShift.chosen_positive hC.wilson above V).ne')]
  simp_rw [paid,Complex.real_smul]
  exact census C hC N p top span X g

end YM.Integration.WilsonPositionSeparatedProfileTranslatedMass
