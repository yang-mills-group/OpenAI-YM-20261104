import YM.Integration.WilsonAddressedFiniteThermalInput
import YM.Integration.WilsonAddressedFiniteGuardCapital
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteThermalWallet
open Finset Lattice Wilson RG Source Labels Marker QuadraticLocal.Affinity MergeProof.Accent
open PhysicalNext.Repeat.Legato Pert.Asymptotics RG16 RG16.Literal
open WilsonOriginalMicroscopicEntranceOpticalUnits (rank)
open WilsonAddressedFiniteGuardTrial (submitted)
open WilsonAddressedFiniteThermalInput (vector)
open WilsonOriginalPublicTrialFigure (weight amount)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I](d:I → ℕ)
  (N per K:ℕ)(live:K ≤ N)(v:∀i:I,R.family.label (d i))(z:I → ℂ)
  (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=I)))(s:(Stock.census I).Mode)
local notation "g" => regulatorRun R.family N per K
local notation "θ" => (R.family.path.rep N per K).p.threshold
local notation "H" => R.family.path.levels.clock.hatBeta K
local notation "F" a:max => R.family.labels.level (d a)
local notation "D" => (fun j:↥s.val=>d j.val)
local notation "entries" => vector R d N per K v z x s

include live in
theorem coefficient (i:↥s.val)(l:(F i.val).Index):
    amount R D g entries i l = (((θ⁻¹)^(((F i.val).grades l).2):ℝ):ℂ)*submitted R d v z x i.val l:=by
  let h:=((F i.val).grades l).2
  have gp:g≠0:=(ActualRunKernelPackets.regulator_pos R N per K live).ne'
  have tp:θ≠0:=(R.family.path.rep N per K).p.threshold_pos.ne'
  have cancel:(g/θ)^h*(g^h)⁻¹=(θ⁻¹)^h:=by rw [div_pow,inv_pow]; field_simp
  have scalar:(((g/θ)^h:ℝ):ℂ)*(((g^h)⁻¹:ℝ):ℂ)=(((θ⁻¹)^h:ℝ):ℂ):=by exact_mod_cast cancel
  change ((((g/θ)^h:ℝ):ℂ)*_)*(((g^h)⁻¹:ℝ):ℂ)=(((θ⁻¹)^h:ℝ):ℂ)*_
  calc _=((((g/θ)^h:ℝ):ℂ)*(((g^h)⁻¹:ℝ):ℂ))*submitted R d v z x i.val l:=by ring
       _=_:=by rw [scalar]

include live in
theorem mass (i:↥s.val):
    (∑l,‖amount R D g entries i l‖) ≤ H^(rank R (d i.val))*(F i.val).coeffSize (z i.val • v i.val):=by
  let u:=submitted R d v z x i.val
  have budget:θ⁻¹ ≤ H:=by
    have fixed : (R.family.path.rep N per K).p=R.family.path.levels.budget K := (R.makes.wilson.represents N per K live).vac
    rw [fixed,←min_eq_left ((R.family.path.levels.budget K).threshold_le)]
    exact WilsonOriginalCoordinateExposure.threshold R K
  have hp:1 ≤ H:=(R.family.path.levels.fits.delayed K).le
  have tp:0 ≤ θ⁻¹:=inv_nonneg.mpr (R.family.path.rep N per K).p.threshold_pos.le
  have phase:(F i.val).coeffSize u  ≤  (F i.val).coeffSize (z i.val • v i.val):=by
    have n:(F i.val).coeffSize u=‖(x i.val).val‖*(F i.val).coeffSize (z i.val • v i.val):=by
      dsimp only [u,submitted]
      rw [mul_smul]
      simp only [Frame.coeffSize,Pi.smul_apply,smul_eq_mul,norm_mul,Finset.mul_sum]
    rw [n]
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun _ _=>norm_nonneg _) (x i.val).property
  calc
    _ ≤ H^(rank R (d i.val))*(F i.val).coeffSize u:=by
      change _  ≤  _*∑l,‖u l‖
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l hl
      rw [coefficient R d N per K live v z x s i l,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg tp _)]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (pow_le_pow_left₀ tp budget _).trans (pow_le_pow_right₀ hp (Finset.le_sup (f:=fun l=>((F i.val).grades l).2) hl))
    _ ≤ _:=mul_le_mul_of_nonneg_left phase (pow_nonneg (zero_le_one.trans hp) _)

include live in
/-- Absolute weight of the full occupied public basis expansion before either
    regulator, for any paid optical input, including every proper subroster. -/
theorem original {B:ℝ}(e:ℕ)(income:∀a,(F a).coeffSize (z a • v a) ≤ B*H^e):
    (∑b, ‖weight R D g entries b‖) ≤ ∏i∈s.val,B*H^(rank R (d i)+e):=by
  have hp:0 ≤ H:=zero_le_one.trans (R.family.path.levels.fits.delayed K).le
  simp only [WilsonOriginalPublicTrialFigure.weight,norm_prod]
  rw [←Fintype.prod_sum (fun (i:↥s.val)(b:(F i.val).Index)=>‖amount R D g entries i b‖),
    ←Finset.prod_coe_sort s.val (fun i=>B*H^(rank R (d i)+e))]
  apply Finset.prod_le_prod (fun i _=>Finset.sum_nonneg fun _ _=>norm_nonneg _)
  intro i _
  refine (mass R d N per K live v z x s i).trans ?_
  calc _ ≤ H^(rank R (d i.val))*(B*H^e):=mul_le_mul_of_nonneg_left (income i.val) (pow_nonneg hp _)
       _=_:=by rw [pow_add];ring

end YM.Integration.WilsonAddressedFiniteThermalWallet
end
