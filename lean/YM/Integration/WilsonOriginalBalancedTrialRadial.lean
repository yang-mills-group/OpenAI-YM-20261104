import YM.Integration.WilsonOriginalPublicTrialInput
import YM.Integration.WilsonOriginalCompactRadialReceiver

/-! The bounded source for radial interpolation is the actual uncut, inverse-priced
canonical trial on the original quiet at its finite insertion date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalBalancedTrialRadial
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open Push Push.Local Push.AbsoluteSums Multi Push.AbsoluteSums.Animals Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations
open WilsonOriginalMicroscopicGuardedReporters WilsonOriginalMicroscopicGuardedPageSchool
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open WilsonOriginalPublicTrialInput WilsonOriginalJointTrialHearing WilsonOriginalRadialCommonGrid
open Pert.Asymptotics Overlay.Bands
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(d j:Fin 3 → ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3 → ℝ)
  (Y:∀a:Fin 3,ℕ×ℕ → R.family.label (d a))
  (before:∀a,j a ≤ K)(registered:Indexed R d j target η M Y)(N per:ℕ)
local notation "C" => R.family
local notation "H" => R.family.path
local notation "J" => Stock.census (Fin 3)
local notation "X" t:max => Config G (R.family.side t per)
local notation "W" => R.family.path.rep N per K
local notation "v₀" => fitted R d j K target η M Y before registered N per
local notation "price" => salary R d j K η M

def expense (s:(J).Mode):ℝ:=∏a∈s.val,loss R (d a) K*((price) a)

def product (o:Fin 3 → Site (R.family.side K per))(U:X K):Poly (J):=
  Poly.inject fun s=>WilsonOriginalMicroscopicGuardedTrial.face (raw R d N per K o (v₀)) s.val U

def trial (o:Fin 3 → Site (R.family.side K per))(U:X K):Poly (J):=
  ((W).eval U:ℂ) • product R d j K target η M Y before registered N per o U

theorem original (live:K<N):
    (∀a,Arrived R (d a) (j a) K N per target (before a) live.le η
      (chosen R d j K target η M Y before registered N per a) (euler R d j Y N per a) ∧
      chosen R d j K target η M Y before registered N per a ((v₀) a)=euler R d j Y N per a ∧
      ((C).labels.level (d a)).coeffSize ((v₀) a) ≤ (price) a) ∧
    ∀o:Fin 3 → Site (R.family.side K per),
    let Z:=trial R d j K target η M Y before registered N per o
    Integrable Z (prior G _) ∧ ∀(s:(J).Mode)(U:X K),
      ‖WilsonOriginalPhysicalRadialDerivative.face R (N:=N) Z s U‖ ≤ expense R d j K η M s:=by
  have contracts:=WilsonOriginalPublicTrialInput.original R d j K target η M Y before registered N per live
  have sale:=registered K before N per live.le (fun a=>(before a).trans_lt live)
  refine ⟨fun a=>⟨?_,(contracts.1 a)⟩,?_⟩
  · simpa only [chosen,dif_pos live] using sale.choose_spec.1 a (euler R d j Y N per a)
  intro o Z
  let f:=product R d j K target η M Y before registered N per o
  have smooth:Continuous f:=by
    rw [show f=fun U:X K=>∑s:(J).Mode,Poly.send s ((f U).part s) from funext fun U=>(Poly.studs _).symm]
    refine continuous_finsetSum _ fun s _=>(sends s).comp ?_
    change Continuous (fun U:X K=>∏a∈s.val,raw R d N per K o (v₀) a U)
    apply continuous_finsetProd
    intro a _
    exact continuous_const.add (((C).localSection (d a)).continuous_places _ _)
  have envelope:Envelope (W).eval:=(W).envelope (R.makes.wilson.represents N per K live.le).good
  obtain ⟨B,hold⟩:=envelope.cost
  obtain ⟨B',hold'⟩:=isCompact_univ.exists_bound_of_continuousOn smooth.continuousOn
  constructor
  · apply Integrable.of_bound ((Complex.continuous_ofReal.measurable.comp envelope.meas).smul smooth.measurable).aestronglyMeasurable (B*B')
    refine ae_of_all _ fun U=>?_
    change ‖((W).eval U:ℂ) • f U‖ ≤ B*B'
    rw [norm_smul,Complex.norm_real]
    exact mul_le_mul (hold U) (hold' U (Set.mem_univ _)) (norm_nonneg _) ((norm_nonneg _).trans (hold U))
  · intro s U
    have positive:0<(W).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson live.le U
    change ‖(((W).eval U:ℂ)⁻¹)*(((W).eval U:ℂ)*(∏a∈s.val,raw R d N per K o (v₀) a U))‖ ≤ _
    rw [←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_mul,norm_prod]
    apply prod_le_prod (fun a _=>norm_nonneg _)
    intro a _
    exact (((unary R d N per K o (v₀) a).2.2 U).2.trans (one R d N per K live.le (v₀) a)).trans
      (mul_le_mul_of_nonneg_left (contracts.1 a).2 (nonneg R _ K))

theorem radial (simple:G.Simple)(radial accuracy:ℕ):
    ∀ᶠ i:ℕ in atTop,∀(d j:Fin 3 → ℕ)(K target₀:ℕ)(η:ℝ)(M:Fin 3 → ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ → (C).label (d a))(before:∀a,j a ≤ K)(registered:Indexed R d j target₀ η M Y)
    {N per:ℕ}(_live:K<N)(past:i<K)(o:Fin 3 → Site ((C).side K per))(s:(J).Mode),
    let Z:=trial R d j K target₀ η M Y before registered N per o
    let A:=expense R d j K η M s
    ∀depth,radial ≤ depth → 1 ≤ ((H).levels.budget i).supportExponent →
    ∀der ≤ radial,∀a∈Push.Local.tests ((C).labels.level radial),
    ∀(values:ℕ → ℂ)(E:ℝ),(∀l ≤ depth,‖read R N per
      (WilsonCapturedPrimaryWeakTrialRadial.field R radial N per i (WilsonOriginalRadialCommonGrid.target radial accuracy) depth a l)
      past.le Z s-values l‖ ≤ E) →
    let g:=regulatorRun (C) N per (i+1)
    let B:=(H).levels.budget i
    let r:=WilsonOriginalPhysicalRadialDerivative.radiusAt R (N:=N) (per:=per) (i:=i) radial (WilsonOriginalRadialCommonGrid.target radial accuracy)
    let t:=g^(WilsonCapturedPrimaryPaid.gap (WilsonOriginalRadialCommonGrid.target radial accuracy) 1)*ratio der depth
    let f:ℝ → ℂ:=fun x=>read R N per (WilsonCapturedPrimaryRays.field (C).params B 0 r a x) past.le Z s
    ‖iteratedDeriv der f 0-WilsonOriginalRadialFiniteDifference.divided der t values‖ ≤
      WilsonCapturedPrimarySamples.price der*(E/t^der+WilsonOriginalRadialSpringTariff.factor (H) (C).params a (der+1)*A*g^accuracy):=by
  filter_upwards [WilsonOriginalRadialCommonGrid.original R simple radial accuracy ((C).labels.level radial)] with i paid
  intro d j K T η M Y before entered N per live past o s Z A depth enough wide der kd a ha values E nodes
  obtain ⟨intg,cap⟩:=(original R d j K T η M Y before entered N per live).2 o
  exact paid der kd a ha live.le past enough wide Z intg s A ((norm_nonneg _).trans (cap s 1)) (cap s) values E nodes

end YM.Integration.WilsonOriginalBalancedTrialRadial
