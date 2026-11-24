import YM.Integration.WilsonOriginalBalancedTrialRadial
import YM.Integration.WilsonCapturedPrimaryWeakTrialNonconstant

/-! The inverse, guarded density, finite decoder and uncut radial salary on the
same appointed reporter. The inverse acts on the full space, including its unit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalBalancedTrialCoordinates
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open Push Push.Local Push.AbsoluteSums Multi Push.AbsoluteSums.Animals Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations
open Pert.Asymptotics Stationary ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalMicroscopicGuardedReporters WilsonOriginalMicroscopicGuardedPageSchool
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet WilsonOriginalPublicTrialInput
open WilsonCapturedPrimaryAperture WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar
open OPE.Therm Extra.Multi Comparison.RG02 RG16 RG16.Literal WilsonCapturedPrimaryPotential WilsonCapturedPrimaryPaid WilsonFirstReceivedRadialStencil WilsonPositionProgramBlockedTrialNodes Next.Rank
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(d j:Fin 3 → ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3 → ℝ)
  (Y:∀a:Fin 3,ℕ×ℕ → R.family.label (d a))
  (before:∀a,j a ≤ K)(registered:Indexed R d j target η M Y)(N per:ℕ)
local notation "C" => R.family
local notation "H" => R.family.path
local notation "F" d:max => R.family.labels.level d
local notation "X" t:max => Config G (R.family.side t per)
local notation "A" => chosen R d j K target η M Y before registered N per

theorem clock (h K:ℕ):
    loss R h K ≤ (1+BasisCost.price ((C).localSection h))*((H).levels.clock.hatBeta K)^(BasisCost.slots (F h)):=by
  let x:ℝ:=(H).levels.clock.hatBeta K
  have hp:1 ≤ x:=((H).levels.fits.delayed K).le
  have pos:=zero_lt_one.trans_le hp
  have inv:((H).levels.budget K).threshold⁻¹ ≤ x:=by
    change ((Real.sqrt x)⁻¹*Real.exp ((Real.log (Real.log x))^2))⁻¹ ≤ x
    have fuel:=Real.one_le_exp (sq_nonneg (Real.log (Real.log x)))
    have root:=Real.sqrt_pos.mpr pos
    calc
      _ ≤ ((Real.sqrt x)⁻¹)⁻¹:=inv_anti₀ (inv_pos.mpr root) (le_mul_of_one_le_right (inv_nonneg.mpr root.le) fuel)
      _ = _:=inv_inv _
      _ ≤ x:=(Real.sqrt_le_left pos.le).mpr (by nlinarith only [mul_nonneg pos.le (sub_nonneg.mpr hp)])
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) (max_le hp inv) _)
    (by have bp:0 ≤ BasisCost.price ((C).localSection h):=zero_le_one.trans (BasisCost.price_pos _); positivity)

theorem original (live:K<N)(a:Fin 3)(e:(C).label (d a)):
    let i:=j a
    let W:=(H).rep N per i
    let v:=((A) a).symm e
    let τ:=stretch R η i K*(F (d a)).coeffSize e
    let at₀:i+(K-i) ≤ N:=by have seen:=before a;omega
    (A) a v=e ∧ (F (d a)).coeffSize v ≤ τ ∧
    (∀(z:Site ((C).side K per))(U:X K),‖WilsonPositionProgramBlockedTrialAddBack.uncut R (d a) N per K z v U‖ ≤
      (1+BasisCost.price ((C).localSection (d a)))*((H).levels.clock.hatBeta K)^BasisCost.slots (F (d a))*τ) ∧
    ∃q:Coefficient (F (d a)) ((C).side i per),q.Format 0 (C).params W ∧
      q.remBound 0 W (safety (C) i) (2*stock (C) i*(F (d a)).coeffSize e) ∧
      q.density 0 ((C).localSection (d a)) W=WilsonPositionProgramOriginalBlockedTrial.carried R (d a) (b:=i) (n:=K-i) (p:=per) at₀ 0 v ∧
      projection (F (d a)) (C).params W.p.threshold 0 q=e ∧
      ∀depth,d a ≤ depth →
      let obs:=reading ((C).localSection (d a)) W 0 q
      let err:=gMap (C) N per (d a) i (e-WilsonCapturedPrimaryWeakTrialRadial.decode R (d a) N per i target depth obs)
      (F (d a)).coeffSize err ≤ WilsonCapturedPrimaryWeakTrialRadial.price R (d a) N per i target depth e 0 ∧
        ∀l,‖err l‖ ≤ WilsonCapturedPrimaryWeakTrialRadial.price R (d a) N per i target depth e 0:=by
  intro i W v τ at₀
  have sale:=registered K before N per live.le (fun l=>(before l).trans_lt live)
  have earn:Arrived R (d a) i K N per target (before a) live.le η ((A) a) e:=by
    simpa only [chosen,dif_pos live] using sale.choose_spec.1 a e
  obtain ⟨size,q,form,remainder,carry,primary,nodes⟩:=earn
  refine ⟨((A) a).apply_symm_apply e,size,?_,q,form,remainder,carry,primary,?_⟩
  · intro z U
    let h:Fin 3→ℕ:=fun _=>d a
    let o:Fin 3→Site ((C).side K per):=fun _=>z
    let w:(l:Fin 3)→(C).label (h l):=fun _=>v
    have bound:=(((unary R h N per K o w 0).2.2 U).2.trans (one R h N per K live.le w 0)).trans
      (mul_le_mul_of_nonneg_left size (nonneg R (d a) K))
    exact bound.trans (mul_le_mul_of_nonneg_right (clock R (d a) K) ((BasisCost.coeff_nonneg v).trans size))
  · intro depth enough
    exact WilsonCapturedPrimaryWeakTrialRadial.original R (d a) N per i target depth ((before a).trans_lt live) enough q e nodes

end YM.Integration.WilsonOriginalBalancedTrialCoordinates
