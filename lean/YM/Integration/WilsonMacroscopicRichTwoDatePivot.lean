import YM.Integration.WilsonMatrixTicketLanesSmearedPair
import YM.Integration.WilsonPhysicalExteriorFrame
import YM.Integration.WilsonMacroscopicRichMovingDetector

/-! The independently issued smooth two-site profiles recover the original running field at a second, closer scale. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichTwoDatePivot
open Filter Function Set Matrix Lattice Wilson RG Source Extraction Table Spec RG17 Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMatrixTicketLanesSmearedPivot
open private cost clm_bound from YM.Integration.WilsonOrdinaryMixedDetectors
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}

def active (r:ℝ)(h:ℕ):RG17.Free R.family h ≃ₗ[ℂ] RG17.Free R.family h:=(homogeneous F J Z r h).trans (J r h).symm

theorem field (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)(h:ℕ)(v:RG17.Free R.family h):
    Tendsto (fun r=>active F J Z r h v) trail (𝓝 v):=by
  have p:=WilsonPositionHomogeneousLeading.field F J Z lead owed simple h v
  apply p.congr
  intro r
  change WilsonPositionPrescribedFrame.change F J Z.store h r (change F J Z h r v)=(J r h).symm (J r h _)
  simp only [LinearEquiv.symm_apply_apply];rfl

theorem bounded (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)(h:ℕ):
    ∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀v:RG17.Free R.family h,‖active F J Z r h v‖≤A*‖v‖:=by
  let e:=Module.finBasis ℝ (RG17.Free R.family h)
  let T:=1+∑i,‖e i‖
  have np:0≤∑i,‖e i‖:=Finset.sum_nonneg (fun i _=>norm_nonneg _)
  have tp:0≤T:=by dsimp [T];linarith only [np]
  have cp:0≤cost e:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have all:∀ᶠr in trail,∀i,‖active F J Z r h (e i)‖≤T:=eventually_all.mpr fun i=>by
    have bound:‖e i‖<T:=by
      have one:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>norm_nonneg (e j)) (Finset.mem_univ i)
      dsimp [T];linarith only [one]
    filter_upwards [(field F J Z lead owed simple h (e i)).norm.eventually (gt_mem_nhds bound)] with r hr using hr.le
  refine ⟨cost e*T,mul_nonneg cp tp,?_⟩
  filter_upwards [all] with r hr v
  let H:=((active F J Z r h).toLinearMap.toContinuousLinearMap).restrictScalars ℝ
  exact (H.le_opNorm v).trans (mul_le_mul_of_nonneg_right (clm_bound e H tp hr) (norm_nonneg _))

/-- The physical field itself, the smaller radius, and the direction on that field are all chosen
      after the profiles. At a coupling-separated date the loss is only a fixed power of that coupling. -/
theorem original (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)(h:ℕ):
    ∃B:Profiles R h, (∀j:B.probes.index,∃w:(standard R.family.book.grid).Ref h,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h w) ∧
      ∀ε:ℝ,0<ε→∃C:ℝ,0≤C ∧ ∀ᶠ τ in trail,∀t∈Ioc (0:ℝ) 1,∀y:S.Field h,
        ‖(J (t*τ) h).symm y‖≤C*t^(-(h:ℝ)-ε)*‖row F J Z B τ y‖:=by
  obtain ⟨B,issued,K,kp,buy⟩:=WilsonMatrixTicketLanesSmearedPair.fixed F J Z lead owed simple h
  obtain ⟨H,hp,cost⟩:=bounded F J Z lead owed simple h
  refine ⟨B,issued,?_⟩
  intro ε ep
  obtain ⟨A,ap,move⟩:=WilsonPhysicalExteriorFrame.between F h J lead ε ep
  have pos:0≤A:=zero_le_one.trans ap
  refine ⟨A*H*K,mul_nonneg (mul_nonneg pos hp) kp.le,?_⟩
  filter_upwards [buy,cost,move] with τ fit honest lift t ht y
  let u:=(homogeneous F J Z τ h).symm y
  have same:active F J Z τ h u=(J τ h).symm y:=by simp only [u,active,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  have cap:‖(J τ h).symm y‖≤H*(K*‖row F J Z B τ y‖):=(same ▸ honest u).trans (mul_le_mul_of_nonneg_left (fit y) hp)
  exact (lift t ht y).trans ((mul_le_mul_of_nonneg_left cap (mul_nonneg pos (Real.rpow_nonneg ht.1.le _))).trans_eq (by ring))
end YM.Integration.WilsonMacroscopicRichTwoDatePivot
