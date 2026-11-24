import YM.Integration.WilsonOriginalSeparatedRegular
import YM.Integration.WilsonOriginalBetweenFiledPrints
import YM.Integration.WilsonOriginalOrdinaryFlatHulls

/-! The regular ordinary face of the actual issued successor, including the old
register, compared with a second, independently filed unmasked compact print. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterSeparatedRegular
open Finset Filter MeasureTheory Lattice Wilson RG Ac Marker QuadraticLocal Multi
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums
open Push.AbsoluteSums.Animals OPE.Therm WilsonRootedKioskOccupiedSlip
open WilsonOriginalOrdinaryFlatHulls WilsonOriginalSeparatedMask
open private YM.Integration.WilsonOriginalOrdinaryFlatHulls.gross from YM.Integration.WilsonOriginalOrdinaryFlatHulls
open Comparison.Density.Transport
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{p p':BudgetPoint}{V X X' ι μ ι':Type}
    [Fintype V][DecidableEq V]{J:Census V}{o o':V→Site n}

open WilsonOriginalSeparatedRegular

omit [Fintype V] in
private theorem local_clear (k:ℕ)(s:J.Mode)(U:Config G n)(v:V)(hv:v∈s.val){b:ℕ}
    (hb:b ≤ max p.B (reach p.B k))
    (h:∀y∈roots p k o s,Healthy p.threshold (halo p.B {y}) U):Healthy p.threshold (halo b {o v}) U:=by
  apply Finset.disjoint_left.mpr
  intro y hy bad
  obtain ⟨x,hx,e⟩:=halo_spec.mp hy
  have eq:x=o v:=by simpa only [mem_singleton] using hx
  have inside:y∈roots p k o s:=halo_spec.mpr ⟨x,eq ▸ mem_image_of_mem o hv,e.trans hb⟩
  have self:y∈halo p.B {y}:=halo_spec.mpr ⟨y,by simp,by simp⟩
  exact Finset.disjoint_left.mp (h y inside) self bad

theorem original [Countable ι][Countable μ][Countable ι']
    (L:Lamps X ι G p o J)(old:Lamps X μ G p o J)(next:Lamps X' ι' G p' o' J)
    (w w':V→ℝ)(hw:∀a,0<w a)(hw':∀a,0<w' a){a a' E C rent C' W W' M δ:ℝ}
    (width:0≤a)(width':0≤a')(paid:L.Paid w p.B a E)(refund:old.Paid w p.B a rent)
    (stock:Gross L w p.B a C)(other:Gross next w' p'.B a' C')
    (ep:0≤E)(cp:0≤C)(rp:0≤rent)(np:0≤C')(wp:0≤W)(mp:0≤M)(dp:0≤δ)
    (x:X)(z:X')(s:J.Mode)(k:ℕ)
    (source:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w t.val)⁻¹≤W)
    (target:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w' t.val)⁻¹≤W')
    (amount:W*(E+rent)≤M ∧ W'*C'≤M)(front:Hot J→V)(mem:∀t,front t∈t.val.val)
    (shared:∀U,(∀v∈s.val,Healthy p.threshold (halo p.B {o v}) U)→
      ∀t:Hot J,t.val.val⊆s.val→‖(bare L x U).part t.val-(bare next z U).part t.val‖ ≤ δ):
    Measurable (defect L old next x z s) ∧
    (∀U,‖defect L old next x z s U‖≤2*cost s M) ∧
    ∀U,(∀y∈roots p k o s,Healthy p.threshold (halo p.B {y}) U)→
      ‖defect L old next x z s U‖≤change s M (W*rent+W*((Real.exp (a*k))⁻¹*C)+δ):=by
  have both:=Lamps.joinPaid paid refund
  have quiet (U:Config G n):((L.join old).log x U).part J.quiet=0 ∧ (bare next z U).part J.quiet=0:=
    ⟨(L.join old).quiet_of_hasSum x U (both.sums width hw x U),WilsonRootedKioskCompleteFiling.quiet next hw' width' other z U⟩
  have after (U:Config G n)(t:Hot J)(ht:t.val.val⊆s.val):‖(bare next z U).part t.val‖≤M:=by
    have h:=WilsonReceivedWholeFieldMask.whole next hw' width' other z U t.val (front t) (mem t)
    exact ((le_inv_mul_iff₀ (Poly.worth hw' t.val)).mpr h).trans
      ((mul_le_mul_of_nonneg_right (target t ht) np).trans amount.2)
  refine ⟨(WilsonOriginalBetweenFiledPrints.ordinary (L.join old) w hw width both x s).sub
    (WilsonReceivedWholeFieldHot.borel next hw' width' other z s),?_,?_⟩
  · intro U
    apply YM.Integration.WilsonOriginalOrdinaryFlatHulls.gross s _ _ (quiet U) mp
    intro t ht
    have h:=WilsonCenteredRegularHit.component (L.join old) w hw width both x U t.val (front t) (mem t)
    exact ⟨h.trans ((mul_le_mul_of_nonneg_right (source t ht) (add_nonneg ep rp)).trans amount.1),after U t ht⟩
  · intro U healthy
    apply WilsonOriginalOrdinaryFlatHulls.ordinary s _ _ (quiet U) mp (by positivity)
    intro t ht
    have clear₁:=local_clear k s U (front t) (ht (mem t)) (le_max_right p.B (reach p.B k)) healthy
    have mask:=WilsonOriginalSeparatedMask.original L hw width stock k x U t.val (front t) (mem t) clear₁
    have mask':‖(L.log x U).part t.val-(bare L x U).part t.val‖≤W*((Real.exp (a*k))⁻¹*C):=by
      have h:‖(L.log x U).part t.val-(bare L x U).part t.val‖≤
          (Real.exp (a*k)*Poly.toll w t.val)⁻¹*C:=(le_inv_mul_iff₀
            (mul_pos (Real.exp_pos _) (Poly.worth hw _))).mpr mask
      rw [mul_inv_rev,mul_assoc] at h
      exact h.trans (mul_le_mul_of_nonneg_right (source t ht) (mul_nonneg (inv_nonneg.mpr (Real.exp_nonneg _)) cp))
    have small:‖(bare L x U).part t.val-(bare next z U).part t.val‖≤δ:=
      shared U (fun v inside=>local_clear k s U v inside (le_max_left p.B (reach p.B k)) healthy) t ht
    have debt:‖(old.log x U).part t.val‖≤W*rent:=
      (WilsonCenteredRegularHit.component old w hw width refund x U t.val (front t) (mem t)).trans
        (mul_le_mul_of_nonneg_right (source t ht) rp)
    refine ⟨after U t ht,?_⟩
    have join:((L.join old).log x U).part t.val=(L.log x U).part t.val+(old.log x U).part t.val:=
      congrArg (fun a:Poly J=>a.part t.val) (Lamps.joinLog x U (paid.sums width hw x U) (refund.sums width hw x U))
    rw [join,show (L.log x U).part t.val+(old.log x U).part t.val-(bare next z U).part t.val=
      (old.log x U).part t.val+((L.log x U).part t.val-(bare L x U).part t.val)+
        ((bare L x U).part t.val-(bare next z U).part t.val) by abel]
    exact (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add debt mask')) small)

end YM.Integration.WilsonOriginalFullRosterSeparatedRegular
end
