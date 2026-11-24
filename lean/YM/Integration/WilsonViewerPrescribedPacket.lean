import YM.Integration.WilsonViewerPublicField
import YM.Integration.WilsonPositionHomogeneousLeading
import YM.Integration.WilsonMacroscopicSharpPacket

/-! Send the one complete OPE coefficient to each genuine viewer at fixed
macroscopic clearance. The spatial truncation and the error of a finite
perturbative coefficient have their own prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonViewerPrescribedPacket
open Function Filter Set Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Climb RG17 PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)(simple:G.Simple)(lead:Leading F J)
  {Y:(Bel R.family.book).Hierarchy}(prepared:∀ d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
local notation "P" => homogeneous F J Z

include Q lead simple prepared in
theorem bounded (h:ℕ):∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀v:RG17.Free R.family h,‖P r h v‖≤A*‖v‖:=by
  obtain ⟨D,Dn,base⟩:=WilsonViewerPublicField.bounded F Q J lead simple h
  let B:=Module.finBasis ℂ (RG17.Free R.family h)
  let L i:=D*(‖B i‖+1)
  have pos i:0≤L i:=mul_nonneg Dn (by positivity)
  have basisPay i:∀ᶠr in trail, ‖P r h (B i)‖≤L i:=by
    have converges:=WilsonPositionHomogeneousLeading.field F J Z lead prepared simple h (B i)
    filter_upwards [base,converges.norm.eventually (ge_mem_nhds (lt_add_one _))] with r paid close
    exact (paid _).trans (mul_le_mul_of_nonneg_left close Dn)
  refine ⟨∑i,‖(B.coord i).toContinuousLinearMap‖*L i,Finset.sum_nonneg (fun i _=>
    mul_nonneg (B.coord i).toContinuousLinearMap.opNorm_nonneg (pos i)),?_⟩
  filter_upwards [eventually_all.mpr basisPay] with r held v
  rw [Finset.sum_mul]
  nth_rw 1 [←B.sum_repr v]
  rw [map_sum]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
  rw [map_smul,norm_smul,mul_right_comm]
  exact mul_le_mul ((B.coord i).toContinuousLinearMap.le_opNorm v) (held i) (norm_nonneg _)
    (mul_nonneg (B.coord i).toContinuousLinearMap.opNorm_nonneg (norm_nonneg _))

private theorem apart {E:Type}[Fintype E]{o:E4}{y:E→E4}{δ:ℝ}(dp:0<δ)(h:ClearOf o y δ):
    Injective (beside (sole o) y):=by
  refine beside_distinct.mpr ⟨injective_of_subsingleton _,?_,?_⟩
  · intro j k eq;by_contra ne;have cost:=h.spread j k ne
    rw [eq,sub_self,norm_zero] at cost;exact (not_le_of_gt dp) cost
  · intro _ j eq;have cost:=h.openSpace j
    change o=y j at eq
    rw [eq,sub_self,norm_zero] at cost;exact (not_le_of_gt dp) cost

variable {E:Type}[Fintype E]{e:E→ℕ}(w:Labels S e){δ:ℝ}(dp:0<δ)
include Q lead simple prepared dp in
theorem discrepancy (services:Services R.family f S)(h:ℕ):
    ∃D:ℝ,0≤D ∧ ∀ᶠr in trail,∀(o:E4)(y:E→E4),ClearOf o y δ→
      ∀(q:Viewers F)(v:S.Field h)(c:RG17.Free R.family h),
      ‖upon (spectator F q) h o y w v-upon (spectator F q) h o y w (P r h c)‖ ≤
        D*‖(P r h).symm v-c‖:=by
  obtain ⟨A,An,field⟩:=bounded F Q J Z simple lead prepared h
  obtain ⟨D,Dn,exterior⟩:=WilsonMacroscopicViewerCharge.uniform F services h w dp
  refine ⟨D*A,mul_nonneg Dn An,?_⟩
  filter_upwards [field] with r paid o y clear q v c
  have preserved:P r h ((P r h).symm v-c)=v-P r h c:=by rw [map_sub,LinearEquiv.apply_symm_apply]
  rw [←map_sub,←preserved,mul_assoc]
  exact (exterior o y clear (apart dp clear) q _).trans (mul_le_mul_of_nonneg_left (paid _) Dn)

include lead prepared dp simple in
theorem sharp (fac:Facilities R.family f S)(foundation:Foundation F Q){u:Filter (ℕ×ℕ)}
    [u.NeBot](under:u≤f.fuse)(ticket:MatrixTicket (C:=R.family) S F.sector.derivatives u)
    {I:Type}[Fintype I]{d:I→ℕ}(v:Labels S d)(h:ℕ){M η:ℝ}(Mn:0≤M)(ep:0<η):
    ∃(k:ℕ)(A D:ℝ), 0<A ∧ 0≤D ∧ ∀ᶠr in trail,∀(x:I→E4)(o:E4)(y:E→E4),
      WithinRoom r M η x o→ ClearOf o y δ→∀(q:Viewers F)(c:RG17.Free R.family h),
      ‖whole (spectator F q) x v y w-upon (spectator F q) h o y w (P r h c)‖ ≤
        A*badge r^k*r^((h:ℝ)+1-weight d)+D*‖(P r h).symm (Q.packet h x v o)-c‖:=by
  obtain ⟨k,A,Ap,exactMaster⟩:=WilsonMacroscopicSharpPacket.on_ticket F Q fac foundation under ticket h v w Mn ep dp
  obtain ⟨D,Dn,delta⟩:=discrepancy F Q J Z simple lead prepared w dp fac.toServices h
  refine ⟨k,A,D,Ap,Dn,?_⟩
  filter_upwards [exactMaster,delta] with r full cost x o y fits clear q c
  exact (norm_sub_le_norm_sub_add_norm_sub _ (upon (spectator F q) h o y w (Q.packet h x v o)) _).trans
    (add_le_add ((full x o y fits clear).2 q) (cost o y clear q _ c))

end YM.Integration.WilsonViewerPrescribedPacket
end
