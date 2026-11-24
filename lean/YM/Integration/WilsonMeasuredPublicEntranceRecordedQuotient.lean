import YM.Integration.WilsonPhysicalPositionCocycleNative
import YM.RG12.Roof.Echelons

/-! The lower engineering plane in the actual physical frame, before any thermal rescaling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceRecordedQuotient
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open Extra.FD RG12.Roof
open WilsonPhysicalPositionAdmissible (Native)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

theorem own {d:ℕ}(B:RStage C.labels d)(i:Fin (B.m+1)):
    B.b i∈LinearMap.range ((scheme C.labels).rise (B.cap i)):=by
  obtain ⟨j,hj,hb⟩:=weighs_corner C.labels B i
  let raw:Labels.Label G d:=(C.labels.level d).basis j
  refine ⟨UVNext.FreeStress.embed C.labels (B.w i).1
    ⟨raw.val,enough_height C.labels j hb.le⟩,?_⟩
  rw [hj]
  exact UVNext.FreeStress.rise_embed C.labels (scheme C.labels) (scheme_filters C.labels) ..

theorem upper {d k:ℕ}(B:RStage C.labels d)(hk:k≤d)(i:Fin (B.m+1))
    (above:k<(B.w i).1)(v:D k):B.b.coord i ((scheme C.labels).rise hk v)=0:=by
  let low:=recorded C.labels k
  have vanishes(j:Fin (low.m+1)):B.b.coord i ((scheme C.labels).rise hk (low.b j))=0:=by
    have eq:=price_coord C.labels B i ((scheme C.labels).rise hk (low.b j)) 2
    rw [gear_rises,Pert.Scale.rare,map_smul,map_smul] at eq
    by_contra nz
    have diff:(low.w j).1≠(B.w i).1:=((low.cap j).trans_lt above).ne
    apply diff
    have e:(2:ℂ)^(low.w j).1=(2:ℂ)^(B.w i).1:=mul_right_cancel₀ nz (by simpa using eq)
    exact pow_right_injective₀ (by norm_num : (0:ℝ)<2) (by norm_num) (show (2:ℝ)^_=2^_ by exact_mod_cast e)
  rw [←low.b.sum_repr v,map_sum,map_sum]
  simp_rw [map_smul,vanishes,smul_zero,Finset.sum_const_zero]

/-- Arbitrary old physical graph values drop out before the choice of the thermal scalar. -/
theorem unscaled (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)(d:ℕ):
    ∀ᶠ r in trail,∀{k:ℕ}(hk:k≤d)(i:Fin ((recorded C.labels d).m+1)),
      k<((recorded C.labels d).w i).1→∀(v:S.Field d)(old:S.Field k),
      (recorded C.labels d).b.coord i ((J r d).symm (v-F.sector.derivatives.rise hk old))=
      (recorded C.labels d).b.coord i ((J r d).symm v):=by
  filter_upwards [WilsonPhysicalPositionCocycleNative.purchased F J lead d] with r paid k hk i high v old
  have issued:=paid.lower hk ((J r k).symm old)
  rw [LinearEquiv.apply_symm_apply] at issued
  rw [map_sub,←issued,LinearEquiv.symm_apply_apply,map_sub,upper (recorded C.labels d) hk i high,sub_zero]

theorem native {d:ℕ}(B:RStage C.labels d)(T:Module.End ℂ (D d))(h:Native C T)
    (i j:Fin (B.m+1))(above:(B.w j).1<(B.w i).1):
    B.b.coord i ((T-1) (B.b j))=0:=by
  obtain ⟨a,ha⟩:=own B j
  obtain ⟨b,hb⟩:=h.lower (B.cap j) a
  change B.b.coord i (T (B.b j)-B.b j)=0
  rw [←ha,←hb,map_sub,upper B (B.cap j) i above,upper B (B.cap j) i above,sub_self]

end YM.Integration.WilsonMeasuredPublicEntranceRecordedQuotient
