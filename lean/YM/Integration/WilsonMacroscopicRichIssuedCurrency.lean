import YM.Integration.WilsonMacroscopicRichFilingNorm
import YM.RG16.Unmasked.Exit

/-! The earlier raw label and every actual incoming capture field differ by the original currency of that same filing. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichIssuedCurrency
open Filter Function Set Spec OPE OPE.Orbits PhysMS Cells Wilson RG16 RG16.Literal
open Trace.Physical.GermGraph Next.UVStress FilteredWilsonProduct RG MergeProof Bid
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}

theorem field (H:C.Makes){h u:ℕ}(doors:∀p,Opened C h u p):
    ∃A:ℝ,0≤A ∧ ∀N p (uN:u≤N) (Y:Cut C N p)(z:C.label h)(e:ℝ),
    mCost C h N p u (topReport C N p h H u (doors p) uN Y -
      (C.factory h N p).terminal.symm z)≤e →
    ‖label (w:=(N,p)) H (doors p) uN Y-z‖≤A*e:=by
  obtain ⟨L,nn,buy⟩:=quota_stop C H (doors 0).post
  refine ⟨L*2,mul_nonneg nn zero_le_two,?_⟩
  intro N p uN Y z e currency
  let T:=(C.factory h N p).terminal
  let x:=topReport C N p h H u (doors p) uN Y
  let Δ:=x-T.symm z
  have gap:quota C h u N p (T Δ)≤2*e:=by
    unfold quota
    change (C.labels.level h).coeffSize ((C.factory h N p).entries u (T.symm (T Δ))).x ≤ _
    rw [T.symm_apply_apply]
    exact (size_gap h N p u H (doors p) uN Δ).2.trans (mul_le_mul_of_nonneg_left currency zero_le_two)
  have equality:T Δ=label (w:=(N,p)) H (doors p) uN Y-z:=by
    dsimp only [Δ]
    rw [map_sub,T.apply_symm_apply]
    rfl
  rw [←equality,mul_assoc]
  exact (buy N p (T Δ) uN).trans (mul_le_mul_of_nonneg_left gap nn)

theorem rate (simple:G.Simple)
    (pace:∀m,((C.S.block m).val:ℝ)≤Real.log (Lambda C.path.levels m))
    (h u:ℕ)(M B:ℝ)(hM:0<M)(hB:20<B)(E:ℕ→ℝ)(generated:RateIs atTop C.S.scale E (-h))
    (A σ:ℝ)(small:σ<1/8):
    ∀ᶠ m:ℕ in atTop,A*(E m/gainChart C.path (port C (8*M) B (mul_pos (by norm_num) hM) m) u) ≤
      (C.S.a m)^h*Real.exp (-σ*C.S.scale m):=by
  have hb:=port_height C simple (8*M) B (mul_pos (by norm_num) hM) (by linarith only [hB]) pace
  have tariff:=generated.div (gain_toward C u hb)
  have result:=RateIs.overtakes (((normal_height C).mesh.power h).mul (RateIs.exp (-σ) C.S.divergent))
    ((RateLE.const A C.S.divergent).mul (tariff.pays C.S.divergent)) C.S.divergent (by linarith only [small])
  exact result.mono fun _ hcut=>hcut.le

end YM.Integration.WilsonMacroscopicRichIssuedCurrency
