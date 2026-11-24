import YM.Integration.WilsonSeparatedOriginalProfileCut

/-! A cofinal successor-cutoff receipt holds on every admitted original joint regulator filter. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalProfileMarch
open Filter Function Extraction Spec RG12 RG17 Lattice Wilson RG Source Extra.Histories PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table}(L:Layout F)

theorem admitted {l:Filter UVIndex}(sub:l ≤ L.lens)(K P:ℕ):∀ᶠ z in l,K ≤ z.1 ∧ P ≤ z.2:=by
  have period:∀ᶠ z in order.fuse,P ≤ z.2:=by
    rw [Extraction.Order.fused,Extraction.Order.late]
    filter_upwards [order.per.cofinal.eventually_ge_atTop P] with p far
    exact Eventually.of_forall fun _=>far
  exact ((Next.UVStress.large_mesh order K).and period).filter_mono (sub.trans L.certified)

theorem original (a:ℝ){s:ℕ→ℕ→Prop}(steps:∀ᶠt:ℕ in atTop,∀per:ℕ,a<R.family.S.radius per → s (t+1) per)
    {l:Filter UVIndex}(sub:l ≤ L.lens):∀ᶠz:UVIndex in l,s z.1 z.2:=by
  obtain ⟨t,cut⟩:=eventually_atTop.1 steps
  obtain ⟨v,room⟩:=eventually_atTop.1 (R.family.S.radius_diverges.eventually_gt_atTop a)
  filter_upwards [admitted L sub (t+1) v] with z late
  obtain ⟨high,far⟩:=late
  have h:=cut (z.1-1) (by omega) z.2 (room _ far)
  simpa only [show z.1-1+1=z.1 by omega] using h

end YM.Integration.WilsonSeparatedOriginalProfileMarch
