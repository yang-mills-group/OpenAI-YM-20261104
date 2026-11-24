import YM.Integration.WilsonMarkedIndependentMixedIntegratedHistory

/-! The signed winding price is uniform in every finer cutoff before the
physical period limit. It therefore survives taking the UV limit first. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedOrderedWinding
open Function Filter Lattice Wilson RG WilsonCoeffUV.Winding
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open WilsonMarkedIndependentMixedMomentPrice (Earned)
open scoped Topology
variable {G:Gauge}{m b:ℕ}{V:Type}[NormedAddCommGroup V]

theorem disappears (R:Run G)(s:ℝ)(hs:0<s):
    Tendsto (fun p=>catchW s (R.family.side b p)) atTop (𝓝 0):=by
  have grow:Tendsto (fun p:ℕ=>(R.family.side b p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(R.family.side b p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator b).pos).tendsto_atTop
  exact (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hs) tendsto_natCast_atTop_atTop)).comp grow

theorem uniform (R:Run G){s:ℝ}(hs:0<s){X:ℕ→ℕ→V}{Y:ℕ→V}
    (h:Earned m (fun p=>catchW s (R.family.side b p)) X (fun N _=>Y N)):
    ∀ε:ℝ,0<ε → ∀ᶠp:ℕ in atTop,∀N,m≤N → ‖X N p-Y N‖<ε:=by
  obtain ⟨C,_,paid⟩:=h
  intro ε eps
  have decay:Tendsto (fun p=>C*catchW s (R.family.side b p)) atTop (𝓝 0):=by
    simpa only [mul_zero] using (disappears R s hs).const_mul C
  filter_upwards [paid,decay.eventually_lt_const eps] with p both small
  exact fun N top=> ((both N top).2.2).trans_lt small

theorem ultraviolet (R:Run G){s:ℝ}{X:ℕ→ℕ→V}{Y:ℕ→V}{x:ℕ→V}{y:V}
    (h:Earned m (fun p=>catchW s (R.family.side b p)) X (fun N _=>Y N))
    (finite:∀ᶠp:ℕ in atTop,Tendsto (fun N=>X N p) atTop (𝓝 (x p)))
    (covered:Tendsto Y atTop (𝓝 y)):
    ∃C:ℝ,0≤C ∧ ∀ᶠp:ℕ in atTop,‖x p-y‖≤ C*catchW s (R.family.side b p):=by
  obtain ⟨C,hC,paid⟩:=h
  refine ⟨C,hC,?_⟩
  filter_upwards [finite,paid] with p converges before
  exact le_of_tendsto ((converges.sub covered).norm) ((eventually_ge_atTop m).mono fun N top=>(before N top).2.2)

theorem ordered (R:Run G){s:ℝ}(hs:0<s){X:ℕ→ℕ→V}{Y:ℕ→V}{x:ℕ→V}{y:V}
    (h:Earned m (fun p=>catchW s (R.family.side b p)) X (fun N _=>Y N))
    (finite:∀ᶠp:ℕ in atTop,Tendsto (fun N=>X N p) atTop (𝓝 (x p)))
    (covered:Tendsto Y atTop (𝓝 y)):Tendsto x atTop (𝓝 y):=by
  obtain ⟨C,_,rows⟩:=ultraviolet R h finite covered
  have decay:Tendsto (fun p=>C*catchW s (R.family.side b p)) atTop (𝓝 0):=by
    simpa only [mul_zero] using (disappears R s hs).const_mul C
  rw [Metric.tendsto_nhds]
  intro ε eps
  filter_upwards [rows,decay.eventually_lt_const eps] with p paid small
  exact (dist_eq_norm (x p) y).symm ▸ paid.trans_lt small

end YM.Integration.WilsonMarkedIndependentMixedOrderedWinding
end
