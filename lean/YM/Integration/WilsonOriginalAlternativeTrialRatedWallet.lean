import YM.Integration.WilsonOriginalAlternativeTrialScales
import YM.Integration.WilsonOriginalAlternativeTrialCapital

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialRatedWallet
open Filter Finset Lattice Wilson RG Marker PhysicalNext.Repeat.Legato WilsonThermometerMixedCollarSubpower
open scoped Topology
variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] (d:V→ℕ)
local notation "C₀" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "mesh" => R.family.S.a

theorem original (simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (forecast:WilsonReportLampForecast.Ready (C₀).path.levels)(span power:ℕ)(B:ℝ):
    ∀ᶠ f:ℕ in atTop,∀K,f≤K→mesh f/mesh K≤(H f)^span→
      scale (H K) ≤ 2*scale (H f) ∧ ((K-f:ℕ):ℝ)*Real.log 2 ≤ span*Real.log (H f) ∧
      ∀N p (_live:K≤N) (_ref:∀j,(C₀).ref (d j)≤K), ((C₀).path.levels.params K).supportExponent=100→
      ∀(o:V→Site ((C₀).side K p))(v:∀j,(C₀).label (d j)),
        (∀j,((C₀).labels.level (d j)).coeffSize (v j)≤B*(H K)^power)→∀j,
        ((WilsonOriginalAlternativeTrialWallet.radius R d N p K o v (100+1+1) 1) j)⁻¹≤(H f)^(2*(6+power)+1):=by
  have hot:=Next.Rank.Station.hat_rate R.family.path.levels simple
  obtain ⟨first,paid⟩:=eventually_atTop.mp (WilsonOriginalAlternativeTrialCapital.original R d simple pace forecast)
  filter_upwards [hot.eventually_ge_atTop (((Fintype.card V:ℝ)+1)*(1+B)),eventually_ge_atTop first,
    WilsonOriginalAlternativeTrialScales.original R simple span] with f cash f0 scale K fk distance
  obtain ⟨temp,z,width⟩:=scale K fk distance
  refine ⟨z,width,?_⟩
  intro N p live ref law o v cost j
  have source:=paid K (f0.trans fk) N p live ref law o v 1 (by norm_num) j
  rw [div_one] at source
  have hk:1≤H K:=(R.family.path.levels.fits.delayed _).le
  have hf:1≤H f:=(R.family.path.levels.fits.delayed _).le
  have bigger:1≤(H K)^(6+power):=one_le_pow₀ hk
  have charge:1+(H K)^6*((C₀).labels.level (d j)).coeffSize (v j)≤(1+B)*(H K)^(6+power):=by
    calc _ ≤ 1+(H K)^6*(B*(H K)^power):=by gcongr;exact cost j
         _ = 1+B*(H K)^(6+power):=by rw [pow_add];ring
         _ ≤ _:=by linarith only [bigger]
  calc _ ≤ _:=source
       _ ≤ ((Fintype.card V:ℝ)+1)*((1+B)*(H K)^(6+power)):=by gcongr
       _ = (((Fintype.card V:ℝ)+1)*(1+B))*(H K)^(6+power):=by ring
       _ ≤ (H f)*((H f)^2)^(6+power):=mul_le_mul cash (pow_le_pow_left₀ (zero_le_one.trans hk) temp _)
         (pow_nonneg (zero_le_one.trans hk) _) (zero_le_one.trans hf)
       _ = (H f)^(2*(6+power)+1):=by simp only [pow_succ,pow_mul];ring

end YM.Integration.WilsonOriginalAlternativeTrialRatedWallet
end
