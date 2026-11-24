import YM.Integration.WilsonOriginalPublicPlantedGramFilms
import YM.Integration.WilsonOriginalPublicPlantedPair

/-! Reflected control on the actual short mesh. The eigenvalue floor precedes
every inner Taylor order, planting depth, test node and finite physical input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedShortGram
open Set Finset Filter Function Metric Lattice Maxwell Maxwell.Wick XSpace XSpace.Cirrus
open XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register MS MS.Land MS.Menus MS.Theater
open Source Labels Local.Physical PowerSeries RG PhysicalNext.Repeat.Legato
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPositionProgramPublicReflectedRead (lower)
open WilsonOriginalPublicPivotCross (detector)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonOriginalPublicPlantedGramFilms (reflected pupil)
open WilsonOriginalPublicPlantedPair (residual)
open scoped Topology Classical BigOperators
variable {G:Gauge}(Z:WilsonPrescription G){sg:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z sg M T dial){d:ℕ}{I L:Type}[Fintype I][Fintype L]{β:Local.Physical.Deck G}
    (ax:Axis)(leg:I→Glyph β d)(l:Filter ℝ){t:ℝ→ℝ}
    (pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))

include H pos small in
theorem matrix (τ C lo hi:ℝ)(hp:0<τ)(hc:0<C)(hl:0<lo)(q:ℕ) :
    ∃ ρ:ℝ,0<ρ ∧ ∀ᶠ r in l,∀j:ℕ,
      lo*(-Real.log (t r))≤ -Real.log (Z.run.step j).spacing →
      -Real.log (Z.run.step j).spacing≤hi*(-Real.log (t r)) →
      ∀(X:L→Sample 2)(μ:L→ℂ),(∀h,(X h).F=Z.run.step j) →
      (∀h,welcome (X h) ∧ dist (familiar (X h)) (lower ax)<ρ) →
      ∑h,μ h=1 → ∑h,‖μ h‖≤C → ∀u:ℝ,|u|≤8*t r →
      ‖(fun i k=>detector Z.scheme X μ q u (reflected Z ax j (leg i)*pupil Z j (leg k)))-
        reading ax (nodes ax) leg‖≤τ := by
  let κ:=Real.log Z.run.ratio
  have hk:0<κ:=Real.log_pos (show 1<(Z.run.ratio:ℝ) by
    exact_mod_cast (show 1<Z.run.ratio from (by decide:1<3).trans_le Z.run.large))
  obtain ⟨j₀,ρ,hr,paid⟩:=WilsonOriginalPublicPlantedGramFilms.original (L:=L)
    Z H ax leg τ C hp hc l pos small 1 (hi/κ) q
  have clock:Tendsto (fun r=>-Real.log (t r)) l atTop:=
    tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨small,pos⟩))
  refine ⟨ρ,hr,?_⟩
  filter_upwards [paid,clock.eventually_ge_atTop ((j₀:ℝ)*κ/lo)] with r fee late j floor ceiling
  have age:-Real.log (Z.run.step j).spacing=(j:ℝ)*κ:=by
    change -Real.log (((Z.run.den j:ℕ):ℝ)⁻¹)=_
    simp [XSpace.Run.den,Real.log_pow,κ]
  rw [age] at floor ceiling
  have lower: (j₀:ℝ)*κ≤(j:ℝ)*κ:=
    ((div_le_iff₀ hl).mp late).trans (by simpa only [mul_comm lo] using floor)
  have higher:j₀≤j:=by exact_mod_cast (mul_le_mul_iff_left₀ hk).mp lower
  have upper:(j:ℝ)≤hi/κ*(-Real.log (t r))^1:=by
    rw [pow_one,div_mul_eq_mul_div]
    exact (le_div_iff₀ hk).mpr ceiling
  obtain ⟨P⟩:=H.packets j (Handoff.Directory.budget G 2 d+q)
  exact fee j higher upper P le_rfl

include H pos small in
theorem original (R:Run G)(each:Injective leg):
    ∃k:ℝ,0<k ∧ ∀ C lo hi:ℝ,0<C → 0<lo → ∀q:ℕ,
    ∃ ρ:ℝ,0<ρ ∧ ∀ᶠ r in l,∀j:ℕ,
      lo*(-Real.log (t r))≤ -Real.log (Z.run.step j).spacing →
      -Real.log (Z.run.step j).spacing≤hi*(-Real.log (t r)) →
      ∀(X:L→Sample 2)(μ:L→ℂ),(∀h,(X h).F=Z.run.step j) →
      (∀h,welcome (X h) ∧ dist (familiar (X h)) (lower ax)<ρ) →
      ∑h,μ h=1 → ∑h,‖μ h‖≤C → ∀ν:ℝ,|ν|≤8*t r →
      ∀(d₀:Fin 2→ℕ)(v:(i:Fin 2)→(R.family.labels.level (d₀ i)).Coeff)(a:I→ℂ)
        (coarse:ℂ)(c z u e b:ℝ),
      let E:=residual R Z.scheme d₀ v X μ q ν a (fun i=>reflected Z ax j (leg i)) (fun i=>pupil Z j (leg i))
      0≤c → 1≤z → 0≤u → e*u≤1 → e*u^2≤1 → b≤1 →
      ‖coarse‖≤c*z^2 → ‖sampled R Z.scheme d₀ v X μ univ q ν-coarse‖≤1 →
      ‖E {0}‖≤e*u*‖a‖ → ‖E {1}‖≤e*u*‖a‖ → ‖E univ‖≤e*u^2+b →
      ‖a‖ ≤ max 1 ((c+5)/k)*z:=by
  obtain ⟨k,τ,hk,hτ,price⟩:=WilsonOriginalPublicPivotReflected.original R Z.scheme ax leg each
  refine ⟨k,hk,?_⟩
  intro C lo hi hc hl q
  obtain ⟨ρ,hr,paid⟩:=matrix (L:=L) Z H ax leg l pos small τ C lo hi hτ hc hl q
  refine ⟨ρ,hr,?_⟩
  filter_upwards [paid] with r fee j floor ceiling X μ hs room mass tv ν hν d₀ v a coarse c z u e b E
    cp zp up first both last gross hearing left right double
  apply price d₀ v X μ q ν coarse _ a c z u e b cp zp up first both last
    (fee j floor ceiling X μ hs room mass tv ν hν) gross hearing
  rw [norm_sub_rev,WilsonOriginalPublicPlantedPair.full]
  calc
    _≤(‖E {0}‖+‖E {1}‖)+‖E univ‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _≤(e*u*‖a‖+e*u*‖a‖)+(e*u^2+b):=add_le_add (add_le_add left right) double
    _=_:=by ring

end YM.Integration.WilsonOriginalPublicPlantedShortGram
