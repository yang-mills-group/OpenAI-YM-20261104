import YM.RGComparison.Core16.Stem.Dome

/-!
# Taylor germs on the true joint (issuers) vs the intended A/Fk connected-normalized law

Not a global IR or field limit and costs in germ ID AFTER fixing every geometry. Model law
incorporates β offsets charged elsewhere; this consumes physical TOP β itself. `Visible` pressure f for
near re-expression only AFTER choosing θ-independent displacement orientation. Projection merely estimates
with masks, does not redefine F data. Coalescent ext argument restored with exp(−1) so costs expressed
in Γ primitive; same mult in numerator & denominator. No Jacobian omitted. `P.expect` relation with
actual normalized Markov inertia after deployment (HP).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Fk
open Function Filter Set Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side} {ι k L T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D][Fintype L]
variable {X:Shelf G A D} (P: Planet X S ι k T) (Z:ChartRatio G)
local notation "Δ"=> Module.finrank ℝ (Panel G ι)
local notation "μ"=> Chart.tangent G ι
local notation "λ#"=> skillet G ι

def scene (p: Stuff G ι L)(v:Door G ι)(j:L): G.Color:= Sum.elim (fun i=>G.curvature (spread v.2 i)) (fun e=>v.1 • e) (p j)

def cap (p: Stuff G ι L)(ψ:(L→G.Color)→ℝ)(v:Door G ι):= Chart.jacobian Z v.2*ψ (scene p v)

def harvest (p:Stuff G ι L) (ψ:(L→G.Color)→ℝ) := stamp μ (cap Z p ψ) (rise P) 1

-- left of actual sector factors. Uses normalized Markov pref before dropping; f is numerator or vacuum.
def phaseAmt (U:Set (Sky G ι))(f: Melody G ι) (g:ℝ) := Real.exp (-1) * ((g^Δ)⁻¹ * ∫ x in U,(P.bureau g) x * f g x ∂ λ#)
variable {P Z} (H:P.Steady)(hZ: LocalRatio Z)
variable {p: Stuff G ι L}{ψ:(L→G.Color)→ℝ}{f:Melody G ι}{N:ℕ}{C:ℝ}(hF:Visible X ψ f p N C)
lemma deckspace (X:Shelf G A D) (Y:Good X) : ∀ᶠ x:Panel G ι in 𝓝 0,crisp (X.δ/2) Finset.univ (spread x):= by
    let u:= spread (G:=G) (ι:=ι); have hu : Tendsto u (𝓝 0) (𝓝 1):=tendsto_pi_nhds.mpr fun i=> by simpa [u,spread] using! ((show Continuous fun x:Panel G ι=> G.lieExp (x i) from by fun_prop).tendsto 0)
    exact hu.eventually ((crisp_open ..).mem_nhds (show crisp (X.δ/2) Finset.univ 1 from fun i _=> by simp [Y.extent.1]))

include H hZ hF
omit [Fintype L] in
lemma gate : ∃ d>0, d ≤ Chart.small G Z ∧ ∀ r∈Ioo 0 d,∀ g>0, amen X g →
    phaseAmt P (Chart.chamber G ι r) f g=chartLine μ (cap Z p ψ) (rise P) 1 g r := by
   obtain ⟨b,hb,h⟩:=Metric.mem_nhds_iff.mp (deckspace (ι:=ι) X H.prices); refine ⟨min b (Chart.small G Z),lt_min hb (Chart.Ratio.small_pos hZ),min_le_right ..,fun r hr g hg ha=>?_⟩
   obtain ⟨J,hJ,he,hH⟩:=hF.stamp
   let U x:= P.bureau g x*f g x; let f' (v:Panel G ι):=Chart.jacobian Z v * U (spread v); let u (v:Panel G ι):=g • ((1:ℝ), v)
   unfold phaseAmt; rw [show (∫ x in Chart.chamber G ι r,U x∂λ#)= _ from Chart.Ratio.chamber_integral hZ (U:=ι) _ ((bureau_env H ha).meas.mul (hF.env g ha).meas) (hr.2.trans_le (min_le_right ..)) hr.1]
   let I:= disc (E:=Panel G ι) g r; let B:= ball (0:Panel G ι) r
   have H₁ (x:Panel G ι) : B.indicator f' (g • x) = I.indicator (fun x=> f' (g • x)) x:= by
      by_cases h:x∈I
      · rw [indicator_of_mem h, indicator_of_mem (show g • x ∈ B from h)]
      rw [indicator_of_notMem h, indicator_of_notMem (show g • x∉B from h)]
   have hi:= Measure.integral_comp_smul_of_nonneg μ (B.indicator f') g (hR:=hg.le); simp_rw [H₁] at hi; rw [integral_indicator (s:=I) (disc_meas ..), integral_indicator (s:=B) isOpen_ball.measurableSet] at hi
   have hP (v:Panel G ι)(hy:v∈I):Radial.projection (cap Z p ψ) (rise P) g ((1:ℝ),v) = Real.exp (-1)* f' (g • v):=by
       let w := g • v; let x:=u v; let y:=spread w; let E:=rise P x; let V:=P.F g
       have ha' : x=(g,w):= Prod.ext ((mul_one g)) rfl
       have hv: crisp (X.δ/2) Finset.univ y:= h (ball_subset_ball (hr.2.trans_le (min_le_left ..)|>.le) hy)
       have hq : crisp X.δ Finset.univ y:=crisp_negligible _ _ (half_le_self H.prices.extent.1.le) (le_refl _) hv
       have hM : V.output g y= Real.exp (-E/g^2)*Real.exp 1:=by
            have hc (t:T): E = g^2+V.action t y:=by unfold E; rw [ha']; exact wages H (g,w) ha hq t
            have hz (t:T): V.cash t g y=Real.exp (-E/g^2)*Real.exp 1:=by unfold Base.cash; rw [←Real.exp_add,hc t]; congr 1; field_simp; ring
            unfold Base.output; simp_rw [hz,← Finset.sum_mul]; rw [show ∑ t,V.choices t y=_ from (H.tickets g ha).normalized y,one_mul]
       have hx : f g y=ψ (scene p x):=by
            rw [hH g ha hg y (crisp_negligible _ _ le_rfl (Finset.subset_univ _) hv)]; apply congr_arg ψ; funext i
            unfold scene; rw [Pi.smul_apply,book,ha']; rcases hp:p i with k|k; exact smul_inv_smul₀ hg.ne' _; rfl
       rw [projection_eq]; change cap Z p ψ x * Real.exp (-E/g^2)=Real.exp (-1)*(Chart.jacobian Z w*(V.output g y*f g y)); rw [hx,hM]; unfold cap; rw [ha']; dsimp only; rw [Real.exp_neg]; field_simp
   change Real.exp (-1) * ((g^Δ)⁻¹ * ∫ x in B,f' x ∂μ) = ∫ x in I, Radial.projection (cap Z p ψ) (rise P) g ((1:ℝ),x) ∂μ
   rw [show (g^Δ)⁻¹ * _= _ from hi.symm,← integral_const_mul]; apply setIntegral_congr_fun (disc_meas ..) fun x hx=> (hP x hx).symm
end YM.RGComparison.Core16.Lumen.Fk
