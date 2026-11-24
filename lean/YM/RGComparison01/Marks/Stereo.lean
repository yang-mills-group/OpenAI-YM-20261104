import YM.RGComparison01.Rights
import YM.RGComparison01.Marks.Borders
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Tensor WilsonStartup
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {K : KernelChoices} {C Z W' μ σ Λ σ' C' T : ℝ} {q q' n k b p w: ℕ} {v d W u : ℝ→ℝ}
namespace Kraal
namespace Stereo
variable (Q : ConnectedActivityE6.Target G P) (o: Target.Order G W') (J:Patch)
    (A:Before G σ C J.J K (p+3)) (c c': Clip) (hq:Bolt G J.L d) (E : FiberFee Q.table ((p+3)+1)) (R : BareRates.pre G σ' C' (p+3))
local notation "M" => A.tables c J
-- Schedule.Spell returned uniformly for this role. Needs assets paid before Launch.
def Board (μ:ℝ) (j j' q q' n k:ℕ) (r f f':ℝ→ℝ) (V:ℝ→ℝ) (C₀ D:ℝ) (T U X₁ X₂ : ℝ→ℝ) (t:ℝ) : Prop :=
    ∀ (a b:Side) (S:StepData a b) (Y:Tube G S) (F:Forest S.ratio) (hh:S.patch=J) (hK:S.kernel=K), Quilt Y F (d t) → Y.high=c → Y.low=c' → Y.up.Bounds c σ C (ConnectedActivityE6.loopBill G J.L t) → ∀ Λ, Y.down.Bounds c' σ' C' Λ → ∀ ρ: Bid.Dir G a→ AxisChart G F,(warm A hh hK).Service F Y.high Y.up ρ→ ClassicalMatch F Y.high Y.low Y.up Y.down ρ →
    ∀ i:S.Choices, ∀ (X : Coat Y F), X.x=t→ X.width=o.K → X.manifest → ∀ (B B' : BudgetPoint) (m' β:ℝ), Cash W' t μ J.L Q o m' Y (Pane.virgin Y B β)→ B'.threshold=Pressure.temp t → flags (Pressure.temp t) X.V=∅ → 1 < r t → ∀ y: Positions (Uniform.Primary a G), X.V=represent (tint G _ y) →
    let D':=wick G J.L D t; let r':=r t*gStep β
    ‖y‖+furl G J.L t < r' → ∀ E e, Probe E p j (q+1) r' D' (f t) (f t) → Render F ρ B β e E q r' D' C₀ →
      Tower Q.table Y F i ρ B β e E n p k q q' j' (T t) (U t) (X₂ t) D' (f' t) r'⁻¹ r' (V t) (X₁ t) y

include R hq E
lemma lacesS (he:0<μ) (hs:n+(q'+q*n)<p) (h₀:n+2<p) (hk:k<p) (hn:1≤n) :
    ∃ D:ℝ,0<D∧∀ r f f' V: ℝ→ℝ, Geo G J.L r→Geo G J.L f → Geo G J.L f' → Geo G J.L V → ∀ C₀ j j', ∃ u v U X: ℝ→ℝ,
      Geo G J.L u∧Geo G J.L v ∧ Geo G J.L U∧ Geo G J.L X ∧ ∀ᶠ t in atTop, Board (σ':=σ') (C':=C') (d:=d) Q o J A c c' μ j j' q q' n k r f f' V C₀ D u v U X t := by
  by_cases hp : 0 < (M).gap; swap
  · let k' (_:ℝ):=(0:ℝ); have hh:Geo G J.L k':=Geo.fixed _
    refine ⟨1,zero_lt_one,fun r f f' V hr h hp hv C₀ j j'=>⟨k',k',k',k',hh,hh,hh,hh,Eventually.of_forall fun t a b S Y F h ht hQ hu hv hF Λ hB ρ hp' hh i=>?_⟩⟩
    subst J; subst K; subst c; exact (show ¬ 0 < (A.tables Y.high S.patch).gap from (by assumption)) (A.receipt F i hF hQ.large rfl rfl|>.1.pos_m)|>.elim -- syntax
  obtain ⟨D,hD,hU⟩:= AuxDesk.quorum Q o J A c' c d hq E R μ he (by omega)
  have hr:= Geo.primary J Q.table c A E hq
  refine ⟨D,hD,fun r f f' V hh hf hp' hv C₀ j j'=>?_⟩
  obtain ⟨T₀,A₀,U₀,V₀,h₁,h₂,h₃,h₄,H⟩:= equipped (σ:=σ) (C:=C) Q.table K n p k q q' M hp hr hq hf hp' hh hv hD Q.table_exists j j' hs h₀ hn hk C₀
  refine ⟨T₀,A₀,U₀,V₀,h₁,h₂,h₃,h₄,?_⟩; filter_upwards [hU,H, upper_guard hh.rate,Delay.shift_pos G J.L] with t ht hw hh hx a b S Y F hJ hK hg hT hL hC ll hP ρ hρ hv i' X hX hu H' B B' m' β hQ hB hF hg' y ha M' d' he E' e hE hy
  have hI:=hQ.laws.intake; have hX': ‖y‖ < eaves G J.L t := (lt_of_le_of_lt (le_add_of_nonneg_right (show 0 ≤ furl G J.L t from (Real.rpow_pos_of_pos hx _).le)) he).trans_le (hh β (by rw [← hJ]; exact hI.window.1) hg')
  have Hp:= ht a b S Y F hJ hK hg hT hL hC ll hP ρ hρ hv i' X hX hu H' B B' m' β hQ hB hF y ha hX'
  exact (hw a b S Y (warm A hJ hK) F B i' ρ y P β (hJ ▸ rfl) hK hg (by subst J; subst K; rw [hT]; rfl) hI hg' hρ _ (by rw [hT]; exact hC) Hp he E' e hE hy)
end Stereo
end Kraal
end YM.RGComparison01
