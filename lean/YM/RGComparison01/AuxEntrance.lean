import YM.RGComparison01.AuxSpell

/-! # Financing the auxiliary test on a fixed stage. Use construction's actual
 post-block table receipts. No statement permitting variation of those constants
 with coupling/cutoff automatically. `AuxSpell.equipped` can instead be used on
 further tests *after* these purchases if paid for. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxEntrance
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {K : KernelChoices} {C Z W' μ σ Λ σ' C' T : ℝ} {q q' r p : ℕ} {f g v d w W u : ℝ→ℝ}
-- read has path Stage cost dependencies at the requested arbitrary derivative order
variable (Q : ConnectedActivityE6.Target G P) (o: Target.Order G W') (J:Patch)
 (A:Before G σ C J.J K (p+3)) (c c': Clip) (hq: Bolt G J.L d) (E : FiberFee Q.table ((p+3)+1)) (R : BareRates.pre G σ' C' (p+3))
local notation "M" => A.tables c J

include hq E R
lemma gate (h:Geo G J.L f) (hp : Geo G J.L g) (hv : Geo G J.L v) (hw : Geo G J.L w)
    (j₁ j₂ q q' n k:ℕ) (hs:n+(q'+q*n)<p) (h₀:n+2<p) (hk:k<p) (hn:1≤n) (he:0<μ) (m:ℝ):
    ∃ (D:ℝ),0<D∧∃ T C₀ Q' t':ℝ→ℝ, Geo G J.L T∧Geo G J.L C₀∧Geo G J.L Q'∧Geo G J.L t' ∧∀ᶠ t in atTop,
    ∀ (a b : Side) (S:StepData a b) (T':Tube G S) (F:Forest S.ratio) (hh:S.patch=J) (hK:S.kernel=K), Quilt T' F (d t) → T'.high=c → T'.low=c' → T'.up.Bounds c σ C (ConnectedActivityE6.loopBill G J.L t) → ∀ Λ, T'.down.Bounds c' σ' C' Λ → ∀ ρ: Bid.Dir G a→ AxisChart G F,(warm A hh hK).Service F T'.high T'.up ρ→ ClassicalMatch F T'.high T'.low T'.up T'.down ρ →
    ∀ i:S.Choices, ∀ (X : Coat T' F), X.x=t→ X.width=o.K → X.manifest → ∀ (B B' : BudgetPoint) (m' β:ℝ), Cash W' t μ J.L Q o m' T' (Pane.virgin T' B β)→ B'.threshold=Pressure.temp t →
    flags (Pressure.temp t) X.V=∅ → 1 < w t → ∀ y: Positions (Uniform.Primary a G), X.V=represent (tint G _ y) →
    let r:=wick G J.L D t; let d:=w t*gStep β
    ‖y‖+furl G J.L t < d → ∀ E e, Probe E p j₁ (q+1) d r (f t) (f t) → Render F ρ B β e E q d r m →
      Tower Q.table T' F i ρ B β e E n p k q q' j₂ (T t) (C₀ t) (Q' t) r (g t) d⁻¹ d (v t) (t' t) y := by
  by_cases hM : 0 < (M).gap; swap
  · let k' (_:ℝ) := (0:ℝ); have hh: Geo G J.L k':= Geo.fixed _
    refine ⟨1,zero_lt_one,k',k',k',k',hh,hh,hh,hh,Eventually.of_forall fun t a b S Y F h ht hQ hu hv hF Λ hB ρ hp hh i=>?_⟩
    subst J; subst K; subst c; exact (hM (A.receipt F i hF hQ.large rfl rfl|>.1.pos_m)).elim
  obtain ⟨D,hD,hU⟩:= AuxDesk.quorum Q o J A c' c d hq E R μ he (by omega)
  have hr:= Geo.primary J Q.table c A E hq
  obtain ⟨T₀,C₀,Q',D',hk₁,h₂,h₃,h₄,H⟩:= equipped (σ:=σ) (C:=C) Q.table K n p k q q' M hM hr hq h hp hw hv hD Q.table_exists j₁ j₂ hs h₀ hn hk m
  refine ⟨D,hD,T₀,C₀,D',Q',hk₁,h₂,h₄,h₃,?_⟩; filter_upwards [hU,H, upper_guard hw.rate,Delay.shift_pos G J.L] with t ht hw hh hx a b S Y F hJ hK hf hT hL hC ll hP ρ hρ hv i X hX hu hi B B' m' β hQ hB hF hg y ha r d' he
  have hI:=hQ.laws.intake; have hX': ‖y‖ < eaves G J.L t := (lt_of_le_of_lt (le_add_of_nonneg_right (show 0 ≤ furl G J.L t from (Real.rpow_pos_of_pos hx _).le)) he).trans_le (hh β (by rw [← hJ]; exact hI.window.1) hg)
  have Hp:= ht a b S Y F hJ hK hf hT hL hC ll hP ρ hρ hv i X hX hu hi B B' m' β hQ hB hF y ha hX'
  exact hw a b S Y (warm A hJ hK) F B i ρ y P β (hJ ▸ rfl) hK hf (by subst J; subst K; rw [hT]; rfl) hI hg hρ _ (by rw [hT]; exact hC) Hp he
end YM.RGComparison01.AuxEntrance
