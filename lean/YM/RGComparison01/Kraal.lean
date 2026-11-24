import YM.RGComparison01.Starlight
import YM.RGComparison01.AuxEntrance
/-!
# Combined auxiliary bills

 After-L, Kernel and q, but before waits on the SAME prices. A `Studio`
 is to be picked AFTER choosing width and purchasing the auxiliary
 wick; exponential stage tests live after their POSTS. A caller can
 nominate its support costs before the posts, its Probe analytic and
 model sup costs after the widths. These are bills, not assertions
 that the inputs will fit. -/

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
structure Floor (G:Gauge) (L:Side) where
  const : ℝ -- Render absolute-bound E globally sunny
  f : ℝ→ℝ -- E probe envelope
  letters : ℕ -- E growth in z (after d, but before support use)
  u : ℝ→ℝ -- certificate bound
  v : ℝ→ℝ -- expenditure-model at exponent one
  s : ℝ→ℝ -- Pencil Expo smooth
  ease : Geo G L f
  spans : Geo G L u
  keeps : Geo G L v
  wings : Geo G L s
-- allow after Stage and allocations
abbrev Buyer (G:Gauge) (L:Side) := (b:ℕ) → ℝ → (V:ℝ→ℝ) → Geo G L V → Floor G L
section aux
variable (Q : ConnectedActivityE6.Target G P) (o: Target.Order G W') (J:Patch)
    (A:Before G σ C J.J K (p+3)) (c c': Clip) (hq:Bolt G J.L d) (E : FiberFee Q.table ((p+3)+1)) (R : BareRates.pre G σ' C' (p+3))
local notation "M" => A.tables c J

-- Uniform financing for only unmarked role. If marked calls add Q.Marker later.
def Launch (μ:ℝ) (j q n k:ℕ) (r f:ℝ→ℝ) (C₀ D:ℝ) (T U : ℝ→ℝ) (t:ℝ) : Prop :=
    ∀ (a b:Side) (S:StepData a b) (Y:Tube G S) (F:Forest S.ratio) (hh:S.patch=J) (hK:S.kernel=K), Quilt Y F (d t) → Y.high=c → Y.low=c' → Y.up.Bounds c σ C (ConnectedActivityE6.loopBill G J.L t) → ∀ Λ, Y.down.Bounds c' σ' C' Λ → ∀ ρ: Bid.Dir G a→ AxisChart G F,(warm A hh hK).Service F Y.high Y.up ρ→ ClassicalMatch F Y.high Y.low Y.up Y.down ρ →
    ∀ i:S.Choices, ∀ (X : Coat Y F), X.x=t→ X.width=o.K → X.manifest → ∀ (B B' : BudgetPoint) (m' β:ℝ), Cash W' t μ J.L Q o m' Y (Pane.virgin Y B β)→ B'.threshold=Pressure.temp t → flags (Pressure.temp t) X.V=∅ → 1 < r t → ∀ y: Positions (Uniform.Primary a G), X.V=represent (tint G _ y) →
    let D':=wick G J.L D t; let r':=r t*gStep β
    ‖y‖+furl G J.L t < r' → ∀ E e, Probe E p j (q+1) r' D' (f t) (f t) → Render F ρ B β e E q r' D' C₀ →
      Pushed Q.table Y F i ρ B β e E n p k q r'⁻¹ (T t) (U t) y

include R hq E
lemma laces (he:0<μ) (hs:n+(0+q*n)<p) (h₀:n+2<p) (hk:k<p) (hn:1≤n) :
    ∃ D:ℝ,0<D∧∀ r f : ℝ→ℝ,Geo G J.L r→Geo G J.L f → ∀ C₀ j, ∃ u v : ℝ→ℝ,
      Geo G J.L u∧Geo G J.L v ∧ ∀ᶠ t in atTop, Launch (σ':=σ') (C':=C') (d:=d) Q o J A c c' μ j q n k r f C₀ D u v t := by
  by_cases hp : 0 < (M).gap; swap
  · let k' (_:ℝ):=(0:ℝ); have hh:Geo G J.L k':=Geo.fixed _
    refine ⟨1,zero_lt_one,fun r f hr h C₀ j=>⟨k',k',hh,hh,Eventually.of_forall fun t a b S Y F h ht hQ hu hv hF Λ hB ρ hp' hh i=>?_⟩⟩
    subst J; subst K; subst c; exact (hp (A.receipt F i hF hQ.large rfl rfl|>.1.pos_m)).elim
  obtain ⟨D,hD,hU⟩:= AuxDesk.quorum Q o J A c' c d hq E R μ he (by omega)
  have hr:= Geo.primary J Q.table c A E hq
  let i (_:ℝ):=(1:ℝ); have hi:Geo G J.L i:=Geo.fixed _
  refine ⟨D,hD,fun r f hh hf C₀ j=>?_⟩
  obtain ⟨T₀,A₀,U₀,V₀,h₁,h₂,h₃,h₄,H⟩:= equipped (σ:=σ) (C:=C) Q.table K n p k q 0 M hp hr hq hf hi hh hi hD Q.table_exists j 0 hs h₀ hn hk C₀
  refine ⟨T₀,A₀,h₁,h₂,?_⟩; filter_upwards [hU,H, upper_guard hh.rate,Delay.shift_pos G J.L] with t ht hw hh hx a b S Y F hJ hK hg hT hL hC ll hP ρ hρ hv i' X hX hu H' B B' m' β hQ hB hF hg' y ha M' d' he E' e hE hy
  have hI:=hQ.laws.intake; have hX': ‖y‖ < eaves G J.L t := (lt_of_le_of_lt (le_add_of_nonneg_right (show 0 ≤ furl G J.L t from (Real.rpow_pos_of_pos hx _).le)) he).trans_le (hh β (by rw [← hJ]; exact hI.window.1) hg')
  have Hp:= ht a b S Y F hJ hK hg hT hL hC ll hP ρ hρ hv i' X hX hu H' B B' m' β hQ hB hF y ha hX'
  exact (hw a b S Y (warm A hJ hK) F B i' ρ y P β (hJ ▸ rfl) hK hg (by subst J; subst K; rw [hT]; rfl) hI hg' hρ _ (by rw [hT]; exact hC) Hp he E' e hE hy).1
end aux

section fees
variable {L:Side}
lemma for_ritual (n p :ℕ) (h : Geo G L d) (hf : Geo G L u) : Geo G L (fun x=> ritual_fee n p (u x) 0 (d x)):= by
  let m:=n+p+1; have hw:=Geo.fixed (G:=G) (L:=L) 0
  let ht:=Geo.power h m
  exact (((Geo.fixed _).times (hf.joins hw)).times ht).joins ((hf.times ht).joins ((Geo.fixed _).times hw))
lemma dangerous (E : BareRates.pre G σ C n) (c:Clip) (k:ℕ) (f:ℝ) (hq:Bolt G L W) (hp: Geo G L v) : Geo G L (fun x=> Bonus.baseFee E c (W x) (ConnectedActivityE6.loopBill G L x) f (v x) k):= by
  let h:= (Geo.basic hq).power n
  have hh: Geo G L (ConnectedActivityE6.loopBill G L):= (Geo.fixed 2).times Geo.by_delay
  exact (for_ritual 2 k hp (h.times (Geo.fixed _))).joins (for_ritual 0 k hp (h.times (((Geo.fixed _|>.joins hh)).times (Geo.fixed _))))
lemma taller {x : ℝ} (hh : 0≤x) (k j:ℕ) (_hq: 0≤ C) (hp:C ≤ C') : ritual_fee j k C 0 x ≤ ritual_fee j k C' 0 x:= by unfold ritual_fee; dsimp; gcongr
lemma paces (E: BareRates.pre G σ C n) (c:Clip) (hv:0≤ BareRates.bill E c) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hΛ:0≤Λ) (h : 0 ≤ W') (hp:W' ≤ Z) (hk:ℕ) :
    Bonus.baseFee E c x Λ W' y hk ≤ Bonus.baseFee E c x Λ Z y hk := by
  unfold Bonus.baseFee; refine add_le_add le_rfl ?_; apply taller hy
  · unfold tollS; positivity
  unfold tollS; gcongr
end fees
end Kraal
end YM.RGComparison01
