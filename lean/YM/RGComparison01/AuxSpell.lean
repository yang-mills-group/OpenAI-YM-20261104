import YM.RGComparison01.AuxBeam

/-! # Give the estimates also back in *link-log* Taylor density readout units -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxSpell
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} (A:ChartRatio G) {L:Side} {p : Teller G} {K : KernelChoices}
    {C Z μ σ Λ D v u HR m' : ℝ} {n j k q q' r : ℕ} {f g v' d w W u' : ℝ→ℝ}
local notation "Φ" => Real.log
local notation "Ψ" => (fun x:ℝ=>x⁻¹)
local notation "H₀" => closedBall (0:ℝ) (1/2)
lemma power_core (k:ℕ) : ∃ C D:ℝ, 0<C ∧ 0<D ∧ (∀ y∈H₀, Brush k C 1 (fun t=> Real.log (t+1)) y)∧ ∀ y∈ H₀, Brush k D 1 (fun t:ℝ=>(t+1)⁻¹) y:= by
  have hh y (hy:y∈H₀): y+1≠0:= by have h:= (abs_le.mp (show |y| ≤ 1/2 from mem_closedBall_zero_iff.mp hy)).1; linarith
  obtain ⟨c,hc,h⟩:= Brush.compact (f:=fun t:ℝ=> Real.log (t+1)) (k:=k) (s:=H₀) (isCompact_closedBall ..) (fun i hi=> (contDiffAt_id.add contDiffAt_const).log (hh i hi))
  obtain ⟨d,hd,H⟩:= Brush.compact (f:=fun t:ℝ=>(t+1)⁻¹) (k:=k) (s:=H₀) (isCompact_closedBall ..) (fun i hi=> (contDiffAt_id.add contDiffAt_const).inv (hh i hi))
  exact ⟨c,d,hc,hd,h,H⟩

variable (K)
-- paid enough to also test consistency of constant coefficient via probes
lemma response (h : Rate G L 0 f) (hd:0 < D) (k:ℕ) (hk:1≤k) : ∃ T:ℝ→ℝ,
    ∀ᶠ t in atTop, let s:= eaves G L t; let r:= wick G L D t
     ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
     (ι:Type) [Fintype ι] [DecidableEq ι] (ϕ ψ : E×Poll.Body ι→ℝ) (ρ : E→Poll.Body ι) (M : E→Matrix ι ι ℝ), Golf ϕ ψ ρ M k r s s (f t) → Probe (AuxGrace.nodes ϕ ψ ρ M) k (AuxGrace.zgrade k) 0 s r (T t) (T t):= by
  obtain ⟨c,hc,hV⟩:=Brush.compact (f:=Real.exp) (k:=k) (s:=Icc (-1) 1) isCompact_Icc fun i _=> Real.contDiff_exp.contDiffAt
  let T t:=Lantern.clump k (Lantern.fee k (f t) (wick G L D t)) c
  have hf:=Lantern.fareRate k h (gen G L D)
  refine ⟨T,?_⟩; filter_upwards [(hf.mul (Sienna.edge G L)).below (by linarith only [Sienna.vow_ok]) _ zero_lt_one,Geo.wiggle (G:=G) (L:=L) D hd] with t ht he s r E _ _ _ ι _ _ ϕ ψ ρ M hk' using AuxFabric.shape hk' hV ((le_abs_self _).trans ht) hk he

section core
variable {K} {c a:Side} {S:StepData c a}
    (T:Tube G S) (F:Forest S.ratio) (i:S.Choices) (ρ:Bid.Dir G c→AxisChart G F)
    (B : BudgetPoint) (β:ℝ) (e:Config G a→ℝ)
local notation "X" => Positions (Uniform.Primary c G)
local notation "g₀" => gStep β
variable (E: Poll.Body (Precision.Key F G)→ℝ × Positions (Uniform.Primary c G)→ℝ)
local notation "x" => rescale F T A ρ B i β (gross e 1)
local notation "V" => noneCo A T F ρ i E q n

structure Pushed (n k j q : ℕ) (Z v C : ℝ) (y:X): Prop where
  receipt : 0 < assay F T A ρ i β y
  phase : x y∈ Set.Icc (1/2) (3/2)
  positive : 0 < weighLess T B β e y
  rate : AuxStage.Points v Z g₀ n j x y (noneCo A T F ρ i E q n)
  center : AuxStage.Points C Z g₀ n j (givenLog A T F ρ i B β e) y (logVia A T F ρ i E q n)

-- consumed at requested marked test, always paired
structure Tower (n k j q q' w : ℕ) (u v C D T' Z R Y L : ℝ) (y:X): Prop where
  unmarked : Pushed A T F i ρ B β e E n k j q Z u v y
  marked (J:Config G a→ℝ) (W : Poll.Body (Precision.Key F G) → ℝ × X→ℝ) (hp:Probe W k w q' R D T' T') (ht : Render F ρ B β J W q' R D Y):
    AuxStage.Points L Z g₀ n j (rescale F T A ρ B i β (gross e J)) y (AuxPackage.bill A T F ρ i E W q q' n) ∧
    AuxStage.Points C Z g₀ n j (read_J T B β e J) y (markCo A T F ρ i E W q q' n)
end core
variable (n k j q q' : ℕ)
local notation "β'" => (fun t=> betaF G t L)
lemma equipped (M:ChartPrices) (hM : 0 < M.gap) (h:Geo G L f) (hp : Bolt G L W) (hr : Geo G L u') (hh:Geo G L v') (hz:Geo G L w) (ht : Geo G L g) (hD : 0 < D) (hA : LocalRatio A)
    (j₁ j₂ : ℕ) (hs : n+(q'+q*n)<k) (h₀ : n+2<k) (hn : 1≤n) (hk : j<k) (m:ℝ) : ∃ T₀ C₀ Q Z':ℝ→ℝ, Geo G L T₀ ∧ Geo G L C₀ ∧ Geo G L Q ∧ Geo G L Z' ∧ ∀ᶠ t in atTop, ∀ (c l:Side) (S : StepData c l) (T:Tube G S) (p:Before G σ C S.patch.J S.kernel (k+3)) (F:Forest S.ratio) (B:BudgetPoint) (i:S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (y:Positions (Uniform.Primary c G)) (V':Teller G) (β:ℝ), S.patch.L=L→S.kernel=K→ Quilt T F (W t)→ p.tables T.high S.patch=M→ Intake V' T t (Pane.virgin T B β) → 1 < w t→
    p.Service F T.high T.up ρ→ ∀ Λ, T.up.Bounds T.high σ C Λ→ AuxDesk.receipt T p B F ρ i L A D (f t) t β y→
    let b:= wick G L D t; let r:=w t*gStep β
    ‖y‖+furl G L t < r → ∀ E e, Probe E k j₁ (q+1) r b (u' t) (u' t) → Render F ρ B β e E q r b m →
      Tower A T F i ρ B β e E n k j q q' j₂ (T₀ t) (C₀ t) (Z' t) b (v' t) r⁻¹ r (g t) (Q t) y:= by
  have hZ₀ := Geo.fixed (G:=G) (L:=L) 1
  have hx:n+(0+q*n) < k:=by omega
  obtain ⟨T₀,hT,H⟩:= AuxPackage.plenty (σ:=σ) (C:=C) A K n k j q 0 M hM h hp hr hZ₀ hz hZ₀ hD hA j₁ 0 hx hn hk m
  obtain ⟨T₁,H₁,h1⟩:= AuxPackage.plenty (σ:=σ) (C:=C) A K n k j q q' M hM h hp hr hh hz ht hD hA j₁ j₂ hs hn hk m
  have hv: Geo G L (fun t=> AuxStage.inter (T₀ t) 2 n):= (hT.joins (AuxStage.wages hT n)).joins (Geo.fixed _)
  obtain ⟨a,b,ha,hb,he,hq⟩:=power_core (n+j+1)
  let T₂ t:= AuxStage.label Φ a (T₀ t) 1 n j
  let T₃ t:= AuxCover.sideFee n k (f t) (w t)
  let T₄ t:= AuxStage.Points.fuse n j (T₁ t) (AuxStage.label Ψ b (T₀ t) 1 n j)
  obtain ⟨B,hB⟩:= response h.rate hD k (by omega)
  refine ⟨T₀,fun t=> T₂ t+T₃ t,T₁,T₄,hT,(AuxStage.label_geo Φ hT 1 a n j).joins (side_cost h hz n k),H₁,AuxStage.fusion_geo n j H₁ (AuxStage.label_geo Ψ hT 1 b n j),?_⟩
  filter_upwards [H,h1,hv.uniform (show 0<(1/2:ℝ) by norm_num),upper_guard hz.rate, hB] with t ht hw hv hx' hC c l S T p F B i ρ y V' β hL hK hf hM hI H' hρ Λ Hp hr₀ b' r hy E e hE hR
  have h:=ht _ _ S T p F B i ρ y V' β hL hK hf hM hI H' hρ Λ Hp hr₀ hy _ _ _ _ hE Probe.unit hR (one_render F ρ B β)
  have h' J W (hP:Probe W k j₂ q' r b' (v' t) (v' t)) (hp : Render F ρ B β J W q' r b' (g t)):= hw _ _ S T p F B i ρ y V' β hL hK hf hM hI H' hρ Λ Hp hr₀ hy _ _ _ _ hE hP hR hp
  have hu : β' t /2 ≤ β:= hL ▸ (show betaF G t S.patch.L / 2 ≤ β from hI.window.1)
  have hvβ:=hI.positive; have ht' := Fare.gS β hvβ|>.1
  obtain ⟨hg,hβ,Hx,hδ⟩:=hr₀.1
  have hxβ := hβ.le.trans hg.small
  have hr : r ≤ eaves G L t:= hx' β hu H'
  let X':= Uniform.Primary c G; have hZ : noneCo A T F ρ i E q n 0=fun _=>1:= by
    let Y:=Lapis.gram F T.up T.high ρ i
    have he' z : shot A F T ρ i z (0,0)=1 := by change Real.exp (Lantern.grace _ _ _ _ z (0,0))=1; rw [Lantern.zeroC,Real.exp_zero]
    exact intent_unit ((hC (Positions X') (Precision.Key F G) _ _ _ _ hg).lower le_rfl hr) hE hx he'
  have hZ': AuxStage.inter (T₀ t) 2 n*gStep β ≤ 1/2:= (mul_le_mul_of_nonneg_right (le_abs_self _) ht'.le).trans (hv β hu).le
  have hA' := bound_at A T F ρ i B β e E hA hvβ h hxβ hZ hZ'
  have hx : ‖y‖ < r := lt_of_le_of_lt (le_add_of_nonneg_right (show 0 ≤ furl G L t from Real.rpow_nonneg (hL ▸ (zero_le_one.trans hI.height.le)) _)) hy
  refine ⟨⟨mul_pos (Fare.sun F A _ hvβ hA) (Real.exp_pos _), hA'.1,hA'.2,h,log_P A T F ρ i B β e E hA hvβ h hxβ hZ hZ' he (AuxCover.channel A T F i ρ p hg hρ hf.large Hp β hvβ y h₀ hk.le H' hr hx)⟩,fun J W hW hw=> ⟨h' J W hW hw, mark_P A T F ρ i B β e J E W hA hvβ h (h' J W hW hw) hxβ hZ hZ' hq⟩⟩
end YM.RGComparison01.AuxSpell
