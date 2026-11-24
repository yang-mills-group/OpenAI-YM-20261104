import YM.RGComparison01.AuxQueue

/-! # True exceptional collar on Aux. At all derivative orders requested in meters.
 Never take a moving-boundary derivative here. Proof via gross bounds on the TRUE normalized
 function and smooth-core approximant (not a differentiated comparison of kernels), and
 value estimates throughout a microscopically smaller open neighborhood. Threshold can
 be attained with equality; no mask-slack assumed at x.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxWeigh
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {C Z a s J v C₀ σ τ d : ℝ} (A: ChartRatio G) {L : Side} {K: KernelChoices} {Q : Patch} {n j : ℕ}
variable {u f g T₀ B : ℝ→ℝ}
local notation "z" => (fun t=> betaF G t L)
local notation "y" => (fun t=> 2*z t)
lemma cut_geo (h : Rate G L 0 B) (p : Rate G L 0 f) (hg : Rate G L s u) (he : Rate G L 0 g) (j:ℕ) (E : ℝ) : Rate G L (s+j) (fun t=> cutFee j (u t) (f t) (g t) (B t) (y t) E) := by
  have hf:=climbF (oatr j h) zero_le_one j E
  unfold cutFee; simpa only [add_zero,one_mul] using! ((((hg.mul p).mul he).mul hf).mul_right (2^j:ℝ))
lemma oats_monotone {v b c d l u u' : ℝ} {j:ℕ} (hp: v ≤ b) (he : 0≤v) (ht : 0 ≤ d) (hm : 0≤ l)
    (hu : 0 ≤ J) (hh : u ≤ u') (hv:0 ≤ u) (hf : 0≤ c) : cutFee j v d c l u J ≤ cutFee j b d c l u' J:= by unfold cutFee oat Lantern.clump; dsimp only; have h := he.trans hp; gcongr

-- gross bound in small collar on rescale
lemma collar (hB:Bolt G L B) (hv:Rate G L 0 T₀) (hf: Rate G L 0 f) (HH : LocalRatio A) (M : ChartPrices) (hM : 0 < M.gap) (K: KernelChoices) (d : ℝ)
    (k j:ℕ) (hp : j≤k) (hk : 1 ≤ k) : ∃ v' : ℝ,
    ∀ᶠ t in atTop, let u:= eaves G L t
       ∀ (c g:Side) (S: StepData c g) (T:Tube G S) (F: Forest S.ratio) (p: Before G σ C S.patch.J S.kernel (k+3)) (bp:BudgetPoint) (V:Teller G) (x: Positions (Uniform.Primary c G)) (β:ℝ) (ρ:Bid.Dir G c→AxisChart G F) (i:S.Choices),
       S.patch.L = L → S.kernel = K → Quilt T F (B t) → p.tables T.high S.patch=M → Intake V T t (Pane.virgin T bp β) → Sienna.receiptS T p bp F ρ i L A d (f t) t β x →
       ∀ J:Config G g→ℝ,GaugeInvariant J→RG.Envelope J→0 ≤ T₀ t→ (∀ k:Config G g,flags bp.threshold k=∅→|J k|≤T₀ t) → ∀ zY∈closedBall x (furl G L t), ‖zY‖<u→ Brush j ((betaF G t L)^v') 1 (rescale F T A ρ bp i β J) zY := by
  obtain ⟨c,hU⟩:= paint_supply G j; obtain ⟨D,hD,hQ⟩:=Brush.compact (f:=Real.exp) (k:=k) (s:=Icc (-1:ℝ) 1) isCompact_Icc fun _ _=> Real.contDiff_exp.contDiffAt
  let V:=1*(j:ℝ)+j+1
  let r t:= B t*(Fintype.card Axis:ℝ); have hr: Rate G L 0 r:= hB.uses.mul_right _
  let P t:= prime G K j c D (y t) (r t); have hp': Rate G L (1*(j:ℝ)) P:= primeR _ K hr
  let K' t:= Lantern.fee k (f t) (wick G L d t); let R' t:= clump k (K' t) D
  have hb:= Lantern.fareRate k hf (Sienna.gen G L d); have hF: Rate G L 0 (fun t=>R' t+1) := (Lantern.lumpRate k hb (Rate.const _)).add (Rate.const 1)
  have he' := (cut_geo hf hv hp' hF j D) V (by unfold V; linarith)
  have hp'' := ((hb.mul (Sienna.edge G L))).below (by linarith only [Sienna.vow_ok]) _ zero_lt_one
  refine ⟨V,?_⟩; filter_upwards [he',hp''] with t ht hQ' u c' g S T F p bp R x β ρ i hL hK hS hm hI hP J he hh hT hz y' hi' hW'
  let a:=(r t); have ha : 0 ≤ a:= by unfold a r; have h:=hS.one; positivity
  have hR : β ≤ 2*betaF G t L:= hL ▸ (show β≤2*betaF G t S.patch.L from hI.window.2); have hhβ : 0<β:= hI.positive
  obtain ⟨hW,hβ,hY,hZ⟩:=hP
  have hw : (Fintype.card (Bond c'):ℝ) ≤ r t:= by rw [Fintype.card_prod]; push_cast; exact mul_le_mul_of_nonneg_right hS.primary (Nat.cast_nonneg _)
  have hν := primeN (G:=G) K (n:=j) hhβ hR hD.le hU.1.le ha
  rw [← hK] at hν
  have he' := hZ y' hW' (mem_closedBall_iff_norm.mp hi')
  let D₀:= wick G L d t
  let ε:= Real.exp (-((p.tables T.high S.patch).gap*D₀^2/4)/2)
  have hE: ε ≤ 1:= by
                         unfold ε; rw [hm]; exact Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hM.le (sq_nonneg D₀)])
  let M' := assay F T A ρ i β y'
  have hp : 0<M':= mul_pos (sun _ _ _ hhβ HH) (Real.exp_pos _)
  have hδ:= (Fare.gS β hhβ).1
  have hh' := burs _ hW (x:=(gStep β,y')) hW' (show ‖gStep β‖<u by rwa [Real.norm_of_nonneg hδ.le]) hk (by rw [max_self]; exact (le_abs_self _).trans hQ') hQ hD.le
  have hx : 0 ≤ R' t := hh'.1.nonneg
  let s':=ratify (Lapis.table F i T.up T.high) (mist F A T.up) (orbit F ρ) (Lapis.gram F T.up T.high ρ i) D₀ (gStep β,y')
  have ha : tramp T bp β y' ≤ M'*(R' t + 1):= by
    have hh : s' ≤ R' t:= (le_abs_self _).trans hh'.1.bound; rw [mul_add]; linarith only [show tramp T bp β y'- M'*s'≤M'*ε from he'.2,mul_le_mul_of_nonneg_left hh hp.le,mul_le_mul_of_nonneg_left hE hp.le]
  have hhg:= normalized F T i A ρ bp J β hI he hh hz hT hU ((hQ 0 (by simp)).smaller ‹j ≤ k›) hν.1 hw HH hW (by assumption) y' hW' ha
  apply hhg.climb _ le_rfl
  have hc :0 ≤ f t:= (hW.curve _ hW').nonneg
  have hp': prime G S.kernel j c D β (r t) ≤ P t:= by unfold P; rw [← hK]; exact hν.2
  exact (oats_monotone hp' hν.1 hT hc hD.le hR hhβ.le (by linarith : 0≤R' t+1)).trans ((le_abs_self _).trans ht)
end YM.RGComparison01.AuxWeigh
