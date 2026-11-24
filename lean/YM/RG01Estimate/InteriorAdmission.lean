import YM.RG01Estimate.InteriorCore
/-! # Expose the same Frame certificate for Weighted Logs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Courtyard
open PhysicalNext.Repeat PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern PhysicalNext.Repeat.Fare Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {σ C σ' C' Λ' W x μ v : ℝ} {q : Teller G} {K : KernelChoices} {f c : Side} {n:ℕ}
variable (Q : ConnectedActivityE6.Target G q) (o : Target.Order G W)
    (P : Patch) (A : Before G σ C P.J K (n+3)) (p'p p : Clip) (w : ℝ→ℝ) (hk : Bolt G P.L w) (E : FiberFee Q.table ((n+3)+1)) (J : BareRates.pre G σ' C' (n+3)) (e : ℝ) (he : 0<e) (hn : 5 ≤ n+3)
local notation "V₀" => A.tables p P
include J he hn hk
set_option maxHeartbeats 400000 in
/-- Variant of `Sienna.reaches` exposing numerical Pigment and mask receipts BEFORE
 discarding them. Require the same region continuity and sales; these then also price weights. -/
lemma pass : ∃ d:ℝ, 0<d ∧ ∀ᶠ t in atTop, ∀ (c f: Side) (S:StepData c f) (T : Tube G S) (F:Forest S.ratio) (h:S.patch=P) (ht:S.kernel=K), Quilt T F (w t) → T.high=p → T.low=p'p → T.up.Bounds p σ C (ConnectedActivityE6.loopBill G P.L t) → ∀ Λ', T.down.Bounds p'p σ' C' Λ' →
    ∀ ρ: Bid.Dir G c→ AxisChart G F,(warm A h ht).Service F T.high T.up ρ→ ClassicalMatch F T.high T.low T.up T.down ρ →
    ∀ k:S.Choices, ∀ (X : Coat T F), X.x=t → X.width=o.K → X.manifest → ∀ (B B' : BudgetPoint) (m β:ℝ), Cash W t e P.L Q o m T (Pane.virgin T B β)→ B'.threshold=Pressure.temp t →
    flags (Pressure.temp t) X.V=∅ → ∀ x: Positions (Uniform.Primary c G), X.V=represent (tint G _ x) → ‖x‖ < eaves G P.L t → let V:= (warm A h ht).tables T.high S.patch
       let U:= eaves G P.L t; let D:= wick G P.L d t
       0 < V.gap ∧ U≤ V.horizon ∧ ∀ z:Positions (Uniform.Primary c G), ‖z‖< U → ‖z-x‖ ≤ furl G P.L t → Interior F T Q.table k ρ B β D z U
        (pam n Q.table p P A (w t) (w t) E (ConnectedActivityE6.loopBill G P.L t)) (Real.exp (-(V.gap*D^2/4)/2)) n := by
  by_cases h' : 0 < (V₀).gap ∧ 0 < (V₀).horizon ∧ 0 < (V₀).initial ∧ 0 < (V₀).safety
  swap
  · refine ⟨1,zero_lt_one,Eventually.of_forall ?_⟩
    intro t c f S T F h hp hq hk hK hr m' hm' ρ H ha k; subst K; subst P; subst p
    have hS := A.receipt F k hr hq.large rfl rfl|>.1; exact False.elim (h' ⟨hS.pos_m,(show A.Service F T.high T.up ρ from H).x_pos,hS.pos_r,hS.reserveH_pos⟩)
  obtain ⟨l,hl,hL⟩:= Fare.wall G P K (V₀).safety h'.2.2.2; obtain ⟨U,hU,Hu⟩:= Fare.faceM G
  let V:= V₀; let Z:= P.L; let D':= pence U; have hd: 0 < D':= inv_pos.mpr (by positivity)
  have he' := compass P.L Q.table Q.table_exists P p A E hk D' o.ample h'.1 hd (stocksK G n σ' C' J p'p V) C'
  refine ⟨D',hd,?_⟩; filter_upwards [he',pencils (G:=G) (L:=P.L) (n:=n) U V Q.table Q.table_exists hU h'.2.1 h'.2.2.1,
    pressures Z P p A hk D' (K.penalty*l^2/2) (by have h:= K.penalty_pos; positivity), Rate.flame (G:=G) (L:=Z) |>.below (by norm_num) _ hl, Pane.wealthy Q Z he w hk.uses] with t hx hY hh hg hM c f S T F h ht hQ hv hV H h₀ H₀ ρ Hρ hθ k X hX hw hm B B' m β R hT hF x hD hu
  subst K; subst P; subst p; subst p'p; subst t
  have hv : A.Service F T.high T.up ρ:= Hρ
  let t:=X.x; let D:= wick G Z D' t; let w':=w t
  let Y:=eaves G Z t; have hR:=R.laws.intake; have hB : B.threshold=Pressure.fiery G t S.patch.L:= hR.received.temp; have hvx:0<β:=hR.positive
  obtain ⟨hp,hvβ⟩:=hR.window
  have hP:Pigment n V Q.table D (gStep β) U Y t B.threshold (furl G Z t):= by rw [hB]; exact hY β hp
  
  have hH i (V: Config G c) (Z:F.Slice G):= hL S rfl rfl hQ.large F V Z i
  have hf : 1 ≤ w':=hQ.one; have hW := hh β hvx hp hQ.one; have hb':B.threshold≤l:= hB ▸ (le_abs_self _).trans hg
  let eB := let a:= stocksK G n σ' C' J T.low (A.tables T.high S.patch);β*(w'*a*‖x‖^5+w'*(C'*B'.threshold^3+C'*B'.threshold^4))+
      (pam n Q.table T.high S.patch A w' w' E (ConnectedActivityE6.loopBill G Z t)+tapir (A.tables T.high S.patch) w'+w'*o.ample/2)
  have hc:= hx eB β hQ.one hvx hvβ _ (Nat.cast_nonneg _) hQ.lever B hB B' (hT ▸ R.laws.data.room.temperatures) ‖x‖ (norm_nonneg _) hu.le rfl
  have hA:= cooler Q o F T k A ρ B B' β E J hv hQ.large H H₀ hQ.one hQ.overall hQ.lever hQ.finalP hP hl hvx hb' hH hW X R rfl hw hm hT hQ.primary hQ.sizes (hT ▸ hF) (by assumption) hu hθ hn (hM _ hQ.step) hc.1
  have hs : (1+Before.Service.trailCost V (n+3))*Y+gStep β*D ≤ 1:= le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hP.lease.le hP.positive)) hP.one.le
  have hh:= slack F T k A ρ hv hQ.large H hP.horizon B β (x:=x) (D:=D) hu hvx hs hA hU (Hu F) hP.sermon
  refine ⟨h'.1,hP.horizon,?_⟩
  intro y hy hr
  have hP' := courtyard Q F T k A ρ B β E hv hQ.large H hQ.one hQ.overall hQ.lever hQ.finalP hP
  have hc' : (1+Before.Service.trailCost V (n+3))*Y+gStep β*D < V.initial:= lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_of_nonneg_right hP.lease.le hP.positive)) hP.initial
  have hY': Uniform.shade G*(Before.Service.trailCost V (n+3)*Y+ gStep β * D) < Q.table.radius := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hP.lease.le hP.positive)) (Uniform.shade_pos G).le) (hP.count.trans_lt (half_lt_self Q.table_exists.patch))
  have hK:=hh y hy hr
  exact ⟨hP', hQ.large.1, ⟨hvx,hP.lease⟩,hy,Fare.gamma F T k A ρ hv hQ.large H hP.horizon hP.booth hy hc',Q.table_exists,mouthF F T k A ρ hv hQ.large H hP.horizon Q.table hY' hP.booth hy,hK, rule_it Q F T k A ρ B β E hv hQ.large H hQ.one hQ.overall hQ.lever hQ.finalP hP hl hvx hb' hH hW hR hy hK hc.2⟩
end YM.RG01Estimate.Courtyard
