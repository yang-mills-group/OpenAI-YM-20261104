import YM.LocalLTE.Weft.Verg
/-! Estimate at Aura. auxiliary - genuine β coupling, use for charging higher mode truncations -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Uniform
variable {G : Gauge} {L : Side} {K : KernelChoices} {σ σ' τ τ' ℒ α ν d : ℝ} {g' : ℝ→ℝ} {q : Teller G}
-- Curl costs for arbitrary purchased D > 0. No large gauge condition.
variable (j n p:ℕ) (Q : ConnectedActivityE6.Target G q) (P: RG.Patch) (A: Before G σ τ P.J K ((n+1+2)+3)) (b b':Clip)
variable {κ V C:ℝ} (h: Reliable G κ V)
include h
set_option maxHeartbeats 200000 in
lemma circleQ (heN:2≤n) (hd:0<d)(hp: p ≤ n)(hX :Bolt G P.L g')(hσ: ν<0) (Y:ℝ) :
    ∃ W: ℝ→ℝ,Rate G P.L 0 W∧∀ᶠ t in atTop, ∀ (c f :Side)(S:StepData c f) (T:Tube G S)(F:Forest S.ratio) (ht:S.patch=P)(hK:S.kernel=K) (k:S.Choices) (B:BudgetPoint),Quilt T F (g' t) →T.high=b →T.low=b'→ T.up.Bounds b σ τ (ConnectedActivityE6.loopBill G P.L t) → T.down.Bounds b' σ' τ' (ConnectedActivityE6.loopBill G P.L t) →
     ∀ (ρ: Bid.Dir G c→ AxisChart G F)(γ:ℝ),(warm A ht hK).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ→ |γ| ≤ |Y| → ∀ β:ℝ, (betaF G t P.L)/2 ≤β →β ≤2*(betaF G t P.L) → B.threshold=Pressure.fiery G t P.L → Weft.Arp (2+(p+3)) j (W t) (fun s=> (Boulevard.stillA (Frame.placed Chi.canonical κ (song F T Q.table ρ (wick G P.L d t) γ k p s))) ∘ Boulevard.actual):=by
      by_cases he : 0<(A.tables b P).gap ∧ 0 < (A.tables b P).horizon∧0<(A.tables b P).initial
      swap
      · refine ⟨fun _=>0, (Rate.const 0),Eventually.of_forall fun t c f S T F ht hK k B H h H' hS hh ρ γ h'=>?_⟩; subst P K b; have hr := A.receipt F k hS H.large rfl rfl|>.1; exact False.elim (he ⟨hr.pos_m,(show A.Service F T.high T.up ρ from h').x_pos,hr.pos_r⟩)
      let J:= Classical.choice (BareRates.offered G σ' τ' (n+1+2)); let E := Classical.choice (Planned.JetPort.purchase Q.table Q.table_exists (((n+1+2)+3)+1))
      let Λ:=ConnectedActivityE6.loopBill G P.L; let H(t:ℝ):= pam (n+1+2) Q.table b P A (g' t) (g' t) E (Λ t); have hP:Rate G P.L 0 H:=(posts P.L P Q.table b A E hX).1
      obtain ⟨M',hM,hY⟩:= YM.LocalLTE.sapphire G P.L (n+1+2) H g' (by omega) hP hX hd (inv_pos.mpr (half_pos he.1));
      obtain ⟨X',hA,hU⟩:= Hall.composed G j h _ hσ hX.uses (χ:=Chi.canonical)
      let X₀:=(16*d)⁻¹; have hx₀:0<X₀:= by unfold X₀; positivity
      let k(t:ℝ):= kinBill (n+1+2) J b' (g' t) (H t); let a(t:ℝ):=cryo J b' (g' t) (H t) Y (Λ t)
      have ht k (b':ℝ→ℝ) (h:Rate G P.L 0 b'): Rate G P.L 0 (fun t=> tollS (g' t) k (b' t)):= by simpa only [zero_mul,zero_add] using! (hX.uses.pow k).mul h
      have hF:Rate G P.L 0 (fun t=> wood (n+1+2) (H t)):= lumpRate _ ((((Rate.const 1).add hP)).add ((Rate.const 1).add hP)) hP
      have hk₁ : Rate G P.L 0 k := (ht _ _ (Rate.const _)).add hF
      have hk₂: Rate G P.L 0 a:= (ht _ _ (((Rate.const _).add (ConnectedActivityE6.loopBill_rate G P.L)).mul_right _)).add (hF.add hP)
      let f t := pollens p j (M' t) (k t) (a t)
      have he' (n:ℕ)(f:ℝ→ℝ)(hf:Rate G P.L 0 f) : Rate G P.L 0 (fun t=> pollenT j n (f t)):= (hf.mul_right _ |>.mul_right _|>.mul_left _)
      have hve: Rate G P.L 0 f:=(((he' _ _ hM).add (he' _ _ hM)).add (he' _ _ hk₁)).add (he' _ _ hk₂)
      let W t:= (j.factorial:ℝ)*f t * (1+(1+X' t)*1)^j
      refine ⟨W,by simpa only [zero_mul, add_zero] using! ((hve.mul_left (j.factorial:ℝ)).mul (((Rate.const 1).add (((Rate.const 1).add hA).mul_right 1)).pow j)),?_⟩
      filter_upwards [hY,hU,Delay.shift_pos G P.L, Sienna.pencils (L:=P.L) (n:=n+1+2) X₀ (A.tables b P) Q.table Q.table_exists hx₀ he.2.1 he.2.2] with t hY hV hp₀ hv c f S T F h hK k' B h₁ hb hB hT hT' ρ γ hρ hCL hg β hβ hr hQ
      subst b b' P K; let u:= S.patch; specialize hv β hβ; have he : Pigment (n+1+2) (A.tables T.high S.patch) Q.table (wick G S.patch.L d t) (gStep β) X₀ (eaves G S.patch.L t) t B.threshold (furl G S.patch.L t):= by
         have ht: pence X₀=d := by unfold pence X₀; field_simp
         rw [ht] at hv; rwa [hQ]
      have hW₁ := courtyard Q F T k' A ρ B β E hρ h₁.large hT h₁.one h₁.overall h₁.lever h₁.finalP he
      have h₀:‖(0:Positions (Uniform.Primary c G))‖ <(A.tables T.high S.patch).horizon:= by rw [norm_zero]; exact (show A.Service F T.high T.up ρ from hρ).x_pos
      have ht:=hY _ _ _ _ _ _ (countsK F (g' t) h₁.overall) hW₁ (wakes F k' T.up T.high ρ σ τ _ A h₁.large hT hρ _ h₀).2.2.1 _ (mem_ball_self he.top)
      have hf := sticks F T Q.table ρ k' hW₁ hT' J h₁.one (countsP F _ h₁.overall) _ (mem_ball_self he.top); have hw:= hills F T Q.table ρ γ k' hW₁ hT' J h₁.one (countsP F _ h₁.overall) _ (mem_ball_self he.top)
      obtain ⟨hp',hu⟩:= hV c h₁.step; have hv : 0 ≤ k t:= (norm_nonneg _).trans (hf.2 1 (by omega) (by norm_num));
      have hh: cryo J T.low (g' t) (H t) γ (Λ t) ≤ a t:= by
         have hk' : 0 ≤ BareRates.bill J T.low := (bareSocket c J hT' (x:=0) (mem_ball_self zero_lt_one) 0).2.2.2.1.le
         unfold a cryo tollS; gcongr; exact pow_nonneg (zero_le_one.trans h₁.one) _ -- edit
      have ha' := (norm_nonneg _).trans ((hw.2 1 (by omega) (by norm_num)).trans hh)
      have hF : fderiv ℝ (cedar F T ρ k') 0 =0:= (unshine F T Q.table ρ k' hW₁ hT' J h₁.one (countsP F _ h₁.overall) _ (mem_ball_self he.top) hCL (by omega)).2
      have hW:= Hall.rays F T Q.table ρ (wick G S.patch.L d t) γ k' j (show p+3≤n+1+2 by omega) ht.nonneg hv ha' ht hf.1 hF hf.2 hw.1 (fun i hi h=> (hw.2 i hi h).trans hh)
      exact Hall.framedW (by assumption) hW (fun s _=> smoothSong F T _ ρ _ γ k' p s j) (show 0 < cone ν _ from Real.rpow_pos_of_pos hp₀ _) hu
end YM.LocalLTE.FrameBox.Hall
