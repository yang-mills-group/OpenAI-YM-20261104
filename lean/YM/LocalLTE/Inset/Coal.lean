import YM.LocalLTE.Inset.Cobalt
/-! Aux pure generation endpoint at post-L. This is the comparison
kernel for extracting tiles. Doesn't assert identical-to-physical or
cut/coupling-independent periodization. In later ports use both core S2 birth
and bills at actual coupling times leftover, not the points alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Inset
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {τ τ' C C' l W w : ℝ} {K : KernelChoices} {T' : Teller G} {J : ℕ}
variable (P : Patch) (Q : ConnectedActivityE6.Target G T') (o : Target.Order G W)
    (n p: ℕ)
local notation "kG" => (n+1+2)
local notation "L" => P.L
variable (M : Push.Uniform.Before G τ C P.J K ((n+1+2)+3)) (R : FiberFee Q.table (((n+1+2)+3)+1))
    (Z : BareRates.pre G τ' C' (n+1+2)) (Z' : BareRates.pre G τ' C' ((n+1+2)+3))
variable {g h : ℝ→ℝ} {Θ γ : ℝ} (b b' : Clip) (hk : p≤ n) (hv : Bolt G P.L g) (hr : Rate G P.L 0 h) (hW: -(1/2:ℝ) < w) (hw: w < Sienna.vow) (hη : 1+w*(p+3:ℝ)<l)
include hk hv hr Z Z' R hW hw hη
-- post-L step comparison; deliberately all θ,w and supported AUX periods
-- within the geometry (Quilt). No-to-curve and no previous Final needed.
set_option maxHeartbeats 360000 in
theorem full (V a : ℝ) (hA : 0<a) :
    ∃ d:ℝ,0 < d ∧ ∀ᶠ t in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (hp:S.patch=P) (ht:S.kernel=K) (k:S.Choices) (B B' : BudgetPoint), Quilt T F (g t) → T.high=b → T.low=b' → T.up.Bounds b τ C (ConnectedActivityE6.loopBill G L t) → T.down.Bounds b' τ' C' (h t) →
    ∀ (ρ:Bid.Dir G c→ AxisChart G F) (α : ℝ), (Sienna.warm M hp ht).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ → |α|≤ |V| → B'.threshold=Pressure.temp t →
    ∀ β c' : ℝ,Cash W t a L Q o c' T (Pane.virgin T B β) → ∀ X:Coat T F, X.x=t → X.width=o.K → X.manifest → flags (Pressure.temp t) X.V=∅ →
      let y:=betaF G t L; let u:=cone w y; let D:= wick G L d t
      ∀ x:Positions (Uniform.Primary c G), X.V=represent (tint G _ x) → ‖x‖ < u →
        0 < tramp T B β x ∧ Brush n (y^l) u⁻¹ (fun x=> harmony T B β α x - (Real.log (solar F Q.table β)+song F T Q.table ρ D α k p (gStep β) x)) x := by
  by_cases h₀ : 0 < (M.tables b P).gap
  swap
  · refine ⟨1,zero_lt_one,Eventually.of_forall fun t c f S T F hp ht k B B' hq ha hB h𝒦 => False.elim ?_⟩
    subst K; subst P; subst b
    exact h₀ (M.receipt F k h𝒦 hq.large rfl rfl).1.pos_m
  obtain ⟨d,hd,hD⟩ := Sienna.reaches Q o P M b' b g hv R Z' a hA (by omega)
  let L':=P.L
  have hP:Rate G L' 0 (fun t=> pam (kG) Q.table b P M (g t) (g t) R (ConnectedActivityE6.loopBill G L' t)):= (posts L' P Q.table b M R hv).1
  let e:= 1+w*(p+3:ℝ)
  obtain ⟨b₁,hX,hY⟩:=languid (C:=C) (σ:=τ) (K:=K) Q.table Q.table_exists (M.tables b P) n d e hP hv hd h₀
  obtain ⟨b₂,hF,hU⟩:=sapphire G L' kG _ _ (by omega) hP hv hd (inv_pos.mpr (half_pos h₀))
  refine ⟨d,hd,?_⟩
  filter_upwards [hD,hY,hU,clearance (G:=G) («L»:=P.L) hW hw,currency' hW (kG) p h _ _ _ hr hP hv.uses hF hη Z b' V] with t hD hY hU hB hy c f S T F hp ht k B B' hQ hk' hT hz he ρ α hρ ha hα h' β c₀ A X hX' hF' he' hV
  intro y u D x hW' hL
  subst K; subst P; subst b; subst b'
  have hβ := A.laws.intake; have hG:0<β:=hβ.positive
  obtain ⟨h₁',h₂,h₃,h₄⟩:= hB
  have hp₁: ‖x‖+2*furl G L' t< eaves G L' t:= (add_lt_add_left hL _).trans h₂
  have hr' := hD c f S T F rfl rfl hQ rfl rfl hz _ he ρ hρ ha k X hX' hF' he' B B' _ _ A h' hV x hW' (hL.trans_le h₃)
  obtain ⟨hp',hL',-⟩:= hY c f S T F M B β ρ k T' x hQ rfl rfl rfl hp₁ hβ hz hρ hr'
  obtain ⟨hg,_,HU,hV'⟩:= hr'
  have h₀ : ‖(0:Positions (Uniform.Primary c G))‖ < eaves G L' t:= by rw [norm_zero]; exact hg.pos
  have hq := hU _ _ (Lapis.table F k T.up T.high) (mist F Q.table T.up) (Lapis.orbit F ρ) (gram F T.up T.high ρ k) (countsK F (g t) hQ.overall) hg (wakes F k T.up T.high ρ τ C _ M hQ.large hz hρ _ (h₀.trans_le HU)).2.2.1
  have hh₁ := countsP F (g t) hQ.overall
  have hh' := refrain F T Q.table ρ D β α k p hg he Z hQ.one hh₁ (show n ≤ n+1+2 by omega) (by omega) h₁' h₃ hq hG (h₄ β hβ.window.1) x (mem_ball_zero_iff.mpr hL) hL'
  have hK : 0 ≤ BareRates.bill Z T.low:= (bareSocket c Z he (x:=0) (mem_ball_self zero_lt_one) 0).2.2.2.1.le
  have hu := (sticks F T Q.table ρ k hg he Z hQ.one hh₁ _ (mem_ball_zero_iff.mpr h₀)).2 (n+1+2) (le_refl _) (by omega)
  refine ⟨hp', hh'.climb (hy _ _ hα hβ.window.2 (le_trans (norm_nonneg _) hu) (zero_le_one.trans hQ.one) hK) le_rfl⟩
end YM.LocalLTE.Inset
