import YM.Juniper.LocalAtlas.Rent
/-!
 # A real all-order *Aux miniature torus* one-step perturbative confirmation

 Log primitive of the Eager/Rain launch estimator, crossing sizes specified in
 Quilt. Keep the same actual `Pane.virgin` (i.e. composing on the interaction
 with all of this scheduled geometry's PTO path terms & loop but E and K
 activities blank; includes its masks, not unmasked restart). This is itself
 the auxiliary term in the comparison of real nonlinear E step (see Boulevard
 clamping) NOT the physical History.unmarked output law. `coverLog` from full
 formal stationary cumulant prescription. All errors BRUSH on the particular
 y gauge, normalized by the `(eaves) ~ Z ^ -(7/16)` not changing gauge.
 Remainder includes ALL hard regions, from the previous analytic `languid`
 Comparison of this UNDEFORMED (not new real regulator) kernel on that space.
 Uniform in geometry including P-volume growth gates, before clamping/resizing
 on actual history. The Gaussian normalization queries are those actually open
 for the supplied cash in THIS coast. Factored universal constants. No hidden
 assumptions of comparing to LPT pose or unconditioning. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
section input
variable {c f:Side}{S: StepData c f} (F:Forest S.ratio)(T:Tube G S)(A:ChartRatio G)(k:S.Choices)
    (ρ: Bid.Dir G c→AxisChart G F)
local notation "V"=> Positions (Uniform.Primary c G)

def kin (n : ℕ) := through n (oneEra (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k))
def grant (n:ℕ) := cleanLetter (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) n

-- base analytic fare retains β^{-1} and explicitly verified Φ_graph not Taylor
-- in y for this interface. Need a Taylor-(β*jets(V)) interface next. Elemental p=2 canonical reclosure costs need separate estimate.
def mean (n:ℕ) (β:ℝ) (x:V) := Real.log (solar F A β) - (coverLog F T A k ρ β x) + grant F T A k ρ n (gStep β,x)

-- uncut Gaussian Tag at fixed anchor; pressure conventions proof-of-input
lemma grant_port (n:ℕ): Work.G05.blockTaylor n (Real.log ∘ kin F T A k ρ n)=grant F T A k ρ n := rfl
end input

private lemma arc_est {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
    (f:ℝ×E→ℝ){n:ℕ}{q r:ℝ}{x:E}{u:ℝ}(hp:Brush n q r f (u,x)):
    Brush n q r (f ∘ Lantern.arc u) x:=by
    let P:= hook E; have hx(i:E): arc u i=(u,0)+P i:=by simp [P]
    rw [show f ∘ arc u=(fun i=> f ((u,0)+P i)) from funext fun i=> congr_arg f (hx i)]; exact skim _ ((hx x) ▸ hp) n_hook

variable {σ σ' C C' W W' : ℝ} {K : KernelChoices} {T' : Teller G}
-- p and q levels set before f and mini price calls; want no `rank` pre.
variable (P : Patch) (Q : ConnectedActivityE6.Target G T') (o : Target.Order G W)
    (n j : ℕ) (hj:n ≤ j) -- derivative order in x, permit high internally
    (M : Push.Uniform.Before G σ C P.J K ((j+1+2)+3)) (R : FiberFee Q.table (((j+1+2)+3)+1))
    (T : BareRates.pre G σ' C' ((j+1+2)+3))
local notation "L" => P.L
variable {Z:ℝ→ℝ} {Θ γ : ℝ} (b b' : Clip)(hk : 2 ≤ j)(hv:Bolt G P.L Z)
local notation "A" => eaves G L
local notation "C₀"=> M.tables b P
local notation "O"=> (fun t=> pam (j+1+2) Q.table b P M (Z t) (Z t) R (ConnectedActivityE6.loopBill G L t))

include T hv R M hk hj
set_option maxHeartbeats 200000 in
lemma quote (a x : ℝ) (ha:0<a)(hp:leaf n < x) :
    ∃ Y U:ℝ→ℝ, Rate G L 0 Y ∧ Rate G L 0 U ∧ ∀ᶠ t in atTop,
      let z:=betaF G t L; let u:=eaves G L t; let o':= furl G L t
      ∀ (c f : Side) (S:StepData c f) (T:Tube G S) (F:Forest S.ratio) (H:S.patch=P) (tK:S.kernel=K)
         (k:S.Choices) (B B':BudgetPoint), B'.threshold=Pressure.temp t → Quilt T F (Z t) → T.high=b → T.low=b' → T.up.Bounds b σ C (ConnectedActivityE6.loopBill G L t) → T.down.Bounds b' σ' C' (ConnectedActivityE6.loopBill G L t) →
       ∀ (ρ : Bid.Dir G c→AxisChart G F),(Sienna.warm M H tK).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ →
       ∀ β p : ℝ,Cash W t a L Q o p T (Pane.virgin T B β) → ∀ X:Coat T F, X.x=t → X.width=o.K → X.manifest → flags (Pressure.temp t) X.V=∅ → ∀ y : Positions (Uniform.Primary c G), X.V=represent (tint G _ y) → ‖y‖+2*o' < u→
        0 < tramp T B β y ∧
        Brush j (2*z^x) u⁻¹ (pures T B β - mean F T Q.table k ρ n β) y ∧
         ∀ w:ℝ× Positions (Uniform.Primary c G), ‖w‖<u →
          Brush (j+1+2) (Y t) 1 (kin F T Q.table k ρ n) w ∧
          Brush (j+1+2) (U t) 1 (Real.log ∘ kin F T Q.table k ρ n) w:= by
   by_cases h₀ : 0<(C₀).gap; swap
   · refine ⟨fun _=>0,fun _=>0,Rate.const 0,Rate.const 0, Eventually.of_forall fun t c f S T F hp ht k B B' he hQ hA hc hx=> False.elim ?_⟩ -- lets erase auto
     subst K; subst P; subst b
     exact h₀ (M.receipt F k hx hQ.large rfl rfl).1.pos_m
   obtain ⟨d,hd,hD⟩:= Sienna.reaches Q o P M b' b Z hv R T a ha (by omega)
   have hQ := (Sienna.posts P.L P Q.table b M R hv).1
   obtain ⟨X,hX,hY⟩:= Token.languid (C:=C) (σ:=σ) (K:=K) Q.table Q.table_exists (C₀) j d x hQ hv hd h₀
   let v:= (M.tables b P).gap/2; have he:=inv_pos.mpr (half_pos h₀)
   obtain ⟨Y,U,hY',hU',hf⟩:= rate_log d v⁻¹ n (j+1+2) hv.uses hQ hd hv he (by omega) x hp
   refine ⟨Y,U,hY',hU',?_⟩
   filter_upwards [hf,hY,hD, Delay.shift_pos G L] with t h hΞ hΩ ht z u d₀ c f S T F H tK k B B' hg hKQ hK hk' hp' hs ρ hV hXK β p X Xp hT hv' hc hΓ y hy hDy
   subst K; subst P; subst b; subst b'
   have hS : M.Service F T.high T.up ρ:=hV
   have hβ:=X.laws.intake
   have hz:0<d₀:= Real.rpow_pos_of_pos ht _
   have ht:‖y‖<u:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg zero_le_two hz.le)) hDy
   have hw:= hΩ c f S T F rfl rfl hKQ rfl rfl hp' _ hs ρ hV hXK k Xp hT hv' hc B B' p β X hg hΓ y hy ht
   obtain ⟨hk,hL,Hx⟩ := hΞ c f S T F M B β ρ k T' y hKQ rfl rfl rfl hDy hβ hp' hV hw
   have ht': ‖(0:Positions (Uniform.Primary c G))‖< u:= by rw [norm_zero]; exact hw.1.pos
   have he':= Lapis.wakes F k T.up T.high ρ σ C (ConnectedActivityE6.loopBill G S.patch.L t) M hKQ.large hp' hS 0 (ht'.trans_le hw.2.2.1)
   have hp:= h _ _ _ _ _ _ (countsK F (Z t) hKQ.overall) hw.1 he'.2.2.1; have hz:‖gStep β‖<u:= by rw [Real.norm_of_nonneg (Fare.gS β hβ.positive|>.1.le)]; exact hw.2.1
   refine ⟨hk, ?_, fun w hw=> ⟨(hp w hw).1,(hp w hw).2.1⟩⟩
   let d':=wick G S.patch.L d t
   let v := grant F T Q.table k ρ n; let e:= lack F T Q.table B ρ β k d'; let f₀:= Token.pigment F T Q.table ρ β k d'
   let b:= gStep β; let K(x):= v (b,x); have hW:= arc_est _ ((hp (b,y) (max_lt hz ht)).2.2.smaller (by omega : j ≤ j+1+2))
   have hp:Brush j (z^x) u⁻¹ (f₀-K) y:= hW; have hU:1 ≤ u⁻¹:= (one_le_inv₀ hw.1.pos).2 hw.1.small
   rw [two_mul]; refine ((hL.climb le_rfl hU).gathering hp).shimmy ?_; refine Eventually.of_forall fun w=>?_ ; unfold mean lack; dsimp only [Pi.sub_apply,K,v,b,d',f₀]; ring -- remove token
end YM.Juniper.LocalAtlas
