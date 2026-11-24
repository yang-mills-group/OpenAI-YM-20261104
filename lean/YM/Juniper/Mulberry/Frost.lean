import YM.Juniper.Mulberry.Viscera
/-!
 # Fare estimate through n, MIXED full negative-log preprojection. Reuses pure
 payment. Normalize scalar+loop weights even at Pad; Phi requires full values
 with THEIR hard tags; here the permits only used on Sunny. No graft onto
 unaligned templates. Next couple into Calendar.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Analysis Work.G05 LocalAtlas
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {T' : Teller G} {σ C a:ℝ} {N n j:ℕ} {L:Side} {c f : Side} {S:StepData c f}
section draft
variable (P: Tube G S) (F:Forest S.ratio) (O:ChartRatio G) (k:S.Choices) (ρ: Bid.Dir G c→AxisChart G F) (B:BudgetPoint)
      (α β:ℝ)(p:Activities G f)
local notation "X"=> Positions (Uniform.Primary c G)
local notation "Z"=> LocalAtlas.arctic
local notation "W"=> (fun x:X=> represent (tint G _ x))
local notation "U"=> LocalAtlas.grant
local notation "Ω"=> coverLog F P O k ρ β
local notation "Ψ"=> solar F O β
local notation "f!"=> (fleece P B β p)
local notation "L₃"=> mouthful F P O k ρ p n β
def aura (x:X): ℝ := Real.log (S.push β (fleece P B β p).eval (W x))+β* mainTerm P.low P.down (W x) + Precision.loop P.down (W x)+α*Precision.secondTerm P.low P.down (W x)
def quasar (n:ℕ)(β:ℝ)(x:X):ℝ := LocalAtlas.arctic F P O k ρ n α β x-LocalAtlas.grant F P O k ρ n (gStep β,x)+Mulberry.mouthful F P O k ρ p n β x
-- tetra geometry interpretation: pure predecessor estimated *plus* all stencils expressed in E grade but input β. Full condition ∀ stamped critical so no mortgage choices. cp8. Decouple log root for first frame. Input Gram target F not yet supplied.
lemma mixed (x:X) : aura P B α β p x-quasar P F O k ρ α p n β x= (veilF P B β p x - (Real.log (solar F O β) - Ω x + L₃ x)) - (Token.pures P B β x - LocalAtlas.mean F P O k ρ n β x) + (Token.harmony P B β α x- arctic F P O k ρ n α β x):= by
    unfold Mulberry.aura Mulberry.quasar LocalAtlas.mean; change _=_ - (Real.log _ - _) + ((Real.log _+_+(_+_))-_); unfold veilF; change _= (Real.log (S.push β (fleece P B β p).eval (W x))-_) - (Real.log (S.push β (Pane.virgin P B β).eval (W x))-_) + ((Real.log (S.push β (Pane.virgin P B β).eval (W x))+_+(_+_))-_)
    ring
end draft
section aura
variable {σ' W C':ℝ} {K: KernelChoices}
   {j n:ℕ} (P : Patch) (Q: ConnectedActivityE6.Target G T')(o : Target.Order G W)
   (hn:n<j)(M : Push.Uniform.Before G σ C P.J K ((j+1+2)+3))(R:FiberFee Q.table (((j+1+2)+3)+1)) (J:BareRates.pre G σ' C' (j+1+2))(J': BareRates.pre G σ' C' (j+1+2+3))
   {p w:ℝ→ℝ}(b b':Clip)(hk : 2≤j) (hw : Bolt G P.L p)(hp : Rate G P.L 0 w)
include hk M R J J' hw hp hn
local notation "L"=> P.L
local notation "k"=> j+1+2
local notation "Z₁"=> (j+1+2+3)
local notation "Ht"=> (fun x=> Delay.fineMonitor G L x ^ (2:ℕ))
local notation "V"=> (M.tables b P)
omit hk M R J J' hw hp hn in
lemma tilt_smaller {ι E:Type}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E] {u t d e f:ℝ} {h:Poll.Body ι→(ℝ×E)→ℝ} {k':ℕ} (p:Tilt k' t u d e h)(he:f≤u): Tilt k' t f d e h:= ⟨fun _x hx=> (p.mass _ hx).mono (closedBall_subset_closedBall he),p.wise,p.flat,fun i x hx hi=> p.atmospheric i x hx (hi.trans he)⟩ -- omit
set_option maxHeartbeats 600000 in
lemma autumn (l a c :ℝ)(hl:0<l)(hz:drive n < a): ∀ᶠ t:ℝ in atTop,
      let x:=betaF G t L; let u:=eaves G L t; let r:=furl G L t; let d:= Mulberry.shadow G L t;
      ∀ (c' f : Side) (S:StepData c' f)(T:Tube G S)(F:Forest S.ratio) (h:S.patch=P)(hS:S.kernel=K) (v:S.Choices)(B B':BudgetPoint), B'.threshold=Pressure.temp t → Quilt T F (p t) → T.high=b → T.low=b' → T.up.Bounds b σ C (ConnectedActivityE6.loopBill G L t) → T.down.Bounds b' σ' C' (ConnectedActivityE6.loopBill G L t)→
         ∀ (ρ: Bid.Dir G c'→AxisChart G F), (Sienna.warm M h hS).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ → ∀ β m:ℝ, Cash W t l L Q o m T (Pane.virgin T B β)→
        ∀ X:Coat T F, X.x=t→X.width=o.K→X.manifest→flags (Pressure.temp t) X.V=∅→ ∀ α:ℝ,|α| ≤ c→ ∀ (Y:Activities G f), Y.Valid B (incomingE G L t) 0 → title Y → Tilt (j+1+2) u (Ht t) d (w t) (adjustment F ρ Y) → ∀ y: Positions (Uniform.Primary c' G), X.V=represent (tint G _ y) → ‖y‖+2*r < u→
         0 < crestF T B β Y y ∧ Brush j (7*x^a) u⁻¹ (aura T B α β Y - quasar T F Q.table v ρ α Y n β) y :=by
    by_cases h : 0 < (M.tables b P).gap; swap; · apply Eventually.of_forall; intro t x u r d c' f S T F h ht m B B' ha hh hv hk hB; subst K; subst P; subst b; exact False.elim (h (M.receipt F m hB hh.large rfl rfl|>.1.pos_m))
    obtain ⟨z,hz',hh⟩:= forerun Q o P M b' b p hw R J' l hl (by omega)
    have hu:= (Sienna.posts L P Q.table b M R hw).1
    have hp':leaf n < a := by apply lt_trans _ hz; apply mul_lt_mul_of_pos_right (by unfold silver sacred; linarith only) (by positivity) -- price notation Macro
    have hφ:= settled Q.table Q.table_exists (σ:=σ) (C:=C) (K:=K) V («k»:=j+1+2) hu hw hp h hz' (show n+1≤ k by omega) j (by omega) a hz
    obtain ⟨g,hg,-,-,hU⟩:= LocalAtlas.quote P Q o n j hn.le M R J' b b' hk hw _ a hl hp'
    obtain ⟨m',-,hV⟩:= LocalAtlas.summit P Q o n j hn M R J J' b b' hk hw c l a hl hp'
    have hh' : ∀ᶠ t in atTop, wick G L z t ≤ Ht t := by filter_upwards [(Bolt.still (G:=G) («L»:=L) z).listens zero_lt_one] with t ht; rw [Real.rpow_one] at ht; exact (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ht) (Delay.monitor_pos G L t).le).trans_eq (sq _).symm
    filter_upwards [hh,hφ,hV,hU,hh', Delay.shift_pos G L] with t hT hx hV hW hr' ht x u r d c' f S T F h hS v B B' he hQ hA hK hB hB' ρ hρ hM β m H X hR hF hq hX α hα Y hY ht' ht'' y hs he'
    subst K; subst P; subst b; subst b'
    have hr:0<r:= Real.rpow_pos_of_pos ht _; have hg:‖y‖<u:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg zero_le_two hr.le)) he'; have hG : Critical F T.high T.up ρ:= (hρ.2.2.2.2.2).1
    obtain ⟨hy,hz⟩:= hx c' f S T F T' M B β v y ρ Y hQ rfl rfl rfl hB H.laws.intake.positive H.laws.intake hY ht' hρ (hT c' f S T F rfl rfl hQ rfl rfl hB _ hB' ρ hρ hM v X hR hF hq B B' m β H he hX y hs hg) (tilt_smaller ht'' hr') he'
    have hσ := (hV c' f S T F rfl rfl v B B' he hQ rfl rfl hB hB' ρ hG ⟨ρ,hG,hM⟩ β m H X hR hF hq hX α hα y hs he').2.2; have h₀ := (hW c' f S T F rfl rfl v B B' he hQ rfl rfl hB hB' ρ hρ hM β m H X hR hF hq hX y hs he').2.1
    rw [show (7:ℝ)*x^a=((2:ℝ)*x^a+2*x^a)+3*x^a from (by ring)]; refine ⟨hy,((hz.separating h₀).gathering hσ).shimmy (Eventually.of_forall fun z=>mixed T F Q.table v ρ B α β Y z)⟩ -- leftover lets reduce algebra
end aura
end YM.Juniper.Mulberry
