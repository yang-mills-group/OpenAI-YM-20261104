import YM.Juniper.Mulberry.Canvas
import YM.Juniper.Mulberry.Wreathe
/-!
 # Neutrally authorized tilted log confirmation through all finite order

 localized cost. No implicit Body count. Everything before projection estimate.
 Takes actual receipt in SAME joint not F0 replaced. Physical read kernel
 validity at same λ; valence stem not here. Capturing proof later requires other
 Taylor estimates & Grams. This proves qass.rg__Stencil.mixed-cost reduction for
 actual *AUX WINDOW*; projection onto T+ globally earned by Orrery.
 Proof adapts Token.languid.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {T' : Teller G} {L : Side} (O : ChartRatio G) (ho : LocalRatio O)
    {K : KernelChoices} (V : ChartPrices) {σ C' C Z a d: ℝ} {t f r P :ℝ→ℝ} {k n:ℕ}
local notation "B"=> (fun t:ℝ=>Pressure.betaF G t L)
local notation "W"=> eaves G L
local notation "V!"=> wick G L d
local notation "Y"=> Mulberry.shadow G L
noncomputable def mouthful {G:Gauge}{c f:Side}{S:StepData c f} (F: Forest S.ratio) (T:Tube G S) (O:ChartRatio G) (k:S.Choices)
  (ρ: Bid.Dir G c→AxisChart G F) (P:Activities G f) (n:ℕ)(β:ℝ) (x:Positions (Uniform.Primary c G)) : ℝ:=
   let M:= Lapis.gram F T.up T.high ρ k; let g:=Lantern.grace (Lapis.table F k T.up T.high) (Lapis.mist F O T.up) (Lapis.orbit F ρ) M
   Mulberry.clean (sweep (M 0)⁻¹) (g+ adjustment F ρ P) n (gStep β,x)
variable (h:Rate G L 0 r)(h':Bolt G L f)(ht:Rate G L 0 t) (hm:0 < V.gap) (hd:0<d)
   (hk:n+1 ≤ k)
-- from LocalAtlas.Local arc_est
private lemma markedArc {j:ℕ}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{p q:ℝ}{h:ℝ×E→ℝ}{x:E}{t:ℝ}(he: Brush j p q h (t,x)): Brush j p q (h ∘ arc t) x:= by
    let P:= hook E; have hx(i:E): arc t i=(t,0)+P i:=by simp [P]
    rw [show h ∘ arc t=(fun i=> h ((t,0)+P i)) from funext fun i=> congr_arg h (hx i)]; exact skim _ ((hx x) ▸ he) n_hook
include ho ht hm hd h h' hk
local notation "θ"=> (V.gap/2)⁻¹
omit ho ht hm hd h h' hk in
private lemma sweat (L:Side)(hp:Rate G L 0 f)(k:ℕ) : Rate G L (-sacred*k) (fun x=> f x*(1 + (Mulberry.shadow G L x)⁻¹)^k):= by
   have he : Rate G L (-sacred) (fun x:ℝ=> (Mulberry.shadow G L x)⁻¹):= by
      refine Rate.power.congr ?_; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le]; rfl
   have ht:= (((Rate.const 1).weaken (show 0 ≤ -sacred by norm_num [sacred])).add he).pow k; simpa only [zero_add] using! hp.mul ht
set_option maxHeartbeats 700000 in
lemma settled (j:ℕ)(hj:j+1≤ k)(X : ℝ)(hX:drive n < X): ∀ᶠ x in atTop, let b:=B x; let u:=eaves G L x; let D:= wick G L d x; let v':=shadow G L x
    ∀ (c f' :Side)(S:StepData c f') (T : Tube G S)(F:Forest S.ratio) (p : Teller G) (K': Before G σ C S.patch.J S.kernel (k+3)) (B' : BudgetPoint) (β:ℝ) (a:S.Choices)(U:Positions (Uniform.Primary c G)) (ρ:Bid.Dir G c→ AxisChart G F)(P: Activities G f'), Quilt T F (f x) → S.kernel=K→ S.patch.L=L → K'.tables T.high S.patch=V →T.up.Bounds T.high σ C (ConnectedActivityE6.loopBill G L x)→
    0<β → Intake p T x (Pane.virgin T B' β) → P.Valid B' (incomingE G L x) 0 → title P → K'.Service F T.high T.up ρ → crimson T K' B' F ρ a L O d (r x) x β U → Tilt k u D v' (t x) (adjustment F ρ P) → ‖U‖+ 2*furl G L x < u →
       let t:= fun x=> veilF T B' β P x- (Real.log (solar F O β) - coverLog F T O a ρ β x + mouthful F T O a ρ P n β x)
       0 < crestF T B' β P U ∧ Brush j (2*b^X) u⁻¹ t U := by
   have hθ:0<θ:= inv_pos.mpr (half_pos hm)
   obtain ⟨p,hp,hQ⟩:= fits k n h h' ht hd hθ X hX hk
   let Q (x:ℝ):= p x*(1+(Y x)⁻¹)^(j+1); let U (x:ℝ):= (f x)*(Fintype.card Axis:ℝ)
   obtain ⟨c',hU⟩:= paint_supply G (j+1); obtain ⟨C₀,hC₀,h₁⟩:= Brush.compact (f:=Real.exp) (k:=j+1) (s:=({0}:Set ℝ)) isCompact_singleton (fun i _=> Real.contDiff_exp.contDiffAt)
   obtain ⟨L₁,hL₁,h₂⟩:= Brush.compact (f:=Real.log) (k:=j+1) (s:=({1}:Set ℝ)) isCompact_singleton (fun i hi=> Real.contDiffAt_log.mpr ((mem_singleton_iff.mp hi) ▸ one_ne_zero)); let J:= j+1
   let K₃ x:= prime G K J c' C₀ (2*B x) (U x); let M x:= clump J (K₃ x) L₁ + (oat J (r x) (2*B x)+oat J (r x) (2*B x)) + (Q x+ Q x)+1
   let D₁:ℝ:= (J:ℝ)^2+2; have h₀ : -(Mulberry.sacred)*(J:ℝ) ≤ D₁ - 1:= by unfold D₁ sacred J; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) j]
   have hM:Rate G L (D₁-1) M:= by
       have hT:= (Token.climbF (Token.primeR U K (Z:=c') (a:=C₀) (n:=J) (h'.uses.mul_right _)) (by positivity) J L₁) -- j arg no. norm
       have hQ:= sweat L hp J; have hR:1 ≤ D₁ -1:=by unfold D₁; nlinarith only [sq_nonneg (J:ℝ)]
       exact (((hT.weaken (by unfold D₁; nlinarith only)).add ((Token.oatr J h).weaken hR)).add ((hQ.add hQ).weaken h₀)).add ((Rate.const _).weaken (zero_le_one.trans hR))
   let v':=Real.exp (-1)*(1/2:ℝ); let g x:= Real.exp (-(V.gap*(V! x)^2 /4)/2)
   let G' x:= (Real.exp 1*g x)/v'; let a':= V.gap*d^2/8; have hg':0<a':=by unfold a'; positivity
   have hy (x:ℝ): g x= Real.exp (-a'* (Delay.fineMonitor G L x)^(2:ℝ)):= by unfold g a' wick; rw [Real.rpow_two]; congr 1; ring
   obtain ⟨w,hw⟩:= iteration G L j (d:=D₁) (m:=X) zero_lt_one; let s:=min (-1) w
   have h'':Rate G L (s-1) G':=by unfold G'; simp_rw [div_eq_mul_inv]; simp_rw [hy]; exact (((Rate.monitor_cutoff (G:=G) (L:=L) hg' (by norm_num)).mul_left _).mul_right _)
   have hD':∀ᶠ x in atTop, f x * incomingE G L x ≤ 1:= (below' G L (h'.uses.mul (incomingE_rate G L)) (by norm_num) zero_lt_one).mono fun _ hx=> hx.le
   filter_upwards [hw,hQ,hM _ (show D₁-1<D₁ by linarith),hD',(Work.E09.betaF_growth G L).eventually_ge_atTop 1, h'' w (by unfold s; linarith only [min_le_right (-1:ℝ) w]), h''.below (by unfold s; linarith only [min_le_left (-1:ℝ) w]) 1 zero_lt_one] with x hw hx hM hE hb hS hv b u D v₀ c f' S T F p' A B' β a y ρ P hF hK hL hA hup hβ hT hP hPt hρ ht hU' hy'
   obtain ⟨hg,hd,hH,hW⟩:= ht; have h₀: ‖(0:Positions (Uniform.Primary c G))‖<u := norm_zero.trans_lt hg.pos
   have hV':0<b := zero_lt_one.trans_le hb; let K':= (2*B x); let W':= cutLog F T β O a ρ P D
   have hwβ: β≤2*b:= by change β≤ 2 * betaF G x L; rw [← hL]; exact hT.window.2
   have hf := mul_le_mul_of_nonneg_right hF.finalP (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (Pressure.betaF G x L))) ((11:ℝ)/5)); have hθ₀ : (Fintype.card (Precision.Key F G):ℝ)≤ f x:=countsK F _ hF.overall
   obtain ⟨hv',hg₀,hR,hQ,hx⟩:= hx _ _ _ _ _ _ _ hg hU' hθ₀ (show _ from fun z=> by rw [← hA]; exact wakes F a T.up T.high ρ σ C (ConnectedActivityE6.loopBill G L x) A hF.large hup hρ _ (h₀.trans_le hH)|>.2.2.1 z) -- σ2 typo
   let v'':= furl G L x; have hz:0<v'':= Real.rpow_pos_of_pos hV' _
   let Φ:= lacking F T B' β O a ρ P D
   have hY (y':Positions (Uniform.Primary c G))(ht:y'∈ closedBall y v''): ‖y'‖<u:= by
       have hh:=mem_closedBall_iff_norm.mp ht; have ha:= norm_add_le y (y'-y); rw [show y+(y'-y)= y' from by abel] at ha; change ‖_‖+2*v''<_ at hy'; linarith only [hz,hb,hy',hh,ha] -- add_sub_cancel simp
   have hδ z (hz:‖(z:Positions (Uniform.Primary c G))‖<u): ‖(gStep β,z)‖<u:= max_lt (by rw [Real.norm_of_nonneg]; exact hd; exact Fare.gS _ hβ|>.1.le) hz
   have hΛ:= mul_nonneg (a:=Real.exp 1) (b:=g x) (Real.exp_pos _).le (Real.exp_pos _).le
   have hG' z (hz:z∈ closedBall y v''): 0<crestF T B' β P z∧ ‖Φ z‖ ≤ G' x:= by
       have hu:= hW z (hY z hz) (mem_closedBall_iff_norm.mp hz)
       rw [hA] at hu; exact allegiance F T B' β O a ρ P hP hPt hT hg (hY _ hz) hd ho hu (hf.trans hE) (by unfold v'; positivity : 0<v') ((hx _ (hδ z (hY _ hz))).1)
   have hu : Brush j (b^X) 1 Φ y:= by
       apply hw _ _ Φ y (fun z hz=> ?_) (fun z hz=> (hG' z hz|>.2).trans ((le_abs_self _).trans hS))
       have hC:(Fintype.card (Bond c):ℝ) ≤ U x:= by unfold U; rw [Fintype.card_prod]; push_cast; exact mul_le_mul_of_nonneg_right hF.primary (Nat.cast_nonneg _)
       have hzk := Token.primeN (C:=C₀) (Z:=c') (v:=U x) (G:=G) K (n:=j+1) hβ hwβ hC₀.le hU.1.le ((Nat.cast_nonneg _).trans hC); rw [← hK] at hzk
       obtain ⟨hΦ,hΦ'⟩:= hG' z hz; obtain ⟨hx',hXβ⟩:= (hx _ (hδ z (hY z hz))).2; have hk' : Brush (j+1) (Q x) 1 W' z:= ((markedArc hx').smaller hj).trim
       apply (sponsor F T B' β O a ρ P hP hPt hT hg (hY _ hz) hzk.1 hC hU (h₁ _ (mem_singleton _)) (h₂ _ (mem_singleton _)) hΦ hj hk' (hΦ'.trans ((le_abs_self _).trans hv))).climb _ le_rfl
       have hK' : Token.oat J (r x) β ≤ Token.oat J (r x) K':= Token.rung hβ.le (hg.curve 0 h₀ |>.nonneg) hwβ -- curve args
       exact le_trans (add_le_add (add_le_add (add_le_add (Token.rising J hzk.1 (show prime G S.kernel J c' C₀ β (U x) ≤ prime G K J c' C₀ K' (U x) from by nth_rw 1 [← hK]; exact hzk.2) hL₁.le) (add_le_add hK' hK')) le_rfl) le_rfl) ((le_abs_self _).trans hM)
   have hy' : y∈ closedBall y v'':= mem_closedBall_self hz.le; have hu':0<u:=hg.pos
   intro t; refine ⟨(hG' y hy').1,?_⟩
   let s':= mouthful F T O a ρ P n β; rw [two_mul]; refine (((hu.climb le_rfl ((one_le_inv₀ hu').2 hg.small)).gathering ((markedArc ((hx _ (hδ _ (hY _ hy'))).2.2)).smaller (by omega : j ≤ k))).shimmy ?_)
   exact Eventually.of_forall fun z=> by change _= Φ z + (W' z-s' z); unfold t Φ lacking s' W'; ring
end YM.Juniper.Mulberry
