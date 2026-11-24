import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Lush
import YM.Contacts.Junction.Lotus
/-!
# adapt Ruling/Canvas: Use real vouchers: on x0 radius all(s).
 All on same V. `ruling` exact closure (no log yet) GO2. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {P : Teller G} {c f : Side} {S : StepData c f} {x W K' y σ C σ' C' Λ' e m t v q w : ℝ} {n : ℕ}
variable (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W) (F : Forest S.ratio) (T : Tube G S) (k : S.Choices)
    (A : Before G σ C S.patch.J S.kernel (n+3)) (ρ : Bid.Dir G c→AxisChart G F) (B B' : BudgetPoint) (β : ℝ)
    {D : ℝ}
local notation "M" => A.tables T.high S.patch
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Θ" => Q.table
local notation "G₀" => gStep β
local notation "U" => eaves G L x
local notation "D₀" => furl G L x
local notation "f₁" => Lapis.table F k T.up T.high
local notation "μ" => (Lapis.orbit F ρ)
local notation "g" => Lapis.mist F Q.table T.up
local notation "K" => Lapis.gram F T.up T.high ρ k
local notation "R₀" => Pane.virgin T B β
local notation "V" => (fun x: Xs=> represent (tint G _ x))
variable (E : FiberFee Q.table ((n+3)+1)) (J : BareRates.pre G σ' C' (n+3))
    (he : A.Service F T.high T.up ρ) (hh : Larger (G:=G) S)
    (hr : T.up.Bounds T.high σ C (ConnectedActivityE6.loopBill G L x)) (hz : T.down.Bounds T.low σ' C' Λ')
variable {vC xX:ℝ} (hb : 1 ≤ vC) (hk : (Fintype.card (Joint F G):ℝ) ≤ vC) (hF : (Fintype.card F.Free:ℝ) ≤ vC) (hs : (Fintype.card (Site f):ℝ) ≤ vC)
    (hp : Pigment n (A.tables T.high S.patch) Q.table D (gStep β) xX (eaves G L x) x B.threshold (furl G L x))
    (hL : S.patch.L=L) (hm : 0 < m) (hβ : 0<β) (hB : B.threshold ≤ m)
local notation "K₀" => pam n Q.table T.high S.patch A vC vC E (ConnectedActivityE6.loopBill G L x)
include k E he hh hr hb hk hs hF hp
variable (H : ∀ i:S.Choices, ∀ V':Config G c, ∀ z:F.Slice G, Alive S (F.drape z) i → (∀ j: Cell f,toll (F.drape z) j ≤ m) → (∀ b, wire (S.prediction (F.drape z) i) V' b ≤ m) →∃ w : Poll.Body (Precision.Key F G), ‖weld (Precision.Key F G) w‖≤(A.tables T.high S.patch).safety ∧ z=draw F V' w)
    (hV : ∀ z:ℝ, 0≤ z → z ≤ eaves G L x → β*meterQ (A.tables T.high S.patch) n vC*z+(A.tables T.high S.patch).gap/4*D^2 ≤ β*(S.kernel.penalty*m^2/2))
local notation "R" => (ChartPrices.gap (A.tables T.high S.patch) * D^2/4)
include E hm hB H hV hβ
lemma our_hub (ZH : Intake P T x R₀) {z:Xs} (ht : ‖z‖<U)
    (hy : ∀ i:Y,‖i‖≤D → flags B.threshold (F.drape (draw F (V z) (μ z+G₀ • i)))=∅)
    (hc : -(Fintype.card F.Free:ℝ)*Real.log (measure_g Q.table β)-R+vC*PathData.loopsPrice B β C (ConnectedActivityE6.loopBill G L x)+ K₀+tapir M vC ≤ -R / 2) :
    let v:=ratify f₁ g μ K D (G₀,z)
    let t:=solar F Θ β* Real.exp (-coverLog F T Θ k ρ β z)
    (∫ y in staying F (μ z) G₀ D (V z), overall F T B β (V z) y ∂F.order G)= t*v ∧
    (∫ y in (staying F (μ z) G₀ D (V z))ᶜ, overall F T B β (V z) y ∂F.order G) ≤ t*Real.exp (-R/2) := by
  intro v' t'; let Y':= staying F (μ z) G₀ D (V z); let G':= overall F T B β (V z)
  have hp' := courtyard Q F T k A ρ B β E he hh hr hb hk hF hs hp; have h' := amt F T B β x P ZH (V z)
  have hc' : (1+Before.Service.trailCost M (n+3))*U + G₀*D < (M).initial:= lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul_of_nonneg_right hp.lease.le hp.positive)) hp.initial
  have hY: Uniform.shade G*(Before.Service.trailCost M (n+3)*U + G₀ *D) < Q.table.radius := lt_of_le_of_lt (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hp.lease.le hp.positive)) (Uniform.shade_pos G).le) (hp.count.trans_lt (half_lt_self Q.table_exists.patch))
  have hv: ∫ i in Y', G' i ∂F.order G=t'*v':= pricing F T Θ k ρ B β D hp' hβ hp.lease hh.1 ht (Fare.gamma F T k A ρ he hh hr hp.horizon hp.booth ht hc') Q.table_exists (mouthF F T k A ρ he hh hr hp.horizon Θ hY hp.booth ht) hy (h'.1.meas.stronglyMeasurable)
  have hX:0< solar F Q.table β:= sun F Q.table β hβ Q.table_exists; have hz :0<t':= mul_pos hX (Real.exp_pos _)
  refine ⟨hv, outside_est F T B β _ _ P ZH (by positivity) (fun i hi=> ?_)⟩
  apply (bulks Q F T k A ρ B β E he hh hr hb hk hF hs hp hm hβ hB H hV ht i hi).trans
  unfold t'; rw [mul_assoc,← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (add_le_add le_rfl hc)) hX.le
end YM.PhysicalNext.Repeat.Sienna
namespace YM.PhysicalNext.Repeat.Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {σ C σ' C' Λ' W x μ v : ℝ} {q : Teller G} {K : KernelChoices} {f c : Side} {n:ℕ}
abbrev loyal {S:StepData c f}(F:Forest S.ratio)(T:Tube G S)(L:Side)(d a β t:ℝ)(ρ:Bid.Dir G c→AxisChart G F)(B:BudgetPoint)(z:Positions (Uniform.Primary c G)):=
   let x:=represent (Uniform.tint G _ z); let f:=overall F T B β x; let H:= staying F (orbit F ρ z) (gStep β) (wick G L d t) x; let Ω:=F.order G; (∀ y∈H, flags B.threshold (F.drape y)=∅) ∧
    ‖z‖< eaves G L t∧ ∫ i in Hᶜ,f i ∂Ω ≤ a *∫ i in H,f i ∂Ω
variable (Q : ConnectedActivityE6.Target G q) (o : Target.Order G W)
    (P : Patch) (A : Before G σ C P.J K (n+3)) (p'p p : Clip) (w : ℝ→ℝ) (hk : Bolt G P.L w) (E : FiberFee Q.table ((n+3)+1)) (J : BareRates.pre G σ' C' (n+3)) (e : ℝ) (he : 0<e) (hn : 5 ≤ n+3)
local notation "V₀" => A.tables p P
include J he hn hk E
set_option maxHeartbeats 400000 in
lemma our_procure : ∃ d:ℝ, 0<d ∧ ∀ y:ℝ, y<0 → ∀ᶠ t in atTop, ∀ (c f: Side) (S:StepData c f) (T : Tube G S) (F:Forest S.ratio) (h:S.patch=P) (ht:S.kernel=K), Quilt T F (w t) → T.high=p → T.low=p'p → T.up.Bounds p σ C (ConnectedActivityE6.loopBill G P.L t) → ∀ Λ', T.down.Bounds p'p σ' C' Λ' →
    ∀ ρ: Bid.Dir G c→ AxisChart G F,(warm A h ht).Service F T.high T.up ρ→ ClassicalMatch F T.high T.low T.up T.down ρ →
    ∀ k:S.Choices, ∀ (X : Coat T F), X.x=t → X.width=o.K → X.manifest → ∀ (B B' : BudgetPoint) (m β:ℝ), Cash W t e P.L Q o m T (Pane.virgin T B β)→ B'.threshold=Pressure.temp t →
    flags (Pressure.temp t) X.V=∅ → ∀ x: Positions (Uniform.Primary c G), X.V=represent (tint G _ x) → ‖x‖ + 2*furl G P.L t < eaves G P.L t → ∀ z∈ closedBall x (furl G P.L t), loyal F T P.L d (betaF G t P.L ^ y) β t ρ B z := by
  by_cases h' : 0 < (V₀).gap ∧ 0 < (V₀).horizon ∧ 0 < (V₀).initial ∧ 0 < (V₀).safety
  swap
  · refine ⟨1,zero_lt_one,fun _ _=>Eventually.of_forall ?_⟩
    intro t c f S T F h hp hq hk hK hr m' hm' ρ H ha k; subst K; subst P; subst p
    have hS := A.receipt F k hr hq.large rfl rfl|>.1; exact False.elim (h' ⟨hS.pos_m,(show A.Service F T.high T.up ρ from H).x_pos,hS.pos_r,hS.reserveH_pos⟩)
  obtain ⟨l,hl,hL⟩:= Fare.wall G P K (V₀).safety h'.2.2.2; obtain ⟨U,hU,Hu⟩:= Fare.faceM G
  let V:= V₀; let Z:= P.L; let D':= pence U; have hd: 0 < D':= inv_pos.mpr (by positivity)
  have he' := compass P.L Q.table Q.table_exists P p A E hk D' o.ample h'.1 hd (stocksK G n σ' C' J p'p V) C'
  refine ⟨D',hd,fun y hyx=>?_⟩; obtain ⟨j,hxj⟩:∃ j:ℕ, n=j+2:=⟨n-2,by omega⟩; subst n;
  let A₁:= Real.exp (-1)*(1/2); let x₁:= V.gap* D'^2/8; have hA₁:0 < A₁ := by unfold A₁; positivity;
  obtain ⟨C'',hC'',hc''⟩:= lookingGlass G Z j w _ (fun z=> pam (j+2) Q.table p P A (w z) (w z) E (ConnectedActivityE6.loopBill G Z z)) _ (V.gap/2)⁻¹ D' vow 1 zero_lt_one (inv_pos.mpr (half_pos h'.1)) hd vow_ok (posts (E:=E) Z P Q.table p A hk |>.1) (edge G Z) (edge G Z) hk (-2)
  filter_upwards [hc'',Token.budgeting (G:=G) (L:=Z) (a:=A₁) y x₁ (by unfold x₁; have h:=h'.1; change 0 < V.gap at h; positivity) hyx, he',pencils (G:=G) (L:=P.L) (n:=j+2) U V Q.table Q.table_exists hU h'.2.1 h'.2.2.1,
    pressures Z P p A hk D' (K.penalty*l^2/2) (by have h:= K.penalty_pos; positivity), Rate.flame (G:=G) (L:=Z) |>.below (by norm_num) _ hl, Pane.wealthy Q Z he w hk.uses] with t hKpre hyP hx hY hh hg hM c f S T F h ht hQ hv hV H h₀ H₀ ρ Hρ hθ k X hX hw hm B B' m β R hT hF x hD hu
  subst K; subst P; subst p; subst p'p; subst t
  have hv : A.Service F T.high T.up ρ:= Hρ
  let t:=X.x; let D:= wick G Z D' t; let w':=w t
  let Y:=eaves G Z t; have hR:=R.laws.intake; have hB : B.threshold=Pressure.fiery G t S.patch.L:= hR.received.temp; have hvx:0<β:=hR.positive
  obtain ⟨hp,hvβ⟩:=hR.window
  have hP:Pigment (j+2) V Q.table D (gStep β) U Y t B.threshold (furl G Z t):= by rw [hB]; exact hY β hp
  
  have hH i (V: Config G c) (Z:F.Slice G):= hL S rfl rfl hQ.large F V Z i
  have hf : 1 ≤ w':=hQ.one; have hW := hh β hvx hp hQ.one; have hb':B.threshold≤l:= hB ▸ (le_abs_self _).trans hg
  let eB := let a:= stocksK G (j+2) σ' C' J T.low (A.tables T.high S.patch);β*(w'*a*‖x‖^5+w'*(C'*B'.threshold^3+C'*B'.threshold^4))+
      (pam (j+2) Q.table T.high S.patch A w' w' E (ConnectedActivityE6.loopBill G Z t)+tapir (A.tables T.high S.patch) w'+w'*o.ample/2)
  have hzT:0<betaF G t Z:= (show 1<betaF G t Z from hR.height).trans' zero_lt_one; have htY:0 < furl G Z t:= Real.rpow_pos_of_pos hzT _;
  replace hu : ‖x‖<Y ∧ ‖x‖ +2*furl G Z t < Y:= ⟨ by change ‖x‖+2*furl G Z t < Y at hu; linarith only [hu,htY], hu⟩
  have hc:= hx eB β hQ.one hvx hvβ _ (Nat.cast_nonneg _) hQ.lever B hB B' (hT ▸ R.laws.data.room.temperatures) ‖x‖ (norm_nonneg _) hu.1.le rfl
  have hA:= cooler Q o F T k A ρ B B' β E J hv hQ.large H H₀ hQ.one hQ.overall hQ.lever hQ.finalP hP hl hvx hb' hH hW X R rfl hw hm hT hQ.primary hQ.sizes (hT ▸ hF) (by assumption) hu.1 hθ hn (hM _ hQ.step) hc.1
  have hs : (1+Before.Service.trailCost V (j+2+3))*Y+gStep β*D ≤ 1:= le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hP.lease.le hP.positive)) hP.one.le
  have hh:= slack F T k A ρ hv hQ.large H hP.horizon B β (x:=x) (D:=D) hu.1 hvx hs hA hU (Hu F) hP.sermon
  intro z hz
  have hy: ‖z‖<Y∧‖z‖ + furl G Z t < Y:= by
      have hL : ‖z‖≤ ‖x‖+ furl G Z t:= (norm_le_norm_add_norm_sub' ..).trans (add_le_add_right (mem_closedBall_iff_norm.mp hz) _); constructor <;> linarith only [hL,hu.2,htY]
  obtain ⟨uP,hp₀⟩:=our_hub Q F T k A ρ B β E hv hQ.large H hQ.one hQ.overall hQ.lever hQ.finalP hP hl hvx hb' hH hW hR hy.1 (hh z hy.1 (mem_closedBall_iff_norm.mp hz)) hc.2
  have hv':= courtyard Q F T k A ρ B β E hv hQ.large H hQ.one hQ.overall hQ.lever hQ.finalP hP
  let f₀:= gStep β; let v' := ratify (Lapis.table F k T.up T.high) (mist F Q.table T.up) (orbit F ρ) (gram F T.up T.high ρ k) D (f₀,z)
  have hpre : A₁ ≤ v':= by
      refine (hKpre _ _ (Lapis.table F k T.up T.high) _ _ _ (countsK F w' hQ.overall) hv' (fun i hi z => (Lapis.wakes F k T.up T.high ρ σ C _ A hQ.large H hv i (lt_of_lt_of_le hi hP.horizon)).2.2.1 z) f₀ z (gS _ hvx).1 hP.lease hy.2).1
  let τ:= solar F Q.table β*Real.exp (-coverLog F T Q.table k ρ β z); let p':= β; let w':= represent (tint G _ z); let m':= staying F (orbit F ρ z) f₀ D w'; let M:= overall F T B β w'; let Φ:= betaF G t Z ^ y
  refine ⟨?_,hy.1,?_⟩
  · rintro i ⟨j,⟨u,hu,w⟩,rfl⟩; subst j; exact hh _ hy.1 (mem_closedBall_iff_norm.mp hz) u (mem_closedBall_zero_iff.mp hu)
  change _ ≤ Φ * ∫ i in m',M i ∂F.order G; erw [uP]; let Ψ:= x₁ * Delay.fineMonitor G Z t^2; have h : -(Ψ)= -( (A.tables T.high S.patch).gap * D^2 / 4 ) /2:= by unfold Ψ x₁ D V wick; ring; -- use
  apply hp₀.trans; change τ * Real.exp _ ≤ Φ*(τ*v'); rw [mul_left_comm Φ]; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sun F _ β hvx Q.table_exists).le (Real.exp_pos _).le); rw [← h]; apply le_trans _ (mul_le_mul_of_nonneg_left hpre (Real.rpow_nonneg hzT.le _)); refine (le_of_eq ?_).trans ((div_le_iff₀ hA₁).1 hyP.1); unfold Ψ; rw [neg_mul]
end YM.PhysicalNext.Repeat.Sienna
