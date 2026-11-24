import YM.Juniper.Mulberry.Spend
/-!
 # E tilts in same Beam coordinates as authentic Sienna/Fare

 *Don't* treat K partners or θ flags here within E analytic. Applied
 ONLY ON the small common footprint KERNEL (has K but *in these
 compared calls* via Canister ALWAYS K blank). Preserve partners all
 actual iterations; join to same kernel with nonlinear transfer from Standing.
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
variable {G : Gauge} {c f:Side} {S : StepData c f} (F:Forest S.ratio) (T: Tube G S) {r t v u s:ℝ}
    (B : BudgetPoint) (β:ℝ) (O:ChartRatio G) (k:S.Choices) (ρ : Bid.Dir G c→ AxisChart G F)
    {D : ℝ} {j:ℕ}
local notation "X"=>Positions (Uniform.Primary c G)
local notation "A"=> Pane.virgin T B β
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "M"=> (Fintype.card (Site f):ℝ)
variable (P: Activities G f)
def fleece (P:Activities G f) := { Pane.virgin T B β with activities:=P }
def title := P.K=(Pane.pale f G).K ∧ P.forced=(Pane.pale f G).forced
def tiltF (U:Config G f):= Real.exp (-(P.additive B U))
local notation "U*"=> fleece T B β P
lemma tilted (ht:title P) (x:Config G f) : (U*).eval x=(A).eval x * tiltF B P x:=by
   have he:= Pane.pale_value B x; have h:(A).activities.gas B x=P.gas B x:=by
       apply tsum_congr; intro i; have hy : (A).activities.admissible B x i ↔ P.admissible B x i := by unfold Activities.admissible; rw [ht.2]; rfl
       unfold RG.Activities.gasOccurrence; split; next hz=> rw [if_pos (hy.1 hz),ht.1]; rfl
       next hz=> rw [if_neg (hy.not.mp hz)]
   have hF: (U*).exponent x= (A).exponent x + -(P.additive B x):=by unfold Rep.exponent; dsimp only [Pane.virgin,fleece]; rw [he.1]; ring
   unfold Rep.eval; rw [hF, Real.exp_add]; unfold tiltF; rw [show (A).activities.gas (A).p x=(U*).activities.gas (U*).p x from h]; ring
lemma stipend (h: P.EBound B r)(U:Config G f) : ‖P.additive B U‖ ≤ M*r:= by
    obtain ⟨b,h,hb⟩:=h; let p i (j:Site f):= if (P.reg i).site=j then B.mass (P.reg i).support (b i) else 0
    have hv:SumBudget (fun i=> ∑ j,p i j) (M*r):= by
       have he:= budget_over Finset.univ (fun j i=> p i j) (fun _=>r) (fun i _=>hb i); simpa only [Finset.sum_const,nsmul_eq_mul, Finset.card_univ] using he
    let f i:= P.regularOccurrence B i U
    have ht : SumBudget (fun i=>‖f i‖) (M*r) := by
       apply budget_mono hv (fun i=>norm_nonneg _); intro i
       have hz: ‖f i‖≤ b i:=AnalyticBridge.CouplingShape.mask_cost (h i) U
       simp only [p,Finset.sum_ite_eq,Finset.mem_univ,if_true]; exact hz.trans (B.loMass _ _ (h i).1)
    unfold Activities.additive; exact (norm_tsum_le_tsum_norm ht.2.1).trans ht.2.2

def openF (U:Config G f):= ∑' i:ℕ, P.E i U
lemma cleanedF (x:Config G f)(hx:flags B.threshold x=∅) : P.additive B x=openF P x := by
   refine tsum_congr (fun i=>masked_eq _ _ _ _ ?_); unfold Healthy; rw [hx]; simp
local notation "Yu"=> fun x:X=> represent (tint G _ x)
local notation "V'"=> Lapis.orbit F ρ
local notation "p"=> Lapis.table F k T.up T.high
local notation "q"=> Lapis.mist F O T.up
local notation "K"=> Lapis.gram F T.up T.high ρ k
local notation "X₀"=> closedBall (0:Poll.Body (Precision.Key F G)) D
noncomputable def shadeShift (z:Y)(y:X)(t:ℝ) := F.drape (draw F (Yu y) (V' y+t • z))
def adjustment (P:Activities G f)(z:Y)(x:ℝ×X):= -(openF P (shadeShift F ρ z x.2 x.1))
local notation "ε"=> (adjustment F ρ P)
local notation "Ω"=> (Lantern.grace p q V' K + adjustment F ρ P)
local notation "Ω'"=> (gStep β)
lemma tanning (z:Y)(x:ℝ× X)(t:ℝ) : ε (t • z) x=ε z (LocalAtlas.turn t x) := by change -(openF P (F.drape (draw F _ (V' _+x.1 • (t • z)))))= -(openF P (F.drape (draw F _ (V' _+(t*x.1) • z)))); rw [smul_comm x.1 t ,mul_smul]; rfl
section Tilt
variable (h : P.Valid B r v) (hp: title P) {J:Teller G} (ht: Intake J T t (Pane.virgin T B β))
    {c':ℝ}
local notation "σK"=> Env.along
abbrev tempered (x:Config G c)(i:F.Slice G):= Fare.overall F T B β x i * tiltF B P (F.drape i)
local notation "Q'"=> (tempered F T B β P)
include ht h hp
lemma fulling (x:Config G c): RG.Envelope (Q' x) ∧ S.push β (U*).eval x=∫ y, Q' x y ∂ F.order G:= by
    let H:= (U*); let w:= (tiltF B P); let u':= Fare.overall F T B β x
    have hm:S.patch.Branches S.kernel G:=ht.ready.knobs.symm ▸ ht.ready.kernel; have he := (amt F T B β _ J ht x); refine ⟨he.1.mul (Env.along (RG.Envelope.exp (RG.Envelope.neg ⟨Activities.E_measurable h.regular,⟨_,fun i=> stipend B P h.boundE i⟩⟩)) F.continuous_drape.measurable),?_⟩
    have hL : (U*).Lawful J.top.width J.top.paths (ConnectedActivityE6.loopBill G S.patch.L t) r v:=⟨ht.cap.paths,h⟩
    rw [F.pushing (S.isKernel hm β) (U*).eval x (lawful_gi hL) ((U*).envelope hL|>.integrable _) (fun k U=>S.covary hm k β U x)]; apply integral_congr_ae; filter_upwards with a; rw [tilted _ _ _ _ hp, tempered,Fare.total]; ring
local notation "K*"=> (fun x:X=> solar F O β * Real.exp (-coverLog F T O k ρ β x))
local notation "r*"=> cut (sweep (K 0)⁻¹) X₀ Ω
variable (H : Golf (Lapis.table F k T.up T.high) (Lapis.mist F O T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) j D u u c')
    {x : Positions (Uniform.Primary c G)} (hx:‖x‖< u) (hr:gStep β < u) (ho: LocalRatio O)
variable (hE: ∀ z : Poll.Body (Precision.Key F G),‖z‖≤ D→flags B.threshold (shadeShift F ρ z x (gStep β))=∅)
  (hK:∀ z:Poll.Body (Precision.Key F G),‖z‖≤ D →windmill F (Lapis.orbit F ρ x+gStep β • z) ∈ mouth O)
  (hG:∀ z:Poll.Body (Precision.Key F G),‖z‖≤ D→∀ l:S.Choices,Lapis.table F l T.up T.high (x,Lapis.orbit F ρ x+gStep β • z)=Lapis.table F k T.up T.high (x,Lapis.orbit F ρ x+gStep β • z))
local notation "U₁"=> staying F (V' x) (gStep β) D (Yu x)
include H hx hr ho hE hK hG
lemma central : ∫ y in U₁, Q' (Yu x) y ∂ F.order G= K* x*r* (gStep β,x):=by
    obtain ⟨h'l,hh⟩:= fulling F T B β P h hp ht (Yu x); have hβ:0<β:=ht.positive; have hm : (K 0).PosDef:= (H.gram 0 (norm_zero.trans_lt H.pos)).1; rw [Fare.cubits F O _ _ _ _ _ (Fare.gS _ hβ).1 ho hK h'l.meas.stronglyMeasurable,← integral_const_mul,Mulberry.cut,Blaze.Shield.recommends _ hm.inv]; rw [← integral_const_mul,← integral_indicator (measurableSet_closedBall)]; apply integral_congr_ae; filter_upwards with i
    by_cases hS:i∈X₀; swap; · rw [Set.indicator_of_notMem hS, indicator_of_notMem hS,mul_zero,mul_zero]
    rw [indicator_of_mem hS,indicator_of_mem hS]; let b:= V' x+gStep β • i; let a := (Yu x); have hb:= Fare.reserves F T O k ρ B β D H hβ hr (ht.ready.knobs.symm ▸ ht.ready.kernel) hx hG ho hK hE i hS
    have hk : tiltF B P (F.drape (draw F a b))=Real.exp (adjustment F ρ P i (gStep β,x)):= congr_arg (fun y:ℝ=> Real.exp (-y)) (cleanedF B P _ (hE i (mem_closedBall_zero_iff.mp hS)))
    dsimp only [a,b] at hk; simp only [Pi.add_apply,Real.exp_add, tempered]; rw [hk]; dsimp only at hb; linear_combination Real.exp (adjustment F ρ P i (gStep β,x))*hb
end Tilt
end YM.Juniper.Mulberry
