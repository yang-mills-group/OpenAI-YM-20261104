import YM.RGComparison01.AuxDrift

/-!
# Recover derivatives of auxiliary tail. General terminal consumer

T₀ is a bound on full J on the contributing fine (globally good only)
domain. Need power gross bound on core integral, including derivative order
*one higher* also (later supply by AuxFabric). -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxMiles
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxWeigh
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} (A : ChartRatio G) {P : Teller G} {K : KernelChoices} {C' p σ c' v κ δ d' : ℝ} {L : Side} {n j k : ℕ}
  {u d f g w T₀ : ℝ→ℝ}

section defs
variable {c f':Side} {S : StepData c f'} (F:Forest S.ratio) (T:Tube G S) (ρ:Bid.Dir G c→AxisChart G F)
    (B:BudgetPoint) (β:ℝ) (k:S.Choices)
local notation "g0" => gStep β
local notation "X" => Positions (Uniform.Primary c G)
local notation "V" => (fun x:X=> represent (tint G _ x))
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "U" => Lapis.table F k T.up T.high
local notation "r" => orbit F ρ
local notation "Ya" => Poll.Body (Precision.Key F G)

abbrev shot := AuxGrace.nodes U (mist F A T.up) r M
def tests (y:X) (z:Ya) := F.drape (draw F (V y) (orbit F ρ y+ g0 • z))
-- equality not asserted off healthy
variable (Z : Poll.Body (Precision.Key F G)→ℝ× Positions (Uniform.Primary c G)→ℝ)
def Plays (J:Config G f'→ℝ) (a D Q:ℝ) := GaugeInvariant J ∧ Envelope J ∧ 0≤Q ∧ (∀ i,flags B.threshold i=∅ → |J i|≤ Q) ∧ ∀ y:X, ‖y‖ < a →∀ z∈closedBall (0:Ya) D, flags B.threshold (tests F ρ β y z)=∅→ shot A F T ρ k z (g0,y)* J (tests F ρ β y z)= Z z (g0,y)

def play (D : ℝ) (x:X):= intake (M 0)⁻¹ Z D (g0,x)
end defs

local notation "M" => Delay.fineMonitor G L
local notation "Y" => (fun t=> betaF G t L)
local notation "mV" => eaves G L

lemma upper_guard (hh : Rate G L 0 d) : ∀ᶠ t in atTop, ∀ β, Y t/2 ≤ β → 1 < d t → d t*gStep β ≤ mV t:= by
  have he:= Sienna.contraction (a:=1) G L zero_lt_one (hh.mul (glim G L)) (show 0+ -(1/2:ℝ)<vow from (by norm_num [vow]))
  filter_upwards [he,Delay.shift_pos G L] with t ht hx β hβ h; rw [one_mul,one_mul] at ht; exact le_trans (mul_le_mul_of_nonneg_left (lamp G L hx _ hβ|>.2) (zero_le_one.trans h.le)) ht.le

set_option maxHeartbeats 480000 in
lemma resume (Q:ChartPrices) (hQ : 0<Q.gap) (hv : Rate G L 0 T₀) (hh : Rate G L 0 d) (hd:0 < d') (hp : Rate G L 0 u) (hr : Bolt G L f) (ha: LocalRatio A) (a g : ℝ) (K:KernelChoices) (k j:ℕ) (hk : j < k) : ∀ᶠ t in atTop,
    ∀ (c F':Side) (S:StepData c F') (T:Tube G S) (F:Forest S.ratio) (L':Before G σ c' S.patch.J S.kernel (k+3)) (B:BudgetPoint) (ρ:Bid.Dir G c→AxisChart G F) (β:ℝ) (P:Teller G) (i:S.Choices),
    S.patch.L = L→ S.kernel=K → Quilt T F (f t) → L'.tables T.high S.patch=Q → Intake P T t (Pane.virgin T B β) → 1 < d t →
    let b:=d t * gStep β; let D:= wick G L d' t
    ∀ x:Positions (Uniform.Primary c G), ‖x‖+furl G L t < b → AuxDesk.receipt T L' B F ρ i L A d' (u t) t β x→
    ∀ Z J, Plays A F T ρ B β i Z J b D (T₀ t) → (∀ y:Positions (Uniform.Primary c G), ‖y‖ < b → Brush (j+1) ((betaF G t L)^g) 1 ( play F T ρ β i Z D) y) →
       Brush j ((betaF G t L)^a) 1 (rescale F T A ρ B i β J -  play F T ρ β i Z D) x := by
  obtain ⟨v,hV⟩:= collar A (C:=c') (σ:=σ) hr hv hp ha Q hQ K d' k (j+1) hk (by omega)
  let s : ℝ := max v g + 1
  obtain ⟨C,hC⟩:= iteration G L j (m:=a) (d:=s) zero_lt_one
  let D:= Q.gap*d'^2/8; have hD:0<D:=by unfold D; positivity
  have ht : Rate G L (C-1) (fun t=> T₀ t * Real.exp (-D * M t^2)):= by
    have he:= Rate.monitor_cutoff (G:=G) (L:=L) (a:=C-1) hD (γ:=2) (by norm_num); simp only [Real.rpow_two] at he; simpa only [zero_add] using hv.mul he
  have he := ((Rate.power (G:=G) (L:=L) (a:=v)).weaken (le_max_left v g)).add ((Rate.power (G:=G) (L:=L) (a:=g)).weaken (le_max_right v g))
  filter_upwards [upper_guard hh,hV,hC,ht C (by linarith),he s (lt_add_one _)] with t h' hb he hx h c F' S T F L' B ρ β P i hL hK hQ' hv hI hr b D' x hz H Z J hP hY
  have hm:t = t:=rfl
  obtain ⟨hg,hξ,hU,hW⟩:=H.1
  obtain ⟨hJ,hy,hv',hT,HJ⟩:=hP
  have hδ : b ≤ mV t:= h' _ (hL ▸ (show betaF G t S.patch.L / 2 ≤ β from hI.window.1)) hr
  have hw y (hy:y∈closedBall x (furl G L t)): ‖y‖< b:= lt_of_le_of_lt ((norm_le_norm_add_norm_sub' y x).trans (add_le_add_right (mem_closedBall_iff_norm.mp hy) _)) hz
  apply he; swap
  · intro y H'
    have hw' := hw _ H'; have hZ := hw'.trans_le hδ; have hs:= H.2 y hZ (mem_closedBall_iff_norm.mp H')
    have he := credit F T A ρ B i β J hI hs hJ hy hT hv' ha hI.positive hg hξ hZ Z (fun z hj=> HJ _ hw' z hj (hs.2.2 z (mem_closedBall_zero_iff.mp hj))) (hW y hZ (mem_closedBall_iff_norm.mp H')).2
    have hT : -((L'.tables T.high S.patch).gap*(wick G L d' t)^2/4)/2= -D*(M t)^2:= by rw [hv]; unfold wick D; ring
    rw [hT] at he; exact he.trans ((le_abs_self _).trans hx)
  intro y H'; have hm:= hb _ _ S T F L' B P x β ρ i hL hK hQ' hv hI H.1 J hJ hy hv' hT y H' ((hw _ H').trans_le hδ)
  exact (hm.separating (hY _ (hw _ H'))).climb ((le_abs_self _).trans h) le_rfl
lemma mean_gross (p : Geo G L g) (hk : j < n) :∃ e:ℝ, ∀ᶠ t in atTop, ∀ β,0<β→β ≤ 2*Y t→ gStep β≤1→∀ d,1 < d→∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E→ℝ) (x:E) (F : AuxStage.Co E), AuxStage.Points (g t) (d*gStep β)⁻¹ (gStep β) k n f x F → Brush (j+1) (Y t^e) 1 f x:= by
  let u := j+1; let s:ℝ:=(1/2)*(u:ℝ)
  have hv:= AuxStage.wages p k; have h:= ((p.joins hv).rate).mul ((((Rate.const 1).weaken (by norm_num : (0:ℝ) ≤ 1/2)).add (burst_rate G L)).pow u)
  simp only [zero_add] at h
  refine ⟨s+1,?_⟩; filter_upwards [h (s+1) (lt_add_one _)] with t hx β hβ ha hu d hp E _ _ f x F H
  have he := (Fare.gS β hβ).1; have hh := H.full he.le hu; exact (((hh.smaller hk).climb le_rfl ((inv_anti₀ he (lt_mul_of_one_lt_left he hp |>.le)).trans (burst_h (G:=G) (L:=L) ha))).trim).climb ((le_abs_self _).trans hx) le_rfl
end YM.RGComparison01.AuxMiles
