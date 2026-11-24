import YM.Juniper.LocalAtlas.Agreement
/-!
 # Stitch critical comparison estimator after rendering real `Sienna` primitives

 Pay normalizer vacuum ∀β across band; after resetting kinetic α. Here
 `arctic` includes truncated `extra` internal order to preserve loss.
 Power of error TRUE through paths, includes draft with retained α.
 Error doesn't include itinerary `δ` or mask curtains, this over every `V`
 healthy AND small representative at aux. Reconnection to overhead Fk still
 to prove incl α chosen and β loss recurrence.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Analysis Work.G05 Shellac
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
local notation "Θ"=> Work.G05.blockTaylor

section smooth
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {u C : ℝ}{j:ℕ} {f:E → ℝ}
omit [FiniteDimensional ℝ E] in
private lemma growing (h : ∀ x∈ Metric.ball 0 u, ContDiffAt ℝ j f x ∧ ∀ i ≤ j, 0 < i → normJ i f x≤C) (he:1≤j)(hu:u≤1) {x:E}(hx:x∈Metric.ball 0 u): Brush j C 1 (off f) x:=by
   let S:=Metric.ball (0:E) u; have ht:S.Nonempty:=⟨x,hx⟩; have hV : (0:E)∈S:=Metric.mem_ball_self (Metric.nonempty_ball.mp ht)
   have he' x (hx:x∈ S):= h x hx; have hk x (hx:x∈S):= (he' x hx).2 1 he one_pos; have hC:= le_trans (norm_nonneg _) (hk x hx)
   apply Brush.offer.2; refine ⟨(he' x hx).1.sub contDiffAt_const,fun i hi =>?_⟩; unfold normJ
   match i with
   | 0=>
     rw [norm_iteratedFDeriv_zero]; refine le_trans ((convex_ball (0:E) u).norm_image_sub_le_of_norm_fderiv_le (fun w hw=> ((he' w hw).1.of_le (Nat.cast_le.mpr he)).differentiableAt (by norm_num)) (fun w hw=> by rw [← norm_iteratedFDeriv_one]; exact hk w hw) hV hx) ?_
     rw [sub_zero]; exact mul_le_of_le_one_right hC ((mem_ball_zero_iff.mp hx).le.trans hu)
   | i+1=> rw [off,iteratedFDeriv_sub_apply ((he' x hx).1.of_le (Nat.cast_le.mpr hi)) contDiffAt_const,iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]; exact (he' x hx).2 _ hi (Nat.succ_pos i)
end smooth

section rate
variable {L:Side}{σ C : ℝ}{k : ℕ}(J:BareRates.pre G σ C k) (b:Clip){f g p:ℝ→ℝ}
private lemma rateWing (h : Rate G L 0 g)(hp : Rate G L 0 p) : Rate G L 0 (fun t=> kinBill k J b (g t) (p t)) :=
  let h' := (Rate.const 1).add hp; (show Rate G L 0 (fun t=> tollS (g t) k (BareRates.bill J b)) from (by simpa only [zero_mul] using! (h.pow k).mul_right (BareRates.bill ..))).add (lumpRate k (h'.add h') hp)
private lemma rateBush (V:ℝ)(h:Rate G L 0 f)(he:Rate G L 0 g)(hp : Rate G L 0 p) : Rate G L 0 (fun t=> cryo J b (f t) (p t) V (g t)):= by
   let x₃(t:ℝ):=(1+|V|+g t)*BareRates.bill J b; let C₁(t:ℝ):=tollS (f t) k (x₃ t)
   have hv: Rate G L 0 C₁:= by simpa only [zero_mul,zero_add] using! (h.pow k).mul (((Rate.const (1+|V|)).add he).mul_right _)
   have h' := (Rate.const 1).add hp
   exact hv.add ((lumpRate k (h'.add h') hp).add hp)
end rate

variable {σ σ' C C' W W' : ℝ} {K : KernelChoices} {T' : Teller G}
variable (P : Patch) (Q : ConnectedActivityE6.Target G T') (o : Target.Order G W)
    (n j : ℕ) (hj:n < j) -- important need ≥ n+1 for `berry`
    (M : Push.Uniform.Before G σ C P.J K ((j+1+2)+3)) (R : FiberFee Q.table (((j+1+2)+3)+1))
    (J : BareRates.pre G σ' C' (j+1+2)) (T : BareRates.pre G σ' C' ((j+1+2)+3))
local notation "L" => P.L
variable {Z:ℝ→ℝ} (b b' : Clip)(hk : 2 ≤ j)(hv:Bolt G P.L Z)
local notation "A" => eaves G L
local notation "C₀"=> M.tables b P
local notation "O"=> (fun t=> pam (j+1+2) Q.table b P M (Z t) (Z t) R (ConnectedActivityE6.loopBill G L t))

include hv hj hk T J R M
set_option maxHeartbeats 700000 in
lemma summit (V a x : ℝ) (ha:0<a)(hp:leaf n < x) :
    ∃ Y:ℝ→ℝ, Rate G L 0 Y ∧ ∀ᶠ t in atTop,
      let z:=betaF G t L; let u:=eaves G L t; let o':= furl G L t
      ∀ (c f : Side) (S:StepData c f) (T:Tube G S) (F:Forest S.ratio) (_h:S.patch=P) (_tK:S.kernel=K)
         (k:S.Choices) (B B':BudgetPoint), B'.threshold=Pressure.temp t → Quilt T F (Z t) → T.high=b → T.low=b' → T.up.Bounds b σ C (ConnectedActivityE6.loopBill G L t) → T.down.Bounds b' σ' C' (ConnectedActivityE6.loopBill G L t) →
       ∀ ρ: Bid.Dir G c→AxisChart G F, Critical F T.high T.up ρ → (∃ ρ', Critical F T.high T.up ρ'∧ ClassicalMatch F T.high T.low T.up T.down ρ') →
       ∀ β p : ℝ,Cash W t a L Q o p T (Pane.virgin T B β) → ∀ X:Coat T F, X.x=t → X.width=o.K → X.manifest → flags (Pressure.temp t) X.V=∅ →
       ∀ α:ℝ, |α| ≤ V → ∀ y : Positions (Uniform.Primary c G), X.V=represent (tint G _ y) → ‖y‖+2*o' < u→
        0 < tramp T B β y ∧
         Estimate F T Q.table k ρ n α (Y t) ∧
         Brush j (3*z^x) u⁻¹ (harmony T B β α-arctic F T Q.table k ρ n α β) y:= by
   let s:= betaF G; let J₀:= j+1+2; let f t:= kinBill J₀ J b' (Z t) (O t); let g t:=cryo J b' (Z t) (O t) V (ConnectedActivityE6.loopBill G L t)
   obtain ⟨Y,U,hY,hU,hP⟩:= quote P Q o n j hj.le M R T b b' hk hv a x ha hp
   obtain ⟨d,hd,hS⟩:=Sienna.reaches Q o P M b' b Z hv R T a ha (by omega)
   have H:= Sienna.posts P.L P Q.table b M R hv|>.1; have hf:= rateWing J b' hv.uses H; have hg:= rateBush J b' V hv.uses (ConnectedActivityE6.loopBill_rate G L) H
   let u₁(t:ℝ):= (f t+overhead (n+3) J₀ * f t)*(A t)^(n+3+1)
   let u₂(t:ℝ):=(g t+overhead n J₀ * g t) * (A t)^(n+1)
   have hz: Rate G L (leaf n) (fun t=>2*s t L * u₁ t+u₂ t):= by
      have he:= (edge G L); have h₁:Rate G L (0+leaf (n+3)) u₁:= (hf.add (hf.mul_left (overhead (n+3) J₀))).mul (he.pow (n+3+1)); have h₂: Rate G L (0+leaf n) u₂:= (hg.add (hg.mul_left (overhead n J₀))).mul (he.pow (n+1)); exact Rate.add ((((show Rate G L 1 (fun t=> s t L) from Rate.hat).mul_left 2).mul h₁).weaken (by unfold leaf vow; push_cast; linarith)) (h₂.weaken (by rw [zero_add]))
   refine ⟨fun t=> f t+g t+U t, (hf.add hg).add hU,?_⟩
   filter_upwards [hP,hS,hz _ hp,Delay.shift_pos G L] with t hW hR hL ht z u o' c f' S T F h he k B B' hy hq hh hc hp' hk' ρ hρ ⟨ρ',hρ',ha⟩ β p X W he' hΞ hs hF α hδ y hw hY'
   subst P; subst K; subst b; subst b';
   obtain ⟨r,hV⟩ := M.graph F hp' hq.large rfl rfl
   have hr: ρ=ᶠ[𝓝 0] r:= Before.Service.is_extension hV hρ; have hr': ρ'=ᶠ[𝓝 0] r:= Before.Service.is_extension hV hρ'
   have hm : ClassicalMatch F T.high T.low T.up T.down r:=by
     intro k hk' v; obtain ⟨hk,hp₀,hP⟩:=ha k hk' v
     let X₀ (ρ:Bid.Dir G c→ AxisChart G F) := fun x=> tested F v T.high T.up x (ρ x)
     have hv:X₀ ρ'=ᶠ[𝓝 0] X₀ r:=hr'.mono fun i hi=> congr_arg (tested F v T.high T.up i) hi
     exact ⟨hk.congr_of_eventuallyEq hv.symm,hp₀, ((hv.iteratedFDeriv ℝ k).eq_of_nhds).symm.trans hP⟩
   obtain ⟨hZ,hΩ,hE⟩:=hW c f' S T F rfl rfl k B B' hy hq rfl rfl hp' hk' r hV hm β p X W he' hΞ hs hF y hw hY'
   have hβ:=X.laws.intake
   have he : β>0:= hβ.positive; have ht₀:0<o':= Real.rpow_pos_of_pos ht _
   have hk₀: ‖y‖<u:= lt_of_le_of_lt (le_add_of_nonneg_right (mul_nonneg zero_le_two ht₀.le)) hY'
   let T':= Q.table
   let K:= cedar F T r k; let Z':= shed F T T' r α k; let P':= ball (0:Positions (Uniform.Primary c G)) u
   have H:=(hR c f' S T F rfl rfl hq rfl rfl hp' _ hk' r hV hm k W he' hΞ hs B B' p β X hy hF y hw hk₀).1
   have hJ:0 <u:= H.pos
   have h0 : (0:Positions (Uniform.Primary c G))∈P':= mem_ball_self hJ; have hσ:= countsP F (Z t) hq.overall
   have ht₁ x (hx:x∈P'): Brush J₀ (f t) 1 (off K) x:= growing (sticks F T T' r k H hk' J hq.one hσ) (by omega) H.small hx
   have hpB: 0 ≤ BareRates.bill J T.low:= (bareSocket c J hk' (x:=0) (mem_ball_self zero_lt_one) 0).2.2.2.1.le
   have ht₂ (x) (hx:x∈P'): Brush J₀ (g t) 1 (off Z') x:= by
     have he: |α|≤|V|:= hδ.trans (le_abs_self _); refine (growing (hills F T T' r α k H hk' J hq.one hσ) (by omega) H.small hx).climb ?_ le_rfl; unfold g cryo tollS; have hZ := zero_le_one.trans hq.one; gcongr
   have hu:= (mem_ball_zero_iff.mpr hk₀); have hz' := (_root_.YM.Juniper.LocalAtlas.overall ht₁ H.small (show n+3+1 ≤ J₀ from (by unfold J₀; omega)) hk₀); have hs' := (_root_.YM.Juniper.LocalAtlas.overall ht₂ H.small (show n+1≤ J₀ from by unfold J₀; omega) hk₀)
   have hE: Brush J₀ (U t) 1 (loopCharge F T T' k r n) 0:=hE 0 ((norm_zero : ‖(0:ℝ×Positions (Uniform.Primary c G))‖=0).trans_lt hJ)|>.2
   obtain ⟨hv',hC⟩:= paired F T T' k ρ r hr n α β (f t+g t+U t)
   have h'₁:= ht₁ _ h0|>.nonneg; have h'₂:= ht₂ _ h0|>.nonneg; have h'₃:= hE.nonneg
   rw [hv']; refine ⟨hZ,hC.mpr ⟨?_,?_,?_⟩,?_⟩ -- loop congr Q not T' ok
   · exact capped (((ht₁ 0 h0).climb (by linarith only [h'₂,h'₃]) le_rfl).smaller (by unfold J₀; omega))
   · exact capped (((ht₂ 0 h0).climb (by linarith only [h'₁,h'₃]) le_rfl).smaller (by unfold J₀; omega))
   · exact capped ((hE.climb (by linarith only [h'₁,h'₂]) le_rfl).smaller (by unfold J₀; omega))
   have hH:= hΩ.gathering (((hz'.smul β).gathering hs').smaller (by unfold J₀; omega : j ≤ J₀)); rw [Real.norm_of_nonneg he.le] at hH
   have hd:β*u₁ t+u₂ t ≤ z^x:= le_trans (add_le_add (mul_le_mul_of_nonneg_right hβ.window.2 hz'.nonneg) le_rfl) ((le_abs_self _).trans hL)
   refine (hH.climb (show 2*z^x+(β*u₁ t+u₂ t) ≤ 3*z^x from by linarith only [hd]) le_rfl).shimmy (Eventually.of_forall fun w=>?_)
   change harmony T B β α w-(Real.log _+β*_+(_+_)+_) = pures T B β w- mean F T _ k r n β w +(β*(K w-K 0-Θ (n+3) (off K) w)+(Z' w-Z' 0-Θ n (off Z') w))
   rw [merit F T T' B r β α k (D:=0) w]; dsimp only [mean,grant,cleanLetter,lack,K,Z',T']; ring
end YM.Juniper.LocalAtlas
