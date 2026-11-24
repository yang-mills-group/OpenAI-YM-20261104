import YM.AllOrder.Local.Pure

/-!
# PURE virtual periods Taylor comparison, physical hat-bandwidth and seam

General r∈(max(∥x∥,gStep β),eaves) chosen after geometry.
Enforce both the weights and flat index. Receipts consumed (and passed to the
canonical comparison). For application at cutoff level, need to debit polynomial
in `gStep β`, `r` with price `H` paid at post-L via the family--not asserted
here. Sharp when r=`Polylog(β)·gStep β`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Pure
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Shellac Vote Work.G05
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius

lemma regroup {r y B f m φ β:ℝ} {k:ℕ} (hr:0 ≤ r) (hy:0 ≤ y) (hp: β ≤ 2*y) (hg:0 ≤ B) (hh : m+m ≤ φ) (H:ℝ) (hf:0 ≤ f) :
    m+β*(B*r^(k+3))+(B+f)*r^(k+1)+(H*r^(k+1)+m) ≤ (|H|+2*B+f)*(y*r^(k+3)+r^(k+1))+φ := by
  let S:=|H|+2*B+f
  have h₁ : 2*B ≤ S:= by unfold S; linarith [abs_nonneg H]
  have h₂ : B+f+H ≤ S:=by unfold S; linarith [le_abs_self H]
  change _ ≤ S*(y*r^(k+3)+r^(k+1))+φ
  linarith only [hh, mul_le_mul_of_nonneg_right hp (mul_nonneg hg (pow_nonneg hr (k+3))), mul_le_mul_of_nonneg_right h₁ (mul_nonneg hy (pow_nonneg hr (k+3))), mul_le_mul_of_nonneg_right h₂ (pow_nonneg hr (k+1))]

variable {G : Gauge} {σ σ' C C' W : ℝ} {K : KernelChoices} {T' : Teller G}
variable (P : Patch) (Q : ConnectedActivityE6.Target G T') (o : Target.Order G W)
    (j k : ℕ) (M : Push.Uniform.Before G σ C P.J K ((j+1+2)+3))
    (R : FiberFee Q.table (((j+1+2)+3)+1)) (T : BareRates.pre G σ' C' ((j+1+2)+3))
local notation "L" => P.L
variable {g : ℝ→ℝ} (b b' : Clip) (hk : k+3 ≤ j) (hv : Bolt G P.L g)
local notation "M₀" => M.tables b P
include hk hv T R
set_option maxHeartbeats 200000 in
lemma predicted (a e : ℝ) (hA : 0<a) : ∃ H : ℝ→ℝ, Rate G P.L 0 H ∧
    ∀ᶠ t in atTop, let A:=eaves G P.L t; let y:= betaF G t P.L
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (hp:S.patch=P) (ht:S.kernel=K) (l:S.Choices) (B B' : BudgetPoint), B'.threshold=Pressure.temp t → Quilt T F (g t) → T.high=b → T.low=b' → T.up.Bounds b σ C (ConnectedActivityE6.loopBill G P.L t) → ∀ Λ, T.down.Bounds b' σ' C' Λ →
    ∀ (ρ:Bid.Dir G c→ AxisChart G F), (Sienna.warm M hp ht).Service F T.high T.up ρ → ClassicalMatch F T.high T.low T.up T.down ρ → ∀ β p : ℝ,Cash W t a L Q o p T (Pane.virgin T B β) →
    ∀ X:Coat T F, X.x=t → X.width=o.K → X.manifest → flags (Pressure.temp t) X.V=∅ → ∀ x:Positions (Uniform.Primary c G), X.V=represent (tint G _ x) → ‖x‖+2*furl G L t < A → ∀ r:ℝ, ‖(gStep β,x)‖ ≤ r → r<A →
        0 < tramp T B β x ∧ Brush j (H t * (y*r^(k+3) + r^(k+1)) + y^e) (r⁻¹)
             (pures T B β-script F T Q.table ρ β l k) x := by
  let U := P.L
  let y t:= betaF G t U
  by_cases h₀ : 0 < (M.tables b P).gap
  swap
  · refine ⟨fun _=>0, Rate.const _,Eventually.of_forall fun t c f S T F hp ht l B B' hx hq ha hB h𝒦=> False.elim ?_⟩
    subst K; subst P; subst b
    exact h₀ (M.receipt F l h𝒦 hq.large rfl rfl).1.pos_m
  obtain ⟨d,hd,hD⟩:= reaches Q o P M b' b g hv R T a hA (by omega)
  let f t:= pam (j+1+2) Q.table b P M (g t) (g t) R (ConnectedActivityE6.loopBill G L t)
  have hF : Rate G U 0 f:= (posts U P Q.table b M R hv).1
  let twist:= ((M₀).gap/2)⁻¹; have hc : 0<twist:= inv_pos.mpr (half_pos h₀)
  obtain ⟨X,hX,hY⟩:= languid (C:=C) (σ:=σ) (K:=K) Q.table Q.table_exists (M₀) j d (e-1) hF hv hd h₀
  obtain ⟨H,hH,h'⟩:= prism G P.L j k g hv hF vow_ok (edge G U) hd hc (by omega) (e-1)
  let B t:= price j (f t); have hB : Rate G U 0 B:= lumpRate j (((Rate.const 1).add hF).add ((Rate.const 1).add hF)) hF
  let Y t:= Real.rpow (y t) (e-1); have hp := ((Rate.power (G:=G) («L»:=U) (a:=e-1)).add Rate.power) e (by linarith)
  let S t:= |H t|+ 2*B t+ f t
  refine ⟨S,(Brim.absolut hH).add (hB.mul_left 2)|>.add hF,?_⟩
  -- H may be negative (property existential) at a given t, so `S` not ≥... need abs H. edit
  filter_upwards [hD,hY,h',hp] with t hD hY hT hJ A Y' c f' S' T F' hp ht l B' B'' hβ' hQ hk' hτ hC Λ he ρ hρ hK β p D X' hK' he' hm hh' x hν hΞ r hx hr
  have hβ:= D.laws.intake
  subst K; subst P; subst b; subst b'
  let g':=gStep β; let A':=M.tables T.high S'.patch; have hy:0< y t:= zero_lt_one.trans hβ.height
  have hb: 0<β:=hβ.positive
  have hS:0<r:= lt_of_lt_of_le (Fare.gS _ hb).1 (le_trans (le_abs_self _) ((norm_fst_le _).trans hx))
  have hp' := hD c f' S' T F' rfl rfl hQ rfl rfl hC Λ he ρ hρ hK l
  have hρ: M.Service F' T.high T.up ρ:= hρ
  have Hv := hp' X' hK' he' hm B' B'' p β D hβ' hh' x hν ((norm_snd_le _).trans_lt (hx.trans_lt hr))
  obtain ⟨hφ, hg, -⟩:= hY c f' S' T F' M B' β ρ l T' x hQ rfl rfl rfl hΞ hβ hC hρ Hv
  let N:= Lapis.gram F' T.up T.high ρ l; have hv' (v) : dotProduct v ((N 0)⁻¹ *ᵥ v) ≤ ((A'.gap/2)⁻¹)*dotProduct v v:= wakes F' l T.up T.high ρ σ C (ConnectedActivityE6.loopBill G U t) M hQ.large hC hρ 0 (norm_zero.trans_lt (Hv.1.pos.trans_le Hv.2.2.1)) |>.2.2.1 v
  have He:= hT _ _ _ _ _ _ (countsK F' (g t) hQ.overall) (golf_less Hv.1 (show j≤j+1+2 by omega)) hv' _ r hx hr hS
  have hk:= poem F' T Q.table ρ β l Hv.1 B' hk (by omega) hb hx hr hg He
  refine ⟨hφ, hk.climb ?_ le_rfl⟩
  -- regroup exact coefficient/cost (use abs H)
  change Y t+β*(B t*r^(k+3))+(B t+f t)*r^(k+1)+(H t * r^(k+1)+Y t)≤_
  have h':0 ≤ B t:= (Vote.cl (c:=1) j (show 0 ≤ 1+f t+(1+f t) from (by have H : 0≤f t:=golf_cost Hv.1; positivity)) (show 0 ≤ f t from golf_cost Hv.1) le_rfl).1
  have hp:β ≤2*y t:= hβ.window.2
  have hh : Y t+Y t≤ (y t)^e:= (le_abs_self _).trans hJ
  exact regroup hS.le hy.le hp h' hh (H t) (show 0 ≤ f t from golf_cost Hv.1)


end YM.AllOrder.Local.Pure
