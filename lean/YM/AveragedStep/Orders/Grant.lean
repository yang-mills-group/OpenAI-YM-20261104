import YM.AveragedStep.Orders.Exact
/-! # One-step Wilson PLANT (posterior/local all-degree named Taylor bill)

Use with a bounded multiplier of the remaining *coarse* V, without any
separation assumptions on the listed stencil-link positions and uniformly
in all admissible periods. Propagate through Hessian recurrence after this;
the Grant is shown before charging that and any stencil/compiler/inversion costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {k d:ℕ} {G: Gauge}{P:Patch}{K:KernelChoices}{A:ChartRatio G}
variable {Q:Cuff P K A} {B D δ:ℝ}(H:Cadence Q B D δ)
variable {c f:Side}{S:StepData c f} (F:Forest S.ratio)(x:Site c)
private lemma exact_reads {Q:Cuff S.patch S.kernel A}(hA:LocalRatio A)(hS:S.patch.Branches S.kernel G)
    (w:List (Ink G c f))(l:F.Free)(i:G.ColorIndex)(d:ℕ)(τ:ℝ){u:Config G c→ℝ}(hu:Envelope u): let j:=fieldKey F l i
    report F (τ^2) x (fun z=>u z.2*arbor F Q x l i w d τ z) + report F (τ^2) x (fun z=>u z.2*tub F Q x l i w d τ z) =
    -report F (τ^2) x (fun z=>u z.2*vice (S:=S) (A:=A) τ⁻¹ j w d (hands F Q x τ z)):=by
 intro j
 let V(z:TopologyQ F G):=u z.2* vice (S:=S) (A:=A) τ⁻¹ j w d (hands F Q x τ z)
 let U:=fun z:TopologyQ F G=> u z.2; let A'(z:TopologyQ F G):=U z* sdEq F Q x (mon w) l (fingers G i) τ z
 let R:= report F (G:=G) (τ^2) x
 have hU:Envelope U:=env_comp hu measurable_snd
 obtain ⟨hv,hW⟩:=pair_safe F Q x l i w d τ hA
 have hV : Envelope V:= hU.mul (vice_env F Q w x j d τ)
 have hF : Envelope A':= hU.mul (sd_safe F Q x (mon w) (mon_cont _) l (fingers G i) τ hA)
 rw [← report_add F x (β:=τ^2) hS (hU.mul hW) (hU.mul hv)]
 change R _= -R V
 have he:R A'=0:=paired_balance F Q x (mon_cont _) l (fingers G i) τ hA hS hu
 have hg: report F (τ^2) x (-V) = -1*R V:=by rw [← neg_one_smul ℝ V]; exact report_scale F x (τ^2) (-1) V
 have hz : R (τ⁻¹ • A')=τ⁻¹*R A':=report_scale F x (τ^2) τ⁻¹ A'
 convert! (show R (τ⁻¹ • A'+(-V))= -R V from (report_add F x (β:=τ^2) hS ((Envelope.const _).mul hF) hV.neg).trans (by change R (τ⁻¹ • A') + report F (τ^2) x (-V) = -R V; rw [hz,hg,he]; ring)) using 2
 ext z; unfold arbor; change u z.2* (τ⁻¹*_ -_-_) + u z.2*_=τ⁻¹* A' z+ -V z; unfold A' V U j; ring

omit F x in
include H in
lemma by_plant (hA:LocalRatio A)(h:P.Branches K G) (i:G.ColorIndex)(k d:ℕ)(a:ℝ)(ha:0<a):
    let n:=2*k+2*d+6
    ∃ W:ℝ,0≤W∧∀ᶠ τ:ℝ in atTop,∀{c f:Side}(S:StepData c f)(F:Forest S.ratio)(hP:S.patch=P)(hK:S.kernel=K), Window G S τ P K→∀ (w:List (Ink G c f)),w.length=k→∀ (x:Site c)(j:F.Free)(u:Config G c→ℝ),Envelope u→(∀ p, |u p|≤1)→
      let q:Cuff S.patch S.kernel A:=hP.symm ▸ hK.symm ▸ Q
      |report F (τ^2) x (fun z=>u z.2*vice (S:=S) (A:=A) τ⁻¹ (fieldKey F j i) w d (hands F q x τ z))| ≤ W* τ⁻¹^(d+1) * lag τ^(n+(d+1))*Real.exp (a*tolls (S:=S) x (Sum.inl j.val) w):=by
 intro n
 let m:=cap (2*aperture P) rimCount+k
 obtain ⟨X,HX,hb⟩:=labor H hA h i k d
 obtain ⟨C,hC,HC⟩:=spend G P K h a ha (d+1) n m H.active
 refine ⟨2*X*C*Real.exp (a*(2*aperture P:ℝ)),by positivity,?_⟩
 filter_upwards [HC,eventually_ge_atTop (1:ℝ)] with τ HC ht
 intro c f S F hP hK hp w hw x j u hU hu q
 subst P K; dsimp only at *
 let U:=fun z:TopologyQ F G=>u z.2
 let D:=aisle (S:=S) (Sum.inl j.val) w
 let R:= tolls (S:=S) x (Sum.inl j.val) w + (2*aperture S.patch:ℝ)
 have hD:WithinReach (S:=S) x m R D :=by
   have he:= aisle_reach (S:=S) x (Sum.inl j.val) w; rw [hw] at he; exact he
 let T:=HC S F hp x D R hD
 have hF:= pair_safe F Q x j i w d τ hA
 have hx:Envelope U:=env_comp hU measurable_snd
 let Z:= lag τ^(n+(d+1))*Real.exp (a*R)
 let J:= τ⁻¹^(d+1)
 have hv:0≤J:=by unfold J; positivity
 let X1(p:TopologyQ F G):=U p*tub F Q x j i w d τ p; let X2(p:TopologyQ F G):=U p*arbor F Q x j i w d τ p
 have ht1: |report F (τ^2) x X1| ≤ X*J*C*Z:= by
   rw [show X*J*C*Z= X*J*C*lag τ^(n+(d+1))*Real.exp (a*R) by unfold Z; ring]
   exact (T _ X (hx.mul hF.1) HX (fun z=> (abs_mul _ _).le.trans ((mul_le_of_le_one_left (abs_nonneg _) (hu _)).trans ((hb S F rfl rfl w hw x j ht z).1)))).2 (fun z hz=>tub_corner F x j i H w d τ z fun he=>hz (by rw [he,mul_zero]))
 have ht2: |report F (τ^2) x X2| ≤ X*J*C*Z:= by
   rw [show X*J*C*Z= X*J*C*lag τ^(n+(d+1))*Real.exp (a*R) by unfold Z; ring]
   exact (T _ (X*J) (hx.mul hF.2) (mul_nonneg HX hv) (fun z=> (abs_mul _ _).le.trans ((mul_le_of_le_one_left (abs_nonneg _) (hu _)).trans ((hb S F rfl rfl w hw x j ht z).2)))).1
 have he:report F (τ^2) x X2+report F (τ^2) x X1= _:=exact_reads (Q:=Q) F x hA h w j i d τ hU
 rw [← abs_neg, ← he]; refine (abs_add_le ..).trans ((add_le_add ht2 ht1).trans_eq ?_)
 unfold Z J R n; rw [mul_add,Real.exp_add]; ring
end YM.AveragedStep
