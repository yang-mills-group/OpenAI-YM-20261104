import YM.AveragedStep.Moments.Cup
/-! Use on any error with local-power estimates (following further re-poses,
ensure any moved derivative indices still belong to this demand footprint
and are accounted by `WithinReach`). -/
noncomputable section
set_option autoImplicit false
namespace YM.AveragedStep
open Lattice RG Precision MeasureTheory Function Filter Tree Loops Wilson Set Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius ENNReal Classical ContDiff
variable {c f:Side}{G:Gauge} {S:StepData c f} (F:Forest S.ratio) (x:Site c)
structure WithinReach (d:ℕ)(R:ℝ)(D:Finset (Rim c f)):Prop where
 mass:D.card ≤ d
 price:0 ≤ R
 pays i:i∈D→ (separation (S.ratio.embed x) (atRim S i):ℝ) ≤ R
def CoverHit (D:Finset (Rim c f))(δ:ℝ)(z:TopologyQ F G): Prop:= ∃ i∈D,δ ≤ G.chord (aboard F x z i)
lemma hit_pay {D:Finset (Rim c f)}{δ:ℝ}{z:TopologyQ F G}(H : CoverHit F x D δ z)(τ:ℝ)(ht : 0≤τ): τ*δ ≤ cup F x τ D z:=by
 obtain ⟨i,hi,h⟩:=H; exact (mul_le_mul_of_nonneg_left h ht).trans (cup_take F x τ ht hi z)
variable (hS:S.patch.Branches S.kernel G)
include hS
lemma report_sum {I:Type*}(s:Finset I){β:ℝ}(u:I→TopologyQ F G→ℝ)(hu:∀ i∈s,Envelope (u i)):
    report F β x (fun z=>∑ i∈s,u i z)=∑ i∈s,report F β x (u i):=by
 unfold report; simp_rw [Finset.mul_sum,integral_finsetSum _ (fun i hi => ((assay_env F x hS β).mul (hu i hi)).integrable
   ((F.order G).prod (prior G c))), Finset.mul_sum]
lemma report_add {β:ℝ}{u v: TopologyQ F G→ℝ}(hu:Envelope u)(hv:Envelope v):
  report F β x (u+v)=report F β x u+report F β x v:=by
 unfold report; simp_rw [Pi.add_apply,mul_add,integral_add (((assay_env F x hS β).mul hu).integrable
   ((F.order G).prod (prior G c))) (((assay_env F x hS β).mul hv).integrable ((F.order G).prod (prior G c))),mul_add]
omit F hS x in
lemma spend (G:Gauge) (P:Patch)(K:KernelChoices)(h:P.Branches K G)(a:ℝ)(ha:0<a)(d n m:ℕ){δ:ℝ}(hδ:0<δ):
 ∃ C:ℝ,0≤C∧∀ᶠ τ in atTop, ∀{c f:Side}(S:StepData c f)(F:Forest S.ratio),Window G S τ P K→ ∀ (x:Site c)(D:Finset (Rim c f))(R:ℝ),WithinReach (S:=S) x m R D→ ∀ (Q:TopologyQ F G→ℝ)(B:ℝ), Envelope Q → 0≤B → (∀ z,|Q z| ≤ B*cup F x τ D z^n) →
   |report F (τ^2) x Q| ≤ B*C*lag τ^(n+d)*Real.exp (a*R)∧
   ((∀ z,Q z ≠0→CoverHit F x D δ z)→ |report F (τ^2) x Q| ≤ B*τ⁻¹^d*C*lag τ^(n+d)*Real.exp (a*R)):=by
 obtain ⟨B,hB,H⟩:= cup_price G P K h (n+d) m a ha
 let C:=max B (δ⁻¹^d*B)
 refine ⟨C,hB.trans (le_max_left ..),?_⟩
 filter_upwards [H,eventually_ge_atTop (1:ℝ)] with τ h ht c f S F w x D R hW q V hq hv hh -- shadow h
 let f(y:TopologyQ F G):=cup F x τ D y
 have hl(y):1≤f y:=cup_ge F x τ (zero_le_one.trans ht) D y
 have heS:S.patch.Branches S.kernel G:=by rw [w.shape,w.control]; assumption
 let X:=lag τ^(n+d)*Real.exp (a*R)
 have hT :0<X:=by unfold X; have hi:=lag_ge ht; positivity
 have hs:report F (τ^2) x (fun y=>f y^(n+d)) ≤ B*X:=by rw [show B*X=B*lag τ^(n+d)*Real.exp (a*R) by unfold X; ring]; exact h S F w x D R hW.mass hW.price hW.pays
 have hw(y:ℝ)(hy:0≤y)(h:∀ z,|q z|≤y*f z^(n+d)):|report F (τ^2) x q|≤ y*(B*X):=by
    have hK:= report_dom F x (τ^2) heS hq ((Envelope.const y).mul (env_npow (cup_env F x τ D) _)) h
    refine hK.trans ?_; rw [show report F _ x (fun x=> y*(f x)^(n+d))=y*report F _ _ (fun x=>(f x)^(n+d)) from report_scale F x (τ^2) y (fun x=> f x ^(n+d))]; gcongr
 constructor
 · refine (hw V hv fun z=> (hh z).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hl z) (Nat.le_add_right ..)) hv)).trans ?_
   calc
     _ ≤ V*(C*X):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left ..) hT.le) hv
     _ = _:=by unfold X; ring
 intro hf
 let L:=τ⁻¹^d*δ⁻¹^d
 have hL : 0≤L:=by unfold L; positivity
 refine (hw (V*L) (mul_nonneg hv hL) (fun z=> ?_)).trans ?_
 · by_cases h:q z=0; · rw [h,abs_zero]; have h:=hl z; positivity
   have he:=hit_pay F x (hf z h) τ (zero_le_one.trans ht)
   have hy:1 ≤ L*f z^d:=by
     unfold L; rw [← mul_pow, ← mul_pow]; refine one_le_pow₀ ?_
     rw [mul_comm τ⁻¹,←mul_inv_rev,← div_eq_inv_mul,le_div_iff₀ (by positivity)]; exact le_trans (one_mul _).le he
   rw [mul_assoc,pow_add]; apply (hh z).trans (mul_le_mul_of_nonneg_left _ hv)
   refine (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans (hl _)) _) hy).trans_eq ?_; ring
 · calc
     _= V*τ⁻¹^d*(δ⁻¹^d*B)*X:=by unfold L; ring
     _ ≤ V*τ⁻¹^d*C*X := by unfold C; gcongr; exact le_max_right ..
     _ = _:=by unfold X; ring
end YM.AveragedStep
