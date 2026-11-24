import YM.WilsonCoeffUV.Marked.Capture.AnalyticBound
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Address
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{o:ι}{i j i' j' a e r h N n m b l:ℕ}{G:Gauge}{σ τ u g B C z ρ:ℝ}{E W V' U':Credit}
variable [DecidableEq ι] [Fintype α]

lemma sprig_both (h:o∈S)(x:Cover)(p:0<σ)(j:ℕ) : SumBudget (fun i:Fence α S o j=>exp (-(σ/4)*Syn Bank.terrain (toe S o x i.1) S i.2)) (tiePay Unit (Fintype.card (S.erase o)) (σ/8) * tiePay α j (σ/8)):=by
    let V:= S.erase o; let K:= Fintype.equivFin (↑V); let F:=fun (i:V →Cover)(p:Fin (Fintype.card (S.erase o)))=> ((i (K.symm p),()) : Cloth Unit)
    have hF: Bijective F:=by
        constructor
        · intro p q he; funext i; have h:=congr_arg Prod.fst (congr_fun he (K i)); simpa only [F,Equiv.symm_apply_apply] using h
        intro i; refine ⟨fun j=>(i (K j)).1,?_ ⟩; funext j; apply Prod.ext (by simp [F]) (Subsingleton.elim ..)
    let Z:=Equiv.ofBijective F hF; let c:=Fintype.card (S.erase o); let Q (i : V→ Cover) := sail (σ/8/c) Bank.terrain x (Z i); have hc:0<σ/8:= by linarith
    have hQ:SumBudget Q (tiePay Unit c (σ/8)):=cap_walk _ _ Z.symm (fun i=> by unfold Q; rw [Z.apply_symm_apply]) (sprigS hc _)
    let T:=sprigS (p:=x) (α:=α) hc j
    refine budget_minor (prod_cap hQ (by exact T.2.2.trans' (tsum_nonneg (T.1))) fun _=>T) (fun _=>by positivity) fun i=> sandCW h x i p

def axleP (W:Credit)(r:ℕ):= Credit.leanC.usingC W |>.prodC (pur (1+4*r:ℝ)) |>.powC r
lemma axleS (W:Credit)(r:ℕ)(x:ℝ)(h:1≤x): (1+4*r*W.buy x)^r ≤ (axleP W r).buy x:=by
    simp only [axleP,Credit.power,Credit.products,Credit.stock_up,Credit.lean_cost]; have hz:=W.purchase h
    refine pow_le_pow_left₀ (by positivity) ?_ r; apply le_trans _ (mul_le_mul_of_nonneg_left (pure_goal _ _) (zero_le_one.trans hz)); linarith

def riding (α:Type)[Fintype α](j r:ℕ)(S:Finset ι)(o:ι)(W:Credit): Credit:=
    let A:= (pur 2).prodC W
    ((pur ((1+2*S.card+j:ℝ)^r)).prodC (axleP W r)).prodC (((billingQ Unit (Fintype.card (S.erase o)) 0).usingC A).prodC ((billingQ α j 0).usingC A))
lemma gaugeS (h:σ⁻¹≤ W.buy z)(t:1≤z)(v:0<σ)(r:ℕ) : (1+2*S.card+j:ℝ)^r*(1+4*r*W.buy z)^r*(tiePay Unit (Fintype.card (S.erase o)) (σ/8)*tiePay α j (σ/8))≤ (riding α j r S o W).buy z:=by
   set u:= (1+2*S.card+j:ℝ)^r; have hu:0≤u:=by unfold u; positivity
   let A:= (pur 2).prodC W
   have hP:1≤W.buy z:=W.purchase t; have he:2*W.buy z ≤ A.buy z:=by unfold A; rw [Credit.products]; exact mul_le_mul_of_nonneg_right (pure_goal ..) (zero_le_one.trans hP)
   have ht {β:Type}[Fintype β] j:tiePay β j (σ/8) ≤ ((billingQ β j 0).usingC A).buy z:=by
      rw [Credit.stock_up]; have hz:(1:ℝ) ≤ 2*W.buy z:=by linarith
      exact ((snuff v h).trans (offer_expands hz)).trans ((billingQ β j 0).elder hz he)
   have hs:0 < σ/8:= by linarith
   rw [riding,Credit.products, Credit.products,Credit.products]; refine mul_le_mul (mul_le_mul (pure_goal ..) (axleS W r z t) (by positivity) (hu.trans (pure_goal ..))) (mul_le_mul (ht _) (ht _) (tie_non hs) ((tie_non hs).trans (ht (β:=Unit) _))) (mul_nonneg (tie_non hs) (tie_non hs)) (mul_nonneg (hu.trans (pure_goal ..)) (zero_le_one.trans (Credit.purchase _ t)))
lemma directV (S:Finset ι)(p:o∈S)(P:(ι→Cover) → Ten (Pen D S) (Cloth α) j)(h:∀ i,Wig Bank.terrain i σ B S (P i))(u:σ⁻¹ ≤ W.buy z)(e:0<σ)(v:1≤z)(r:ℕ): PostMark S o j P (σ/2) (B*(riding α j r S o W).buy z) r:=by
   intro x; choose μ hμ hf hx f using fun i:Fence α S o j=> voucher S (towerV S o j P x i); refine ⟨μ,fun i=>⟨hμ i,hf i⟩,f,?_⟩; simp_rw [hx]; let C:= (1+2*S.card+j:ℝ); let w:= W.buy z; let Z:=(1+4*r*w)^r; have hw:1≤w:= Credit.purchase W v
   have hB:0≤B:=(h (fun _=>0)).1; have hC:0≤C:=by unfold C; positivity
   have hZ:0≤Z:=by unfold Z; positivity
   let G (i:Fence α S o j):= lineOut (toe S o x i.1) S o i.2 ^r * exp (σ/2*Syn Bank.terrain (toe S o x i.1) S i.2)*‖towerV S o j P x i‖
   have he:SumBudget G (B*C^r*Z*(tiePay Unit (Fintype.card (S.erase o)) (σ/8)*tiePay α j (σ/8))):=by
       refine budget_minor (cap_scale (sprig_both (α:=α) p x e j) (show 0≤ B*C^r*Z by positivity)) (f:=G) ?_ ?_
       · intro i; unfold G; have hh:1≤ lineOut (toe S o x i.1) S o i.2:= (lineBound p i.2).1; positivity
       intro i
       let y:=toe S o x i.1; have hh:=lineBound (p:=y) p i.2; let t:= Syn Bank.terrain y S i.2
       have hy: lineOut y S o i.2 ^ r ≤ C^r*(Z*exp (σ/4*t)):=by
           apply le_trans (pow_le_pow_left₀ (zero_le_one.trans hh.1) hh.2 _); rw [mul_pow]; apply mul_le_mul_of_nonneg_left (ember e u _ _) (pow_nonneg hC _)
       change lineOut y S o i.2^r*_* ‖P y i.2‖ ≤ _; refine (mul_le_mul (mul_le_mul_of_nonneg_right hy (by positivity)) ((h y).2 i.2) (norm_nonneg _) (by positivity)).trans_eq ?_; change _=B*C^r*Z *exp (-(σ/4)*t); rw [show -(σ/4)*t=(σ/4*t+σ/2*t)+ -σ*t by ring, exp_add, exp_add]; unfold t y; ring
   refine ⟨he.1,he.2.1,le_trans he.2.2 (le_trans ?_ (mul_le_mul_of_nonneg_left (gaugeS (α:=α) (o:=o) u v e r) hB))⟩; unfold C Z w; exact le_of_eq (by ring)
end YM.WilsonCoeffUV.Wheel.Address
