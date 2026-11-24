import YM.OPE.Compatible.Grotto.Flags
/-!
# Families.Wealth coordinates for Hexes and Reader Lines
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics Drift
open scoped Topology BigOperators Classical
variable {E F M J:Type}[NormedAddCommGroup E][NormedAddCommGroup F] {r x b c t q:ℝ}
variable {p Q:M→ℝ}{a f:M→E}
lemma normDig {u:M→ F}(h:Wealth a p Q)(hp:∀ i,‖u i‖≤ ‖a i‖): Wealth u p Q:=by obtain ⟨c,hc,k,H⟩:=h; exact ⟨c,hc,k,fun i=> (hp i).trans (H i)⟩
lemma normW (h:Wealth a p Q) : Wealth (fun i=>‖a i‖) p Q:= normDig h (fun i=>by rw [Real.norm_of_nonneg (norm_nonneg (a i))]) -- maybe lhs lambda
lemma scaleD {k:ℝ}[NormedSpace ℝ E](h: Wealth a p Q): Wealth (fun i=> k • a i) p Q:=by
    obtain ⟨c,hc,d,H⟩:=h; refine ⟨‖k‖*c,mul_nonneg (norm_nonneg k) hc,d,fun i=>?_⟩; rw [norm_smul]; apply (mul_le_mul_of_nonneg_left (H i) (norm_nonneg _)).trans_eq; ring
lemma walletZero (E:Type)[NormedAddCommGroup E](p Q:M→ℝ): Wealth (0:M→ E) p Q:= wealthZ p Q
lemma anthW (hp:1≤ p)(hz:0 ≤ Q)(h: Wealth a p Q)(he: Wealth f p Q): Wealth (fun i=> a i+f i) p Q:= fortSum h he hp hz
lemma subW (hp:1≤ p)(hz:0 ≤ Q)(h: Wealth a p Q)(he: Wealth f p Q): Wealth (a-f) p Q:= (show a+-f=a-f from (sub_eq_add_neg a f).symm) ▸ (fortSum h (fortNeg he) hp hz)
lemma aimW [NormedSpace ℝ E][NormedSpace ℝ F](R:E→L[ℝ] F)(h:Wealth a p Q): Wealth (fun i=>R (a i)) p Q:=by obtain ⟨c,hc,k,H⟩:=h; refine ⟨‖R‖*c,mul_nonneg (norm_nonneg _) hc,k,fun i=>?_⟩; exact (le_opNorm ..).trans ((mul_le_mul_of_nonneg_left (H i) (norm_nonneg _)).trans_eq (by ring))
def TameP (r:ℝ)(p Q:M→ℝ)(f:M→ℕ→E):Prop:=∃ b:M→ℝ, Wealth b p Q ∧ ∀ i, Hex r (f i) (b i)
lemma zeroP (p Q:M→ℝ)(r:ℝ): TameP r p Q (0:M→ℕ→E):= ⟨0,wealthZ p Q,fun _=> Hex.zero E r ⟩
section
variable {f g:M→ℕ→ E}
lemma TameP.plus (ht:1 ≤ p)(hq:0≤ Q)(h:TameP r p Q f)(he:TameP r p Q g): TameP r p Q (f+g):=by obtain ⟨a,ha,hF⟩:=h; obtain ⟨b,hb,hB⟩:=he; exact ⟨a+b,fortSum ha hb ht hq, fun i=> (hF i).add (hB i)⟩
lemma TameP.sub (ht:1 ≤ p)(hq:0≤ Q)(h:TameP r p Q f)(he:TameP r p Q g): TameP r p Q (f-g):=by obtain ⟨a,ha,hF⟩:=h; obtain ⟨b,hb,hB⟩:=he; exact ⟨a+b,fortSum ha hb ht hq, fun i=> (hF i).sub (hB i)⟩
lemma TameP.place (h:TameP r p Q f)(n:ℕ): Wealth (fun i=>f i n) p Q:=by obtain ⟨a,ha,hB⟩:=h; apply normDig (scaleD (k:=r^n) ha); intro i; rw [smul_eq_mul, Real.norm_eq_abs]; exact (hB i n).trans ((mul_comm _ _).le.trans (le_abs_self _)) -- lambda
lemma TameP.cast [NormedSpace ℝ E][NormedSpace ℝ F](T:E→L[ℝ] F)(h:TameP r p Q f): TameP r p Q (fun i n=> T (f i n)):=by obtain ⟨a,ha,hF⟩:=h; exact ⟨fun i=>‖T‖*a i,scaleD ha,fun i=>(hF i).invoke T⟩
lemma TameP.grows (h:TameP r p Q f)(hp:0 ≤ r)(ht:r≤ t): TameP t p Q f:=by obtain ⟨a,ha,hF⟩:=h; exact ⟨a,ha,fun i=> (hF i).warm hp ht⟩
lemma TameP.byOp [NormedSpace ℝ E] {A:M→ℕ→ E→L[ℝ] E}(hx:TameP r p Q f)(hp:TameP b p 1 A): TameP (r*b) p Q (fun i n=> A i n (f i n)):=by
     obtain ⟨a,ha,H⟩:=hx; obtain ⟨c,hc,K⟩:=hp; refine ⟨a*c, show Wealth (a*c) p Q from mul_one Q ▸ wealth_mul ha hc ?_,fun i=> (H i).acts (K i)⟩; intro i; exact le_of_eq (norm_mul ..)
lemma TameP.set (s:Finset J)(f:J→M→ℕ→E)(hp:1≤ p)(ht:0 ≤ Q)(h:∀ i∈s,TameP r p Q (f i)): TameP r p Q (∑ i∈ s,f i):=by
    induction s using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zeroP p Q _ | insert j t hj ih=> rw [Finset.sum_insert hj]; apply TameP.plus hp ht (h _ (Finset.mem_insert_self ..)) (ih fun i hi=> h _ (Finset.mem_insert_of_mem hi))
end
end YM.OPE.Hark
