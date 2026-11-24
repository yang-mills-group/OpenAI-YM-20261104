import YM.FVA2.Gen.Pack
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
/-!
 # Polynomial orders and operations at zero (classical comparison helpers)
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Topology
open scoped ContDiff BigOperators Classical
variable {E F H : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup H][NormedSpace ℝ H] {p q f g : ℝ→ E} {a b :ℝ→F}{n k m:ℕ}
/-- \[d\]-jet, *through* indicated inclusive height. -/
def Near (n:ℕ)(p q:ℝ→ E): Prop:= ∀ k≤n, iteratedDeriv k p 0=iteratedDeriv k q 0
@[refl] lemma Near.rise : Near n p p:=fun _ _=>rfl
@[symm] lemma Near.turn (u:Near n p q): Near n q p:=fun i h=>( u i h ).symm
lemma Near.across (u:Near n p q)(v:Near n q g): Near n p g:= fun i h=>(u i h).trans (v i h)
lemma Near.here (u:Near n p q): p 0=q 0:=by simpa using u 0 (Nat.zero_le _)
@[simp] lemma near_first : Near 0 p q ↔ p 0=q 0:= by constructor; exact Near.here; intro h i hi; simpa [show i=0 by omega] using h
lemma Near.low (u:Near n p q)(v:k≤n): Near k p q:=fun _ w=>u _ (w.trans v)
lemma Near.taller (u:Near n p q)(h:iteratedDeriv (n+1) p 0=iteratedDeriv (n+1) q 0): Near (n+1) p q:=fun i w=> by obtain rfl|H:=w.eq_or_lt; exact h; exact u i (by omega)
lemma Near.add (u:Near n p q)(v:Near n f g)(hp:ContDiffAt ℝ ∞ p 0)(hq:ContDiffAt ℝ ∞ q 0)(hf:ContDiffAt ℝ ∞ f 0)(hg:ContDiffAt ℝ ∞ g 0): Near n (p+f) (q+g) :=by
    intro i hi; have he:(i:WithTop ℕ∞)≤∞:=WithTop.coe_le_coe.mpr le_top
    rw [ iteratedDeriv_add (hp.of_le he) (hf.of_le he), iteratedDeriv_add (hq.of_le he) (hg.of_le he),u i hi,v i hi]
lemma Near.neg (u:Near n p q): Near n (-p) (-q):=fun i hi=>by rw [ iteratedDeriv_neg, iteratedDeriv_neg,u i hi ]
lemma near_of_ev (u:p=ᶠ[𝓝 0]q):Near n p q:=fun i _=> u.iteratedDeriv_eq i
variable (n k) in
lemma iterL {x:ℝ}(hp:ContDiffAt ℝ ∞ p x)(L:E→L[ℝ]H): iteratedDeriv k (L ∘ p) x=L (iteratedDeriv k p x):= by unfold iteratedDeriv; rw [ L.iteratedFDeriv_comp_left hp ( WithTop.coe_le_coe.mpr le_top ) ]; rfl
lemma Near.box (u:Near n p q)(v:Near n a b)(hp:ContDiffAt ℝ ∞ p 0)(hq:ContDiffAt ℝ ∞ q 0)(ha:ContDiffAt ℝ ∞ a 0)(hb:ContDiffAt ℝ ∞ b 0): Near n (fun t=>(p t,a t)) (fun t=>(q t,b t)):= by
    intro i hi; let X:= fun t=>(p t,a t); let Y:= fun t=>(q t,b t); apply Prod.ext; · let L:= ContinuousLinearMap.fst ℝ E F; change L (iteratedDeriv i X 0) = L (iteratedDeriv i Y 0); rw [← iterL i (hp.prodMk ha),← iterL i (hq.prodMk hb)]; exact u i hi
    let L:= ContinuousLinearMap.snd ℝ E F; change L (iteratedDeriv i X 0) = L (iteratedDeriv i Y 0); rw [← iterL i (hp.prodMk ha),← iterL i (hq.prodMk hb)]; exact v i hi
lemma Near.from_each {A:Type*}[Fintype A]{F G:ℝ→ A→ E}(h:∀ x:A,Near n (fun a=> F a x) (fun a=> G a x))(hF:ContDiffAt ℝ ∞ F 0)(hG:ContDiffAt ℝ ∞ G 0): Near n F G:= by
    intro i hi; ext1 u; let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:A=>E) u; change L ( iteratedDeriv i F _)=L ( iteratedDeriv i G _); rw [← iterL i hF,← iterL i hG]; exact h u i hi
variable (u:Near n p q)(hp:ContDiffAt ℝ ∞ p 0)(hq:ContDiffAt ℝ ∞ q 0){ψ:E→F}
theorem Near.vcomp (u:Near n p q)(hp:ContDiffAt ℝ ∞ p 0)(hq:ContDiffAt ℝ ∞ q 0)(h:ContDiffAt ℝ ∞ ψ (p 0)): Near n (ψ∘p) (ψ∘q):= by
    intro i hi; rw [ iteratedDeriv_vcomp_eq_sum_orderedFinpartition h hp (WithTop.coe_le_coe.mpr le_top), iteratedDeriv_vcomp_eq_sum_orderedFinpartition ( u.here ▸ h ) hq ( WithTop.coe_le_coe.mpr le_top ), u.here ]; apply Finset.sum_congr rfl; intro c hc; congr! 1; ext1 j; exact u _ ( ( c.partSize_le j ).trans hi )
private lemma smaller (c:OrderedFinpartition n)(i:Fin c.length)(hc:1<c.length): c.partSize i<n:=by
    haveI: Nontrivial (Fin c.length):= Fin.nontrivial_iff_two_le.mpr hc
    let X(j:Fin (c.partSize i)) : (k:Fin c.length) × Fin (c.partSize k):= ⟨i,j⟩ -- notation sigma?
    let L:= c.equivSigma; have hu:= Fintype.card_lt_of_injective_not_surjective (f:=L ∘ X) ( L.injective.comp ?_ ) ?_
    · simpa only [Fintype.card_fin] using hu
    · exact fun {_ _} h=> eq_of_heq (Sigma.mk.inj_iff.mp (show Sigma.mk _ _= Sigma.mk _ _ from h)).2
    obtain ⟨w,hw⟩:= exists_ne i; intro v; let j:Fin (c.partSize w):=⟨0,c.partSize_pos _⟩; obtain ⟨p,hp⟩:=v (L ⟨w,j⟩); exact hw (congrArg Sigma.fst (L.injective (show L ⟨i,p⟩=L ⟨w,j⟩ from hp)).symm)
private lemma iter_one_n {k:ℕ}{x:E}(h:k=1)(he:fderiv ℝ ψ x=0)(w:Fin k→E): iteratedFDeriv ℝ k ψ x w=0:= by subst k; rw [iteratedFDeriv_one_apply, he]; rfl
include u hp hq
private lemma fat_zero (h:ContDiffAt ℝ ∞ ψ (p 0))(hk:fderiv ℝ ψ (p 0)=0): iteratedDeriv (n+1) (ψ∘p) 0=iteratedDeriv (n+1) (ψ∘q) 0:= by
    rw [ iteratedDeriv_vcomp_eq_sum_orderedFinpartition h hp (WithTop.coe_le_coe.mpr le_top), iteratedDeriv_vcomp_eq_sum_orderedFinpartition ( u.here ▸ h ) hq ( WithTop.coe_le_coe.mpr le_top ), ← u.here ]; apply Finset.sum_congr rfl; intro c hc
    obtain he|he:= (show 1≤ c.length from c.length_pos (Nat.succ_pos _)).eq_or_lt
    · rw [ iter_one_n he.symm hk,iter_one_n he.symm hk]
    congr! 1; ext1 w; apply u _; have h' := smaller c w he; omega
theorem ahead (h:ContDiffAt ℝ ∞ ψ (p 0)): iteratedDeriv (n+1) (ψ∘p) 0-iteratedDeriv (n+1) (ψ∘q) 0 = fderiv ℝ ψ (p 0) (iteratedDeriv (n+1) p 0-iteratedDeriv (n+1) q 0):= by
    let L:= fderiv ℝ ψ (p 0); have ht: ContDiffAt ℝ ∞ ψ (q 0):= u.here ▸ h; have he:(↑(n+1:ℕ):WithTop ℕ∞)≤∞:= WithTop.coe_le_coe.mpr le_top; change _=L _; rw [ map_sub, ← iterL (n+1) hp L, ← iterL (n+1) hq L ]; apply sub_eq_zero.mp; rw [ show ∀ a b c d:F,a-b-(c-d)=a-c-(b-d) from fun _ _ _ _=>by abel, ← iteratedDeriv_sub (( h.comp _ hp ).of_le he) (( L.contDiff.contDiffAt.comp _ hp ).of_le he), ← iteratedDeriv_sub (( ht.comp _ hq ).of_le he) (( L.contDiff.contDiffAt.comp _ hq ).of_le he) ]; refine sub_eq_zero.mpr (fat_zero (ψ:=ψ- ⇑L) u hp hq (h.sub L.contDiff.contDiffAt) ?_); rw [fderiv_sub (h.differentiableAt (by simp)) L.differentiableAt,L.fderiv]; exact sub_self _
omit u hp hq
-- Scalar powers special utility
lemma lift_symbol (i j:ℕ){x:E}: iteratedDeriv j (fun t:ℝ=> t^i • x) 0= if j=i then (j.factorial:ℝ) •x else 0:= by rw [ iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_fun_pow_zero ]; by_cases he:j=i<;> simp [he]
-- at_cost.Fact.Pow
lemma charge_pay (i:ℕ)(x:E): Near i (fun t:ℝ=> t^(i+1) • x) 0:=fun j hj=>by rw [lift_symbol,if_neg (by omega), iteratedDeriv_const_zero]
lemma iter_weight (hp:ContDiffAt ℝ ∞ p 0)(n:ℕ): iteratedDeriv (n+1) (fun t:ℝ=> t • p t) 0=((n+1:ℕ):ℝ) • iteratedDeriv n p 0:= by
    -- via product rule within
    change iteratedDeriv (n+1) ((fun x:ℝ=>x) • p) 0=_; simp_rw [← iteratedDerivWithin_univ]; rw [ iteratedDerivWithin_smul (f:=fun x=>x) (Set.mem_univ _) uniqueDiffOn_univ (contDiffWithinAt_id) ((hp.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt) ]; simp_rw [ iteratedDerivWithin_univ, iteratedDeriv_fun_id_zero ]; rw [ Finset.sum_eq_single_of_mem 1 ( Finset.mem_range.mpr (by omega) ) (fun x hx h=> by simp [h]) ]; simp [-Nat.cast_add,Nat.cast_smul_eq_nsmul]
lemma Near.weight (u:Near n p q)(hp:ContDiffAt ℝ ∞ p 0)(hq:ContDiffAt ℝ ∞ q 0): Near (n+1) (fun t=> t • p t) (fun t=> t • q t):= by
    intro i hi; cases i with| zero=> simp| succ i=> rw [iter_weight hp, iter_weight hq,u i (by omega)]
end YM.FVA2.Gen
