import YM.AllOrder.Ker.Quotes
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ker.Start
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function
open Next.Fluctuations Gauge Tree Pressure
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m : Side}{k N:ℕ}
local notation "T[" n "]" => (trees P K n)
local notation "S[" n "]" => (dock P K n)
abbrev rr (P:Patch)(n:Side) : (below P n).val=n.val*P.L.val :=  rfl -- notation? proof
abbrev Lacing (n m:Side) (N :ℕ) := Lace (rr P n) (rr P m) N
local notation "X[" n "]"=> Positions (Joint (trees P K n) G)
-- native counted lightly. All labels frozen common branch (changes separately stationary). keep Jacobian gain dependent only on O. Allows all. exported bonuses separate.
def classicalT (R:PathData G)(p:Clip) (n:Side): X[n]→ℝ := priced T[n] (label S[n]) p R
def thermalT (R:PathData G)(n:Side): X[n]→ℝ := Precision.loop R ∘ fine G T[n]
def jacT (O:ChartRatio G)(n:Side): X[n]→ℝ := Liquid.bead (B := T[n]) O

lemma thermo_walks (R:PathData G)(W:Lacing P n m N) (x:X[n]): thermalT P K R m (x ∘ (walks P K W).bores)= N*thermalT P K R n x :=  by
  unfold thermalT; simp only [comp_apply]; apply (congr_arg (Precision.loop R) ((walks P K W).governs x)).trans
  unfold Precision.loop Patch.average; dsimp [Function.comp]; simp_rw [W.high.signed]; simp_rw [Window.unc]; rw [← Finset.mul_sum]; ring_nf; rfl -- direction sum factor
lemma jac_walks (O:ChartRatio G)(W:Lacing P n m N)(x:X[n]): jacT P K O m (x ∘ (walks P K W).bores)= N*jacT P K O n x := by
  let a: T[m].Free→T[n].Free :=  (walks P K W).limb; let b(j:T[n].Free) :=  Liquid.droplet j x; have hx :=  multiplied a ((walks P K W).trees _) (fun j:T[n].Free=> Real.log (O.J (b j))); unfold jacT Liquid.bead; dsimp [Function.comp_apply]; rw [nsmul_eq_mul] at hx; exact hx

variable (R:PathData G)(p:Clip) (O:ChartRatio G) {a C D Λ:ℝ}{L:ℕ}
variable (Q: Push.Uniform.Before G a C P.J K L)(h:R.Bounds p a C Λ)(hO:LocalRatio O)
-- nonnative radius purchases. Want strict. Supply cap using non-normalized Q.
def revenue (Q: Push.Uniform.Before G a C P.J K L)(k:ℕ) :=  let Y :=  Q.tables p P; Y.value*Real.exp (Y.width*k) * boltC k Y.width
include Q h
lemma class_pay (hB:P.Branches K G)(hk:k+1≤L) : let Y := Q.tables p P; ∃ F:Fan (Lobby P K G) (Lobby P K G) k, Cap F (small_a Y.width) (revenue P K p Q k) ∧ ∀ n, Ad G P K n→ billed P K (classicalT P K R p) k n=pieces F n := by
   let I := Ad G P K; let f := classicalT P K R p; have hs n (hi:I n) :=  (Q.receipt T[n] (label S[n]) h hi rfl rfl).1; intro Y; obtain ⟨d,H⟩ := dock_larger P K hB; let c:Side := ⟨d+1,by omega⟩; have h0 :=  hs c (H c (by show d ≤ d+1; omega));
   have ha (n:Side)(hn:I n) :=  (hs n hn).born _ (mem_ball_self (x := 0) (hs n hn).pos_r); -- field name?
   let hZ :=  billed_keeps P K I f (fun _ h=>enough P K h) (fun N n m W _ _ x=> (walks P K W).appraisal K x (label _) p R) (fun n hn=>(ha n hn).1) k
   exact obtain_fan ⟨d,H⟩ hZ (fun n hn=> seat_cost P K I f (fun _ h=>enough P K h) (fun n hn=>(ha n hn).1) h0.pos_a.le h0.pos_C.le _ k hk hn (ha n hn).2) h0.pos_a (mul_nonneg h0.pos_C.le (Real.exp_pos _).le)

-- Loop bounds term. Don't swallow Λ. coordinates
local notation "Y"=>Q.tables p P
def orbC (Q:Push.Uniform.Before G a C P.J K L) (B:ℝ)  :=  B*atomCost G Q.Z a L 2 * countCost (entryWidth L P.L a/2)
lemma thermo_cost (n:Side): ContDiffAt ℝ ω (thermalT P K R n) 0 ∧ Scatter (address T[n] G) (Y).width L (thermalT P K R n) 0 (orbC P K Q Λ)  :=  by
   let X :=  X[n]; let A(s:Signed) (i : Site (below P n)) (z:X)  :=  ∑' j,(R.loop j).unmasked (signedFine T[n] z s) i
   have hp: PaintSupply G L Q.Z :=  ⟨Q.labels.1, fun x hx => (Q.labels.2 x hx).order (Nat.le_succ L)⟩
   let Y' := Y; have hc(s i): ContDiffAt ℝ ω (A s i) 0 :=  Push.Uniform.label_analytic _ _ h.width h.two s hp i 0 (mem_ball_self zero_lt_one)
   have H0:0 ≤ Λ :=  (tsum_nonneg h.two.1).trans h.two.2.2; -- terms
   have ha : 0 < entryWidth L P.L a :=  width_positive h.width ..
   let B (s:Signed) (z:X) := ∑ i,A s i z; have H(s) :=  (ContDiffAt.sum (s := Finset.univ) (fun i _=> hc s i)) -- no let
   have hx(s : Signed): Scatter (address T[n] G) (Y).width L (B s) 0 (orbC P K Q Λ) :=  by
     have hF i  :=  atom_beacon T[n] s h.width h.two hp 0 (mem_ball_self zero_lt_one) i
     have ht : Injective (affine (R := Per (below P n)) s 0)  :=  by intro x y he; unfold affine at he; simpa using congr_arg s⁻¹.act (add_right_cancel he)
     have hu :=  scatter (Multiplicity.injective ht) (hc s) hF ha (mul_nonneg H0 (atomCost_nn hp h.width 2)); rw [Nat.cast_one,mul_one] at hu; exact hu
   let b:ℝ :=  Fintype.card Signed; have hb:0<b := by unfold b; positivity
   have hf:thermalT P K R n=fun z=>b⁻¹ • ∑ s,B s z :=  rfl
   rw [hf]; have hS := ContDiffAt.sum (s := Finset.univ) (fun i _=>H i); have he := (scatter_sum (s := Finset.univ) (fun i _=>H i) (fun i _=> hx i)).smul hS b⁻¹; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_nonneg (inv_pos.mpr hb).le, inv_mul_cancel_left₀ hb.ne'] at he; exact ⟨hS.const_smul _,he⟩
omit Q h
open Liquid
include hO
def jacC (O:ChartRatio G)(N:ℕ):ℝ:= ∑ i∈Finset.range (N+1), ‖(iteratedFDeriv ℝ i (Real.log ∘ O.J) 0)‖
lemma jac_cost (t:ℝ)(n:Side): Scatter (address T[n] G) t N (jacT P K O n) 0 (jacC O N):= by
  let r:= address T[n] G; let F:= Real.log ∘ O.J
  intro k hk s i; let U₀:= iteratedFDeriv ℝ k F 0; let f (q:T[n].Free) (j:Fin k):= droplet q (bolt (s j)); unfold jacT bead; rw [entries_finset (fun j _=> water hO j)];
  have ht q : entry (F ∘ droplet q) 0 s= U₀ (f q):= congr_arg (fun T:ContinuousMultilinearMap ℝ (fun _:Fin k=>X[n]) ℝ => T (fun i=> bolt (s i))) (Next.Foundations.jets_linear _ ((tincture hO).of_le le_top))
  change ‖∑ q:T[n].Free, entry (F∘droplet q) 0 s‖≤ _; simp_rw [ht]; have hc : 0≤jacC O N:= by unfold jacC; positivity
  rcases H:s i with (w|v)
  · rw [Finset.sum_eq_zero ?_,norm_zero]; positivity; intro j _; exact ContinuousMultilinearMap.map_coord_zero U₀ i (by unfold f; rw [H,dry j w]) -- arguments?
  rw [Finset.sum_eq_single_of_mem v.1 (Finset.mem_univ v.1) ?_]; swap; · intro j _ hj; exact ContinuousMultilinearMap.map_coord_zero U₀ i (by unfold f; rw [H,dry' j v hj])
  by_cases hV:∃ j,f v.1 j=0; · obtain ⟨j,hj⟩:=hV; rw [ContinuousMultilinearMap.map_coord_zero U₀ j hj, norm_zero]; positivity
  have he(j:Fin k) : ∃ b:G.ColorIndex,s j=Sum.inr (v.1,b):= by
      rcases h:s j with (x|b)
      · exact (hV ⟨j,(by unfold f; rw [h,dry])⟩).elim
      by_cases hh : v.1=b.1; · exact ⟨b.2, by rw [hh]⟩
      exact (hV ⟨j,(by unfold f; rw [h,dry' v.1 b hh])⟩).elim
  have hx : spanSites r (r (s i)) s=0 := Finset.sum_eq_zero fun j _=> by obtain ⟨x,hx⟩:=he j; rw [hx,H]; exact separation_self _
  rw [H] at hx; unfold r at hx; rw [hx,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]; refine (U₀.le_opNorm _).trans ?_
  simp_rw [(show ∀ j, ‖f v.1 j‖=1 from fun j=> by obtain ⟨q,hq⟩:=he j; unfold f; rw [hq]; exact light (v.1,q)), Finset.prod_const_one,mul_one]; exact Finset.single_le_sum (s:=Finset.range (N+1)) (fun k _ => norm_nonneg (iteratedFDeriv ℝ k F 0)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
include Q h
omit hO in
lemma orbC_ge : 0 ≤ orbC P K Q Λ := by
   have hp: PaintSupply G L Q.Z:= ⟨Q.labels.1, fun x hx=>(Q.labels.2 x hx).order (Nat.le_succ L)⟩
   exact mul_nonneg (mul_nonneg ((tsum_nonneg h.two.1).trans h.two.2.2) (atomCost_nn hp h.width 2)) (count_pos (half_pos (width_positive h.width ..))).le

def shadow (O:ChartRatio G)(R:PathData G) (n:Side): X[n]→ℝ:= thermalT P K R n - jacT P K O n
-- shadowT pure includes jac already price without period.
def revS (Q:Push.Uniform.Before G a C P.J K L)(Λ:ℝ)(k:ℕ):= let Y':=Q.tables p P; (orbC P K Q Λ+jacC O L)*Real.exp (Y'.width*k)*boltC k Y'.width
lemma shadow_pay (hB:P.Branches K G) (hk:k+1 ≤ L) : let Y':=Q.tables p P; 0≤revS P K p O Q Λ k ∧ ∃ F:Fan (Lobby P K G) (Lobby P K G) k, Cap F (small_a Y'.width) (revS P K p O Q Λ k) ∧ ∀ n, Ad G P K n→ billed P K (shadow P K O R) k n=pieces F n:= by
   let I:=Ad G P K; let f:=shadow P K O R; obtain ⟨d,H⟩:= dock_larger P K hB; let c:Side:=⟨d+1,by omega⟩; have h0:= (Q.receipt T[c] (label S[c]) h (H c (by show d≤d+1; omega)) rfl rfl).1; intro Z'; let X':=orbC P K Q Λ+jacC O L
   have hQ(n:Side) : ContDiffAt ℝ ω (f n) 0 ∧ Scatter (address T[n] G) Z'.width L (f n) 0 X':= by
      obtain ⟨ha,hL⟩:=thermo_cost P K R p Q h n; let V:=jacT P K O n; have hb:ContDiffAt ℝ ω V 0:=hydrated hO
      refine ⟨ha.sub hb,?_⟩; have he:= (jac_cost P K O hO (N:=L) Z'.width n).smul hb (-1); have hz:= hL.add ha (hb.const_smul (-1 : ℝ)) he; rw [abs_neg,abs_one,one_mul] at hz; refine (show f n=_ from ?_) ▸ hz;
      funext t; change _-V t=_+(-1:ℝ)•V t; rw [neg_one_smul,sub_eq_add_neg]
   let hZ:= billed_keeps P K I f (fun _=>enough P K) (fun N n m W _ _ x=> show _-_=_*(thermalT P K R n x-_) from (by rw [mul_sub, thermo_walks P K R W x, jac_walks P K O W x])) (fun n _=> (hQ n).1) k
   have hp:0≤X':= add_nonneg (orbC_ge P K R p Q h) (by unfold jacC; positivity); -- omission O later.
   have ha:0 ≤ X'*Real.exp (Z'.width*k):= mul_nonneg hp (Real.exp_pos _).le; exact ⟨mul_nonneg ha (boltC_pos _ h0.pos_a).le,obtain_fan ⟨d,H⟩ hZ (fun n hn=> seat_cost P K I f (fun _=> enough P K) (fun n _=>(hQ n).1) h0.pos_a.le hp _ k hk hn (hQ n).2) h0.pos_a ha⟩
end YM.AllOrder.Ker.Start
