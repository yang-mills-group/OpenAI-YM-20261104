import YM.AllOrder.Iron.Canvas
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Ker Start
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function
open Next.Fluctuations Gauge Tree Pressure
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m : Side}{k N:ℕ}
local notation "T[" n "]" => (trees P K n)
local notation "S[" n "]" => (dock P K n)
local notation "X[" n "]"=> Positions (Joint (trees P K n) G)
-- native counted lightly. All labels frozen common branch (changes separately stationary). keep Jacobian gain dependent only on O. Allows all. exported bonuses separate.
def atom (F:ℕ→Atom G k)(n:Side): X[n]→ℝ := Stationary.orbitRaw F ∘ fine G T[n]

lemma atom_walks (F:ℕ→Atom G k)(W:Lacing P n m N) (x:X[n]): atom P K F m (x ∘ (walks P K W).bores)= N*atom P K F n x :=  by
  unfold atom; simp only [comp_apply]; apply (congr_arg (Stationary.orbitRaw F) ((walks P K W).governs x)).trans
  unfold Stationary.orbitRaw Patch.average; dsimp [Function.comp]; simp_rw [W.high.signed]; simp_rw [Window.unc]; rw [← Finset.mul_sum]; ring_nf; rfl -- direction sum factor
variable (R:PathData G)(p:Clip) (O:ChartRatio G) {a C D Λ:ℝ}{L:ℕ}
variable (Q: Push.Uniform.Before G a C P.J K L)(h:R.Bounds p a C Λ)(hO:LocalRatio O)
-- nonnative radius purchases. Want strict. Supply cap using non-normalized Q.
def rev (Q: Push.Uniform.Before G a C P.J K L)(k:ℕ) :=  let Y :=  Q.tables p P; Y.value*Real.exp ((P.L.val:ℝ)*Y.width*k) * boltC k (breath a L)
include Q h
lemma class_payoff (hB:P.Branches K G)(hk:k+1≤L) : let _Y := Q.tables p P; ∃ F:Fan (Lobby P K G) (Lobby P K G) k, Cap F (small_a (breath a L)) (rev P K p Q k) ∧ ∀ n, Ad G P K n→ billed P K (classicalT P K R p) k n=pieces F n := by
   let I := Ad G P K; let f := classicalT P K R p; have hs n (hi:I n) :=  (Q.receipt T[n] (label S[n]) h hi rfl rfl).1; intro Y; obtain ⟨d,H⟩ := dock_larger P K hB; let c:Side := ⟨d+1,by omega⟩; have h0 :=  hs c (H c (by show d ≤ d+1; omega));
   have ha (n:Side)(hn:I n) :=  (hs n hn).born _ (mem_ball_self (x := 0) (hs n hn).pos_r); -- field name?
   let hZ :=  billed_keeps P K I f (fun _ h=>enough P K h) (fun N n m W _ _ x=> (walks P K W).appraisal K x (label _) p R) (fun n hn=>(ha n hn).1) k
   exact obtain_fan ⟨d,H⟩ hZ (fun n hn=> sightline P K h0.pos_a.le (promised P h.width.le) ((ha n hn).1) ((ha n hn).2) (enough P K hn) hk h0.pos_C.le) (breath_pos h.width L) (mul_nonneg h0.pos_C.le (Real.exp_pos _).le)

-- Loop bounds term. Don't swallow Λ. coordinates
local notation "Y"=>Q.tables p P

open Liquid
include hO
def revShadow (Q:Push.Uniform.Before G a C P.J K L)(Λ:ℝ)(k:ℕ):= let Y':=Q.tables p P; (orbC P K Q Λ+jacC O L)*Real.exp ((P.L.val:ℝ)*Y'.width*k)*boltC k (breath a L)
lemma shadow_payoff (hB:P.Branches K G) (hk:k+1 ≤ L) : let _Y':=Q.tables p P; 0≤revShadow P K p O Q Λ k ∧ ∃ F:Fan (Lobby P K G) (Lobby P K G) k, Cap F (small_a (breath a L)) (revShadow P K p O Q Λ k) ∧ ∀ n, Ad G P K n→ billed P K (shadow P K O R) k n=pieces F n:= by
   let I:=Ad G P K; let f:=shadow P K O R; obtain ⟨d,H⟩:= dock_larger P K hB; let c:Side:=⟨d+1,by omega⟩; have h0:= (Q.receipt T[c] (label S[c]) h (H c (by show d≤d+1; omega)) rfl rfl).1; intro Z'; let X':=orbC P K Q Λ+jacC O L
   have hQ(n:Side) : ContDiffAt ℝ ω (f n) 0 ∧ Scatter (address T[n] G) Z'.width L (f n) 0 X':= by
      obtain ⟨ha,hL⟩:=thermo_cost P K R p Q h n; let V:=jacT P K O n; have hb:ContDiffAt ℝ ω V 0:=hydrated hO
      refine ⟨ha.sub hb,?_⟩; have he:= (jac_cost P K O hO (N:=L) Z'.width n).smul hb (-1); have hz:= hL.add ha (hb.const_smul (-1 : ℝ)) he; rw [abs_neg,abs_one,one_mul] at hz; refine (show f n=_ from ?_) ▸ hz;
      funext t; change _-V t=_+(-1:ℝ)•V t; rw [neg_one_smul,sub_eq_add_neg]
   let hZ:= billed_keeps P K I f (fun _=>enough P K) (fun N n m W _ _ x=> show _-_=_*(thermalT P K R n x-_) from (by rw [mul_sub, thermo_walks P K R W x, jac_walks P K O W x])) (fun n _=> (hQ n).1) k
   have hp:0≤X':= add_nonneg (orbC_ge P K R p Q h) (by unfold jacC; positivity); -- omission O later.
   have ha:0 ≤ X'*Real.exp ((P.L.val:ℝ)*Z'.width*k):= mul_nonneg hp (Real.exp_pos _).le; exact ⟨mul_nonneg ha (boltC_pos _ (breath_pos h.width L)).le,obtain_fan ⟨d,H⟩ hZ (fun n hn=> sightline P K h0.pos_a.le (promised P h.width.le) ((hQ n).1) ((hQ n).2) (enough P K hn) hk hp) (breath_pos h.width L) ha⟩

def chargeAtom (k L:ℕ)(U a:ℝ) (B:ℝ)  :=  B*atomCost G U a L k * countCost (entryWidth L P.L a/2)
omit Q h hO
variable (μ U ξ:ℝ) (X₀:ℕ→Atom G k) (hK:SumBudget (fun i=>(X₀ i).budget μ) ξ)(hm:0<μ)(hp:PaintSupply G L U)
include hp hK hm
lemma atom_cost (n:Side): ContDiffAt ℝ ω (atom P K X₀ n) 0 ∧ Scatter (address T[n] G) (weaker L (entryWidth L P.L μ)) L (atom P K X₀ n) 0 (Iron.chargeAtom P (G:=G) k L U μ ξ)  :=  by
   let X :=  X[n]; let A(s:Signed) (i : Site (below P n)) (z:X)  :=  ∑' j,(X₀ j).unmasked (signedFine T[n] z s) i
   have hc(s i): ContDiffAt ℝ ω (A s i) 0 :=  Push.Uniform.label_analytic _ _ hm hK s hp i 0 (mem_ball_self zero_lt_one)
   have H0:0 ≤ ξ :=  (tsum_nonneg hK.1).trans hK.2.2; -- terms
   have ha : 0 < entryWidth L P.L μ :=  width_positive hm ..
   let B (s:Signed) (z:X) := ∑ i,A s i z; have H(s) :=  (ContDiffAt.sum (s := Finset.univ) (fun i _=> hc s i)) -- no let
   have hx(s : Signed): Scatter (address T[n] G) (weaker L (entryWidth L P.L μ)) L (B s) 0 (Iron.chargeAtom P (G:=G) k L U μ ξ) :=  by
     have hF i  :=  atom_beacon T[n] s hm hK hp 0 (mem_ball_self zero_lt_one) i
     have ht : Injective (affine (R := Per (below P n)) s 0)  :=  by intro x y he; unfold affine at he; simpa using congr_arg s⁻¹.act (add_right_cancel he)
     have hu :=  scatter (Multiplicity.injective ht) (hc s) hF ha (mul_nonneg H0 (atomCost_nn hp hm k)); rw [Nat.cast_one,mul_one] at hu; exact hu
   let b:ℝ :=  Fintype.card Signed; have hb:0<b := by unfold b; positivity
   have hf:atom P K X₀ n=fun z=>b⁻¹ • ∑ s,B s z :=  rfl
   rw [hf]; have hS := ContDiffAt.sum (s := Finset.univ) (fun i _=>H i); have he := (scatter_sum (s := Finset.univ) (fun i _=>H i) (fun i _=> hx i)).smul hS b⁻¹; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_nonneg (inv_pos.mpr hb).le, inv_mul_cancel_left₀ hb.ne'] at he; exact ⟨hS.const_smul _,he⟩

def rightsAtom (μ ξ U:ℝ)(L d k:ℕ) :=  (Iron.chargeAtom P (G:=G) d L U μ ξ)*Real.exp ((P.L.val:ℝ)*(weaker L (entryWidth L P.L μ))*k) * boltC k (breath μ L)
lemma atom_payoff (hB:P.Branches K G){i:ℕ}(hk:i+1≤L) :  ∃ F:Fan (Lobby P K G) (Lobby P K G) i, Cap F (small_a (breath μ L)) (rightsAtom (G:=G) P μ ξ U L k i) ∧ ∀ n, Ad G P K n→ billed P K (atom P K X₀) i n=pieces F n := by
   let I := Ad G P K; let f := atom P K X₀; have ha n:= atom_cost P K μ U ξ X₀ hK hm hp n; obtain ⟨d,H⟩:= dock_larger P K hB;
   let Y':= (weaker L (entryWidth L P.L μ)); have hr:0<Y':= by unfold Y'; apply div_pos (width_positive hm ..) (by positivity)
   have h0 : 0≤ Iron.chargeAtom P (G:=G) k L U μ ξ:= by unfold chargeAtom; exact mul_nonneg (mul_nonneg ((tsum_nonneg hK.1).trans hK.2.2) (atomCost_nn hp hm _)) (count_pos (half_pos (width_positive hm ..))).le
   let hZ :=  billed_keeps P K I f (fun _ h=>enough P K h) (fun N n m W _ _ x=> Iron.atom_walks P K X₀ W x) (fun n hn=>(ha n).1) i
   exact obtain_fan ⟨d,H⟩ hZ (fun n hn=> sightline P K hr.le (promised P hm.le) ((ha n).1) ((ha n).2) (enough P K hn) hk h0) (breath_pos hm L) (mul_nonneg h0 (Real.exp_pos _).le)

end YM.AllOrder.Iron
