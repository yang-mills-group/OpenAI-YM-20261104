import YM.QuadraticLocal.Poetry.County
/-!
# The lantern publishes its entire series onward
 with uniform quantitative wallet. Witnesses bound to FinanceH.Length. 
 Relative ℓ-Λ costs linear here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b:ℝ} {n m:Side}{k d e j N:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "E"=> Point (Coarse G⊕M)
namespace Dais
open Comparison.Density.Render
variable (ha:0<a)(hb:0<b)
include ha hb
lemma purse (G:Gauge)(k r:ℕ) (ht:b*(4*r:ℕ)≤ a/2): ∃ D>(0:ℝ),∀ T:Atom G k,(torch T r).Good b (D*T.budget a) r:= by
 let d:ℝ:= Fintype.card G.ColorIndex+1; let i:ℝ:=Fintype.card (Coarse G)
 let w:= Comparison.Density.Render.entry G k r; have hz:0≤ w:= pow_nonneg (mul_nonneg (code_nn _) (pass_nn G _)) _; let s:=a/4; let hh:0<s:=by unfold s; positivity
 obtain ⟨L,hL,H⟩:= Knot.addon (r*k) 1 zero_lt_one hh; obtain ⟨M,hM,h⟩:= Knot.addon (4*r) 2 zero_lt_two hh; simp_rw [one_mul] at H; let Z:=(M*i^r)* (d^r*(w*L)); have hZ:0≤Z:=by unfold Z d i; positivity
 refine ⟨1+Z,by positivity,fun u=> (power u r b hb).debt le_rfl ?_ le_rfl⟩; let n:= u.length; let g:= u.magnitude; let F:= field u.length G; let V:=(n:ℝ); let p:=Real.exp (s*↑n)
 have hp: (((F).card:ℝ))^r≤ i^r*(M*p):= by
    unfold F; rw [plaza]; push_cast; rw [mul_pow, ← pow_mul, mul_comm]; apply mul_le_mul_of_nonneg_left _ (by positivity); refine (pow_le_pow_left₀ (by positivity) (?_:2*V+1≤ (2:ℝ)*(1+V)) _).trans (h u.length); unfold V; linarith
 have he : b*↑(r*(4*n):ℕ) ≤ a/2*(n:ℝ):= by push_cast; push_cast at ht; nlinarith [mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (α:=ℝ) n)]
 have hG : 0≤g:= Texture.mag_nonneg _; let P:=Real.exp (a/2*V); change _*(Real.exp (b*↑(r*(4*n):ℕ))*(d^r*(g*w *(1+V)^(r*k)))) ≤ _
 refine (mul_le_mul hp (mul_le_mul (show _≤P from Real.exp_monotone he) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (H n) (mul_nonneg hG hz)) (pow_nonneg (show 0≤d from by unfold d; positivity) _)) (by change 0≤ d^r*(g*w* (1+V)^(r*k)); unfold d V; positivity) (by unfold P; positivity)) (by change 0≤ Real.exp _*(d^r*(g*w* (1+V)^(r*k))); unfold d V; positivity) (by unfold i p; positivity)).trans ?_
 have hx: P * p * p= Real.exp (a*V):= by unfold P p; rw [←Real.exp_add,← Real.exp_add]; unfold V s; congr 1; ring
 refine le_trans (le_of_eq (show _=Z*u.budget a from ?_)) (mul_le_mul_of_nonneg_right (by linarith) (by change 0≤ g*_; positivity)); unfold Z Atom.budget; rw [← show _=Real.exp (a*u.length) from hx]; change i^r*(M*p)*(P*(d^r*(g*w*(L*p))))= _*(g*_); ring
end Dais
namespace Lantern
open Picket Dais Garnish
variable (p:Lantern G M)(x:Site n)(s:ℕ)
def charter (e d:ℕ): AllOrder.Ink.Field (Coarse G⊕M) := if e≤d then Garnish.stack (torch p.atom (d-e+p.r)) p.roots else Field.void (Coarse G⊕ M)
lemma read (e d:ℕ)(A:Link G n)(v:rule M n): (p.charter e d).site n x (mingle A v) = p.gleam x v e d A:= by
 unfold charter; split; next h=> rw [placed p x v e A _ h, Garnish.regard,noted]
 next h=> rw [p.pre x v e (by omega)]; unfold Field.void Field.site; simp only [tsum_empty,Pi.zero_apply] -- h:¬≤ need >
variable (h:p.Bears H q N)
include h
lemma elected (e d:ℕ) : Fixed H q (p.charter e d):=by
 unfold charter; split; next hp=> exact attire H q _ _ h.considered h.owns
 next hp=> exact wash H q
omit h
variable (H₀:0<a)(hb:0<b)(hD:b≤a)
include H₀ hb hD
lemma currency (G:Gauge){N d e:ℕ}(Y: d≤N)(K: b*(4*N:ℕ)≤ a/2): ∃ C₀> (0:ℝ),∀ i≤N, i ≤ N-(d-e) → ∀ T:Atom G i, (torch T (d-e+i)).Good b (C₀*T.budget a) (d-e+i):=by
 let O(i:ℕ): Prop:= i≤N ∧ i≤N-(d-e)
 choose f hf Hf using fun (i:Fin (N-(d-e)+1)) => purse (a:=a) (b:=b) H₀ hb G (i.val) (d-e+i.val) (by refine (mul_le_mul_of_nonneg_left (show (↑(4*(d-e+i.val)):ℝ) ≤ ↑(4*N) from ?_) hb.le).trans K; exact_mod_cast (show 4*(d-e+i.val)≤4*N by omega)); let Q:=∑ i,f i
 refine ⟨1+Q,by have hx:0≤Q:= sum_nonneg fun i _=> (hf i).le; positivity,fun i h h' T=>?_⟩; let x:Fin (N-(d-e)+1):= ⟨i,Nat.lt_succ_of_le h'⟩; have ht:f x ≤ Q:=Finset.single_le_sum (f:=f) (fun i _=>(hf i).le) (Finset.mem_univ x); exact (Hf x T).debt le_rfl (mul_le_mul_of_nonneg_right (ht.trans (le_add_of_nonneg_left zero_le_one)) (by unfold Atom.budget; have hh:= Texture.mag_nonneg T; positivity)) le_rfl
-- lantern age e. r proof needs scope.Tech: previous d'=e+σ+2; k≤N-(d-e).
lemma allowed (u:Finset M)(G:Gauge)(q:M){k e N:ℕ}(he:k≤N)(hp:k+(d-e)≤N)(K:b*(4*N:ℕ) ≤ a/2)(hX:d≤N): ∃ M':(ℝ),0<M' ∧ ∀ (T:Lantern G M),T.Bears u q k→(T.charter e d).Good b (M' * T.money a) (k+(d-e)):= by
 obtain ⟨t,hμ,hZ⟩:= currency H₀ hb hD G (e:=e) hX K; refine ⟨t,hμ,fun T h=>?_⟩; have hg:= T.card_le h.tall; unfold charter; split
 next h'=>
   let R:= hZ T.r (hg.1.trans he) (by omega) T.atom; let g:= T.atom; let L:= meter T.roots; refine (Garnish.license T.roots _ R).debt le_rfl ?_ ?_
   · let ν:= Real.exp (a*L); have he:T.money a=ν*T.atom.budget a:= by unfold Lantern.money Atom.budget Lantern.length; push_cast; rw [mul_add,Real.exp_add]; unfold ν L; ring
     rw [he, mul_left_comm]; have hhh:0≤t*T.atom.budget a:= by unfold Atom.budget; have hh:=Texture.mag_nonneg T.atom; positivity
     rw [mul_left_comm t (Real.exp _),mul_left_comm t ν]; exact (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg L))) hhh)
   have hh:T.r+T.roots.length≤k:=h.tall; omega
 next hc=> refine Field.Good.debt Field.silent le_rfl (mul_nonneg hμ.le ?_) le_rfl; exact T.fee_nn _
end Lantern
end YM.QuadraticLocal.Poetry
