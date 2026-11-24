import YM.QuadraticLocal.Sunrise.Scatter
/-!
# Shift each output-column through κ powers in the unmarked-clock visible algebra
ℤ-inverted inputs must already come with nonnegative unshifted grade at this instant!
The map only introduces each WHOLE positive shift. Recover at `k+h` with projection cost.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Function Finset Filter MeasureTheory RG Precision Lattice
open Marker Multi Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order Join
open AllOrder AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Response
open PositionX.Jet
open scoped Topology BigOperators Classical
variable {V:Type}[Fintype V][DecidableEq V](J : Census V) (w:V→ℕ)
variable (F G:PTable J)(q:J.Mode)
namespace Launch
open PowerSeries
-- choose after engine
abbrev index (q:J.Mode) :ℕ:=∑ i∈q.val,w i
local notation "I"=>index J w
def see (n:ℕ):=(PowerSeries.coeff n F).part q
def summon:=PowerSeries.mk (see J F q)
def slow : PTable J := PowerSeries.mk (fun j=>Poly.inject (fun q=> PowerSeries.coeff j (((X:PowerSeries ℂ)^I q)*summon J F q)))
local notation "Λ"=> slow J w
local notation "τ"=> summon J
local notation "ψ"=> see J
local notation "ν"=> X (R:=ℂ)
local notation "χ"=> PowerSeries.coeff
-- avoid Xi notation `[ClassicalDecEq]`
lemma timing (j:ℕ) : ψ (Λ F) q j= if I q≤ j then ψ F q (j-I q) else 0 := by
 unfold see slow; rw [coeff_mk,show (Poly.inject _ : Poly J).part _=_ from rfl]; change χ j (X^I q*_) =_; rw [coeff_X_pow_mul']; unfold summon; rw [coeff_mk]; split_ifs<;> rfl
lemma headgate (j:ℕ):ψ (Λ F) q (j+I q)= ψ F q j:=by rw [timing,if_pos (Nat.le_add_left _ _),Nat.add_sub_cancel]
lemma reads : τ (Λ F) q= (ν)^I q*τ F q:=by ext n; rw [summon,coeff_mk,timing, coeff_X_pow_mul']; unfold summon; rw [coeff_mk]
lemma posted (r:ℂ) : τ (r•F) q=r • τ F q:=by ext n; simp only [summon,coeff_mk,see, coeff_smul,Poly.part_smul, smul_eq_mul]
lemma resolve {F G:PTable J} (h:∀ i,τ F i=τ G i):F=G:=by ext n i; specialize h i; apply_fun χ n at h; simpa [summon,see] using h
lemma addition : τ (F+G) q=τ F q+τ G q:=by ext n; simp only [summon,see,map_add, coeff_mk,Poly.part_plus]
lemma origin : τ 0 q=0:= by ext n; simp [summon,see]
lemma indicator : τ 1 q= if q=J.quiet then 1 else 0:=by
 ext n; rw [summon,coeff_mk,see,coeff_one]; simp only [apply_ite (χ n)]; split_ifs with h1 h2 h3 h4 <;> simp_all [Poly.one_part,coeff_one]
lemma both : τ (F*G) q=∑ i:J.Mode,∑ j:J.Mode,if Poly.merges i j q then τ F i*τ G j else 0 :=by
 ext n; simp_rw [summon,map_sum,apply_ite (χ n),coeff_mk,see,coeff_mul]; simp_rw [Poly.part_sum,Poly.part_mul,map_zero,coeff_mk,see]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]; apply sum_congr rfl; intro j _; by_cases h: Poly.merges i j q <;> simp [h]
lemma reduce : Λ (F*G)=Λ F*Λ G:=by
 apply resolve; intro q; rw [reads, both,both]; simp_rw [reads,mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; split
 next h=> rw [show I q=I i+I j from ?_,pow_add]; · ring
          unfold index; rw [← h.2,sum_union h.1];
 next=> rw [mul_zero]
lemma up_one : Λ 1=1:=by
 apply resolve; intro i; rw [reads,indicator]; split_ifs with ht; · subst i; simp [index,Census.quiet]
 rw [mul_zero]
-- audit lengths
lemma agenda : Λ (F+G)=Λ F+Λ G:= by apply resolve; intro i; rw [addition, reads,reads,reads,addition,mul_add]
lemma monoT (p:ℂ):Λ (p•F)=p•Λ F:=by apply resolve; intro i; rw [reads,posted,posted,reads,mul_smul_comm]
def hom : PTable J →+* PTable J where
 toFun:= Λ
 map_zero' :=by apply resolve; intro i; rw [reads,origin,mul_zero]
 map_one' :=up_one J w
 map_add' := agenda J w
 map_mul':= reduce J w
@[simp] lemma move (p:ℂ):hom J w (p•F)=p•hom J w F:= monoT J w F p
lemma through (r:ℕ)(h:series J r F=series J r G): series J r (Λ F)= series J r (Λ G):= by
   apply Join.both_parts; intro t u; rw [polarization,polarization]; congr 1; change see _ _ _ _= see _ _ _ _; rw [timing,timing]; split_ifs with hp; · unfold see; rw [← observation J r F (Nat.le_trans (Nat.sub_le _ _) (Order.order_limit _ u)), h, observation J r G (Nat.le_trans (Nat.sub_le _ _) (Order.order_limit _ u))]
   rfl
end Launch
end YM.QuadraticLocal.Sunrise
