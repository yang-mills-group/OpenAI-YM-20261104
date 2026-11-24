import YM.QuadraticLocal.Rebirth.Cash
import YM.QuadraticLocal.Germ.Tariff
import YM.QuadraticLocal.Germ.Annual
/-!
# Birth offset clones and their budget

Keep EVERY root, address and path stencil. Reparam mark packets simultaneously
 with the reborn copies. For Loan, rank `r` is preserved and offsets add to
 the FLUCTUATION count, hence change explicit spectral powers, not measured by
 remasking on real fields/literacy tests. Need payment on the re-expressed kernel norm.
 Copies created for all rows and offset repays through the height of this order controller.
 Palette solid amplitude tests still need pipeline into real probes and capacities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Finset Lattice RG Wilson Marker
open Comparison.RG02 Comparison.RG02.Adjacent
open Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling
open PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP
open Ac Push Push.AbsoluteSums Paths
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Chart Sunrise
-- `ProofFairness` and signatures depend.Keep scaled image exact width
namespace Mutation
open Earn Row
variable {V ι W:Type}[DecidableEq V]{R:Census V}
variable {G:Gauge}{n:Side} {P:Passport n V}
variable (X:ι→Row P R G W)
variable (Q:Pace.Coin)(h:Q 0=0)(L j:ℕ)
set_option quotPrecheck false
local notation "T"=> (tariff Q h L)
local notation "p" i:max=> ((X i).lamp)

def next (u:Loan)(i:ℕ): Loan where
   toll := u.toll
   e := u.e+i
   r := u.r
   higher := u.higher
   crest := u.crest.trans (by omega)
abbrev ways (i:ι) := Fin (j-(X i).lamp.e+1)
local notation "Xk"=> (Mutation.ways X j)
abbrev Names := (Σ i, ways X j i)
local notation "N"=> (Mutation.Names X j)
def offset (i:Mutation.Names X j) := ((next ((X i.1).lamp) (i.2.val)))
def coefficient (i: Mutation.Names X j) := Chart.tariff Q h L ((X i.1).lamp.lag) (i.2.val)
def stamp (i:N) : Row P R G W := { (X i.1) with lamp := (offset X j i), atom:= (X i.1).atom, salary:= (X i.1).salary * (1+|Mutation.coefficient X Q h L j i|), sound:= mul_pos (X i.1).sound (by positivity), paint:=((Mutation.coefficient X Q h L j i : ℂ) • (X i.1).paint) }
-- are other proof fields filled? write manually
local notation "Y"=> (Mutation.stamp X Q h L j)
local notation "φ" i:max=> ( X i )
lemma mode (i:N): ( (Mutation.stamp X Q h L j) i ).mode=(X i.1).mode:=rfl
lemma aged (i:N): ( Y i ).lamp.toll=( X i.1 ).lamp.toll ∧ ( Y i ).lamp.e=(X i.1).lamp.e+i.2.val:= ⟨rfl,rfl⟩
lemma billed (i:N) : ( Y i ).lamp.lag= (X i.1).lamp.lag+(i.2.val:ℤ):=by unfold Loan.lag; rw [(Mutation.aged X Q h L j i).2]; change _-(↑((X i.1).lamp.r):ℤ)= _; omega
lemma growth (i:N) : ( Y i ).length=( X i.1 ).length:=rfl
lemma stable (i:N) : ( Y i ).center=(X i.1).center:=rfl
lemma feature (i:N) (P:BudgetPoint): (Y i).ground P=(X i.1).ground P:=rfl
lemma reflects (i:N): (Y i).clear ↔ (X i.1).clear:= .rfl
local notation "Φ" i:max=> ( coefficient X Q h L j i )
local notation "C" i:max=> ( (X i).lamp )

variable (w:V→ℝ)(t:V→ℕ){k d:ℕ}{a c U D ν z x r:ℝ}
variable (H: Recharged Q h U D L j d a ν z)
variable (A: Earn.Scene.Armada X w t x c j k d)
include H A
lemma valid (i:ι): (X i).lamp.toll≤ d ∧ (X i).lamp.e≤ j ∧ (X i).lamp.r ≤ j+d+1:= let he:=Scene.Armada.degreeR t A.toMinistry _ (A.purchases.usable i); ⟨he.2.1,he.1,he.2.2⟩
lemma rebate (i:N): 1+ |Mutation.coefficient X Q h L j i| ≤ a:= H.progress (C i.1) (A.purchases.usable i.1).1 ( valid X Q h L j w t H A i.fst|>.1 ) i.2.val (Nat.le_of_lt_succ (i.2.isLt))
lemma tickets : Offers (Mutation.stamp X Q h L j) w x (z*c):= by
   intro n; let f(v:Row P R G W):= if v.center=n then (Poly.toll w v.mode)*v.height x else 0; let f₁ i:= f (X i); let f₀ i:= f (Y i); let V i:= z*f₁ i; have hξ:1≤z:= H.z_quota; have hp := A.suggests n; apply Width.trapeze f₀ (show SumBudget V (z*c) from budget_scale (le_trans zero_le_one hξ) hp);
   intro i; have h₁(r:Fin (j-(X i).lamp.e+1)) : f₀ (⟨i,r⟩:N) = (1+|Φ (⟨i,r⟩:N)|)* f₁ i:= by
      unfold f₀ f₁ f; rw [stable,Row.height, Mutation.growth, Mutation.mode]; split
      · unfold Row.height; change _*(( (X i).salary*(1+|Φ (⟨i,r⟩:N)|))*_)= _; ring
      ·  rw [mul_zero]
   have hN:0≤f₁ i:= hp.1 i; apply budget_finite; intro r; rw [h₁]; positivity
   rw [sum_congr rfl (g:=fun r:Xk i=> (1+ |Φ (⟨i,r⟩:N)|)* f₁ i) (fun i' _=>h₁ i') ,← sum_mul]; apply mul_le_mul_of_nonneg_right _ hN; refine ( sum_le_sum (f:=fun r:Xk i=> 1+|Φ (⟨i,r⟩:N)|) (fun k _=> Mutation.rebate X Q h L j w t H A ⟨i,k⟩)).trans ?_; rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]; exact (mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr (show j-(X i).lamp.e+1≤j+1 from by omega) ) (le_trans zero_le_one H.quota)).trans H.attendance
lemma allocate : Earn.Scene.Armada (Mutation.stamp X Q h L j) w t x (z*c) j k d:= by
    refine ⟨A.toMinistry,A.positive, Mutation.tickets X Q h L j w t H A,⟨fun i=> A.purchases.spend i.1,?_⟩,?_⟩ -- typo
    · intro i; have he : i.2.val < j - (X i.1).lamp.e+1:= i.2.isLt; refine ⟨?_,(A.purchases.usable i.1).2⟩; rw [(Mutation.aged X Q h L j i).2]; have ht:= ( valid X Q h L j w t H A i.1 ).2.1; omega
    intro i v; change ‖(Φ i:ℂ) • (X i.1).paint v‖ ≤ (X i.1).salary*(1+|Φ i|); rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,mul_comm (X i.1).salary]; exact mul_le_mul (le_add_of_nonneg_left zero_le_one) (A.honor i.1 v) (norm_nonneg _) (by positivity)
omit H A

-- include projection proof in separate branch
section links
open QuadraticLocal.Affinity
variable {𝕜:Type}[RCLike 𝕜][NormedAlgebra 𝕜 ℂ]{Y':V→Type} [∀ i,AddCommGroup (Y' i)][∀ i,Module 𝕜 (Y' i)]
variable (A':∀ i,Set (Y' i))(E:∀ i,Submodule 𝕜 (Y' i))(X':ι→Row P R G (Wallet A'))
lemma fidelity (hA: Earn.Tableau E A' X') : Earn.Tableau E A' ( Mutation.stamp X' Q h L j ):= ⟨fun i=> (hA.bill i.1).cs (↑(Mutation.coefficient X' Q h L j i))⟩
instance instCountable [Countable ι] : Countable ( Mutation.Names X j ):= by unfold Names; infer_instance
end links
end Mutation
end YM.QuadraticLocal.Rebirth
