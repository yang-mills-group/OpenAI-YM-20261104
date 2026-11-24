import YM.XSpace.Invariance
import YM.XSpace.Whiff

/-!
# Independent X-space correlation graph with nested position equations solved

Plots fixed for all perturbative orders. Each mesh sufficiently fine for its
comparison. Unit normalization and H-frame, real labels & signed parity coherent.
Any finite grade projection. Identity *neighborhood branch* at constant order,
all-orders formal recursive real position solution. No removal of regulator
from positive coefficients yet or coupling registration here. No comparison
made to already constructed continuum hierarchy here!
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick PowerSeries Expense Fray TestBudget
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n:ℕ} {A:Screen G d}

/-- Nested position condition data (including finite polynomial recipes). -/
structure Store (G:Gauge) extends Choice G where
  survey : ∀ d, Fray (measure d)

lemma equipped (g:G.Simple): Nonempty (Store G):=by obtain ⟨v⟩:=choose_horizons g; exact ⟨v,fun d=> Classical.choice (choose_fray (v.measure d))⟩

variable {ι : Type*} {F:Filter ι} {g:ι→Mesh}
namespace Store
variable (V:Store G) (A:Initialize G)
def layout (p:Mesh) (d:ℕ) : Pick G d:= (V.survey d).Lays (V.prepared d) (batch A p d)
def opens (p:Mesh) (d:ℕ) : Reports G d:= (V.survey d).fit (V.prepared d) (batch A p d)
lemma fits_walk (p:Mesh) (d:ℕ): realm (deck (V.layout A p d)) (batch A p d)= V.opens A p d:=rfl

def Meets (p:Mesh) (d:ℕ): Prop:=
  Formal (deck (V.layout A p d)) ∧
  (∀ i,(V.measure d).D (V.opens A p d i)=if i=0 then (V.measure d).D (reference G d) else 0) ∧
  faced (V.layout A p d)=V.layout A p d ∧ Forward (V.opens A p d) ∧ Respect (V.opens A p d) ∧
  Bijective (slope (V.measure d) (V.layout A p d 0) (batch A p d 0))

theorem nested_solution (d:ℕ) (S:Stretched F g): Rate F g (fun i=> guide G d (V.layout A (g i) d 0)) 0 ∧
    ∀ᶠ i in F,V.Meets A (g i) d ∧ V.layout A (g i) d=(fun l=> fell d (V.layout A (g i) (d+1) l)) ∧ ∀ l:ℕ,recruit (step d) (V.opens A (g i) (d+1) l)=V.opens A (g i) d l:=by
  let P (d:ℕ) (i:ι):= batch A (g i) d; let D:= V.survey; have hu d: (D d).Via (u:=F) (fun i=> P d i 0):= gait _ _ S
  have he:= Fray.chain_layout (D d) (V.prepared d) (D (d+1)) (V.respects d) (V.prepared (d+1)) (fun i j=> stepped A (g i) d j) (hu (d+1)) (hu d)
  refine ⟨(D d).costsPass (V.prepared d) A S,?_⟩; filter_upwards [he,(D d).parity_lane (P:=P d) (V.prepared d) (hu d) (Eventually.of_forall (fun i j=> slot_arrays ..)),(D d).happy (P:=P d) (V.prepared d) (hu d)] with i hi hj hz
  exact ⟨⟨hz.1,hz.2.1,hj.1,hj.2,(D d).reality (V.prepared d) (P d i) (fun j => reel_array A (g i) d j), hz.2.2⟩,hi⟩

theorem cumulative {d l:ℕ} (S:Stretched F g) (h:d≤l): ∀ᶠ i in F, ∀ j, recruit (up h) (V.opens A (g i) l j)=V.opens A (g i) d j:=by
  induction l,h using Nat.le_induction with
  | base => exact Eventually.of_forall fun i j=> rfl
  | succ l hl ih=> filter_upwards [(V.nested_solution A l S).2,ih] with i hi hi' j; rw [← hi' j, ← hi.2.2 j]; rfl

theorem uniqueness (d:ℕ) (S:Stretched F g) (T:ι→ Pick G d) (he:Tendsto (fun i=> guide G d (T i 0)) F (𝓝 0)) (hx:∀ᶠ i in F,(V.measure d).Solved (T i) (batch A (g i) d)): ∀ᶠ i in F,V.layout A (g i) d=T i:=
  (V.survey d).unique_shift (V.prepared d) (gait _ _ S) he hx

-- exact equality with power divergences kept on both numerator/denominator expansions; *any* coefficient sizes in this ambiguity.
theorem bare_invariance (p:Mesh) (d:ℕ) (h:V.Meets A p d): ∀ T: Guard G d,Formal T → constantCoeff T=1 → V.opens A p d=(V.survey d).fit (V.prepared d) (realm T (batch A p d)):= fun T hT hp=> Fray.invariance _ _ _ T hT hp ⟨h.1,h.2.1,h.2.2.2.2.2⟩

theorem leading (S:Stretched F g) (p:Fin n→Sec G d) (K:Set (Points n)) (h:IsCompact K) (hp:K⊆conf n) :
    ∃ C:ℝ,0≤C∧∀ᶠ i in F,∀ f:Test n,tsupport f⊆ K → ∀ b:ℝ,Bound f b→ ‖V.opens A (g i) d 0 n f p-reference G d n f p‖ ≤ b*C*(g i).spacing := (seeds_pay (V.survey d) _ A K h hp p S).land
end Store
end YM.XSpace.Normalize
