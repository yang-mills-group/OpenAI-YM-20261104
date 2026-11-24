import YM.LocalLTE.East.Globe
import YM.LocalLTE.Bonnet.Career
/-! Expanding finitely many true addresses, booking the tails.We DON'T leave out tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Scarf
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio Marlin Push.BetaTransport Shingle
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {X : Listing G c} {m r j k p:ℕ} {e d a Z K q b v Y : ℝ} {x:ℝ} {s:Set ℝ} {ι:Type}
lemma normRange {o x:Site c} {s:Seat c}(hz:x=affine s.1 s.2 o) (p:ℕ):Seat.spread s (neighbors p o) = neighbors p x:=by
    let e:= Push.Local.turnSites s.1 s.2
    rw [hz]; ext i; obtain ⟨y,rfl⟩:= e.surjective i
    change e y ∈ (neighbors p o).image e ↔ e y∈ neighbors p (e o);
    simp only [Finset.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right, neighbors_mem,neighbors_mem,show separation (e o) (e y)=separation o y from Push.Local.turn_sep ..] -- edit

variable [DecidableEq ι](E:ι→ RegularAddress c) (s:Finset ι)(m:ℕ)
def enlarged (i:ι): RegularAddress c:=if i∈s then leap m (E i).site else E i
lemma homeland (i:ι): (enlarged E s m i).site=(E i).site:= by unfold enlarged; split <;> rfl
structure Rooms (B:BudgetPoint) (A:ℕ) : Prop where
   stands : m≤ A*B.B
   places i: i ∈ s →(E i).support⊆ neighbors m (E i).site
variable {A:ℕ} (B:BudgetPoint)(h:Rooms E s m B A)
include h
lemma placed (i:ι) : (E i).support ⊆ (enlarged E s m i).support:= by unfold enlarged; split; exact h.places _ (by assumption); rfl
-- can reuse East.places with Paint? generic A
omit h s E in
lemma standing (A:ℕ)(u:Site c) (hx:m ≤ A*B.B) : coverNumber B.B (neighbors m u) ≤ ballCost A := by
    refine (Corona.cover_mono ?_ B.B).trans (Corona.tile u A B.B B.B_pos); exact fun j hj=> halo_spec.mpr ⟨u,mem_singleton_self u,((neighbors_mem ..).1 hj).trans hx⟩
lemma outdoors (i:ι): coverNumber B.B (enlarged E s m i).support ≤ coverNumber B.B (E i).support+ballCost A:= by
    unfold enlarged; split
    next => exact le_trans (standing m B _ _ h.stands) (Nat.le_add_left ..)
    exact Nat.le_add_right ..
def kiosk (E':ℝ)(A:ℕ):ℝ:= Real.exp (E'*ballCost A)
lemma opens {f:ι→ℝ}(hp:∀ i,0≤ f i)(hr:Quotes.early
    B E f a): Quotes.early B (enlarged E s m) f (kiosk (preExponent B) A*a):=by
      intro x; refine budget_mono (budget_scale (Real.exp_nonneg _) (hr x)) (fun i=> ?_) (fun i=>?_)
      · split; next =>exact mul_nonneg (hp i) (Real.exp_nonneg _)
        exact le_rfl
      dsimp only; split; next hx=>
        rw [if_pos (show (E i).site=x from (homeland E s m i).symm.trans hx)]
        have hz:= Scarf.outdoors E s m B h i
        refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hz) (headline B|>.exponent_pos.le))) (hp i)) ?_; rw [Nat.cast_add,mul_add,Real.exp_add]; apply le_of_eq; unfold kiosk; ring -- edit
      next hx=> rw [if_neg (show ¬(E i).site=x from (fun h=>hx ((homeland ..).trans h))),mul_zero]
lemma acreage (f:ι→ Config G c→ℝ)(he:Meadow.Budget B E f a): Meadow.Budget B (enlarged E s m) f (kiosk (preExponent B) A*a):=by
    obtain ⟨g,hh,hk⟩:=he; refine ⟨g, opens E s m B h (fun i=> (hk _).2.1) hh,fun i=>⟨VerifiedReset.reg_larger (hk _|>.1) (Scarf.placed E s m B h i),?_⟩⟩; rw [homeland]; exact VerifiedReset.sup_larger (hk _|>.2) (placed E s m B h i)

end YM.PhysicalNext.Repeat.Scarf
