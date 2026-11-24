import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Tiling
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.RoofTile
/-!
# Counting ports. Uniformly paid mats from true period-natural families

Shift structure uses same displacements and type positions as TwoWave.
`Nat` at this module read after receiving period cost (post-L). Keep ANY
summer customers with declared Λ. α root and β inputs may have color/resident
series etc. Work on real ℓ∞ positions.

Covariance invoices written here for δ-local CP maneuver. Results depend on
primitive assumptions of Lean YM project (see cp checks). No FFT convention changes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ker
open Lattice Laurent Bloch Matrix Complex RG Push.Uniform Precision Push
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Primitives.TwoWave Primitives.TwoWave.RealSlice Further.PhysicalPeriodLimitF933 Shingle Macrame
open scoped BigOperators Topology Classical ContDiff
variable {n m : Side} {α β : Type} [Fintype α] [Fintype β] {k M : ℕ}
abbrev BookM (M : Window n m M) (α:Type): Leaf m α → Leaf n α := Prod.map M.cut id
lemma seats (W:Window n m M) : Fold (BookM W α) M:= Lace.Fitted.volume W.fold
abbrev rule (α:Type) (n:Side):=Board α n ℝ
def convey (W:Window n m M) : rule α n →L[ℝ] rule α m:= ContinuousLinearMap.pi fun i:Leaf m α=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) (BookM W α i)

omit [Fintype β] in
lemma wheel (W : Window n m M) (f v) (z w) : BookM W β ∘ floated (k:=k) (β:=β) f v w = floated z v w ↔ (∀ _ : Fin k,z=W.cut f) := by
  constructor
  · intro he i; have hh:= congr_arg Prod.fst (congr_fun he i); change W.cut (f+wrap _ _) = z+_ at hh; rw [W.port] at hh; exact (add_right_cancel hh).symm
  intro he; funext i; exact Prod.ext ((W.port f (point w i)).trans (congr_arg₂ (· + ·) (he i).symm rfl)) rfl
abbrev transport (α : Type) {ι : Type} (e : ι → Leaf n α) (i : ι) (w : Site n) : Leaf n α := ((e i).1+w,(e i).2)
abbrev turnM (α:Type)(w : Site n) := BookM (Macrame.parallel w) α
-- relative base entry determined by all moments including rank#1=0
abbrev Mat (n:Side) (α β:Type) (k:ℕ):= FrameCoeffs (Leaf n α) (Leaf n β) k ℝ
abbrev Mats (α β:Type)(k:ℕ):= (n:Side) → Mat n α β k
variable {C a : ℝ}
def Stilled (G : Mat n α β k) : Prop:= ∀ (w:Site n) i t, G (turnM α w i) (turnM β w ∘ t) = G i t
def Room (G : Mat n α β k) (a C:ℝ): Prop:= ∀ i t, |G i t|≤C*Real.exp (-a* (∑ j, separation i.1 (t j).1:ℕ))
def robe (W:Window n m M)(t:Fin k→Leaf n β) := parcel (fun z=> BookM W β ∘ z) t
lemma tried (W:Window n m M)(t:Fin k→Leaf n β) (z:Fin k→ Leaf m β): z∈robe W t ↔ BookM W β ∘ z=t:= posted ..
def Same (G : Mat n α β k) (V : Mat m α β k) (W:Window n m M) := ∀ i t, G (BookM W α i) t=∑ w∈robe W t,V i w
variable (Ad : Side→Prop)
def Often (Ad : Side→Prop) : Prop:= ∃ d:ℕ,∀ n : Side,d≤n.val→Ad n

def pristine (i: Site n)(t:Fin k → Leaf n β): Shift (Arm k) := fun w=> lift ((t w.1).1-i) w.2
omit [Fintype α] [Fintype β]
lemma coute (i : Leaf n α)(t:Fin k→Leaf n β)(w:Shift (Arm k))(j : Fin k) : point w j = lift ((floated i.1 (Prod.snd ∘ t) w j).1-i.1) ↔ point w j= lift (wrap n (point w j)) := by simp [floated]
lemma shoes (i:Site n) (t:Fin k→ Leaf n β)(j:Fin k) : point (pristine i t) j = lift ((t j).1-i):=rfl
lemma frock (i : Site n)(t:Fin k→Leaf n β): floated i (Prod.snd ∘ t) (pristine i t)=t:= by
  ext1 j; apply Prod.ext; · dsimp only [floated]; rw [shoes,wrap_lift]; abel
  rfl

lemma tour (i : Site n) (t:Fin k→Leaf n β) : Laurent.size (pristine i t) ≤ 4*∑ j, separation i (t j).1:=by
 unfold size; rw [Fintype.sum_prod_type,Finset.mul_sum]; apply Finset.sum_le_sum; intro j hj; rw [separation_comm]; unfold separation; change ∑ x:Axis, _ ≤ _; exact (Finset.sum_le_sum (fun i _ => Lattice.component_le ((t j).1-_) i)).trans_eq (by simp [Axis])
end YM.AllOrder.Ker
