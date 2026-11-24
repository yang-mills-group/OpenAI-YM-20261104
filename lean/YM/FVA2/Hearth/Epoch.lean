import YM.FVA2.Hearth.Passage
import YM.FVA2.Hearth.Stables
import YM.Branch.Pick
import YM.XSpace.Sequence
/-!
# Existence of physical multiscale `Epoch`s on the inversion regulator

Stick to the chosen odd ratio of the `Run`. Can even choose specific data
(supplied `Patch` and `Branch` notions). See `Register/Pressroom.lean` for
incorporating this into the public Wilson prescription.
Not about costing the steps on this or other geometry in analytic PT estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable (G: Gauge) (R:XSpace.Run) (Y: Patch) (h:Y.L.val=R.ratio)

structure Asteroid (G:Gauge) where
 Y: RG.KernelChoices
 ready : ∀ P:RG.Patch, P.Branches Y G
lemma galaxy (g:ℝ) (h:0<g):∃ t:Asteroid G,t.Y.penalty=g:=by obtain ⟨P,hp,H⟩:= Axial.viable G g h; exact ⟨⟨P,H⟩,hp⟩

 def vein (n:ℕ) : Side:= ⟨R.finalSide.side.val * R.den n,Nat.mul_pos R.finalSide.side.pos (R.den_pos _)⟩
lemma vein_even (n:ℕ) : Even (vein R n).val:= by
 exact even_iff_two_dvd.mpr (dvd_mul_of_dvd_left R.finalSide.even (R.den n))
lemma vein_large (n:ℕ): 4≤ (vein R n).val:= R.finalSide.large.trans (Nat.le_mul_of_pos_right _ (R.den_pos n))
include h in
lemma longer (n:ℕ) : (vein R (n+1)).val=(vein R n).val * Y.L.val:= by unfold vein; rw [h]; unfold XSpace.Run.den; change R.finalSide.side.val* R.ratio^(n+1) = R.finalSide.side.val*R.ratio^n * R.ratio; ring
 def lots (N:ℕ):=N+R.reserve*N*N
lemma lot_value (N:ℕ): vein R (lots R N)=(R.step N).p.side:= rfl

variable (A: Asteroid G)
 def advance (i: ℕ) : StepData (vein R i) (vein R (i+1)) := ⟨ Y,A.Y,longer _ _ h i⟩
local notation "S"=> Hearth.advance G R Y h A
-- exact sequence with chosen fixed P t tags (any such Choice will have same effect)
 def habit : (i:ℕ) → Fabric G (vein R i)
 | 0=> .endcap _ (vein_even ..)
 | i+1=> Fabric.layer (S i) (A.ready Y) (Classical.choice inferInstance) (vein_even ..) (habit i)
lemma roofed (i:ℕ) : Bottom (habit G R Y h A i) = R.finalSide.side:= by
 induction i with
 | zero=> change vein R 0= _; unfold vein XSpace.Run.den; apply PNat.eq; simp
 | succ i ih=> exact ih -- recursion
include h A in
lemma days_for (N:ℕ) : ∃ L:Fabric G (R.step N).p.side, Bottom L= R.finalSide.side:= ⟨habit G R Y h A (lots R N),roofed ..⟩

 def program (f:ℕ)(hf:4≤f): Patch:= ⟨⟨ R.ratio, (show 0<R.ratio from lt_of_lt_of_le (by decide) R.large) ⟩, f,hf,R.large,R.odd⟩

-- set (not front level in estimates; only physics symbol)
structure Epoch (G:Gauge)(m:Side) where
 F: Fabric G m
 T: Cloth F
 clock: Gear F

variable (K:ℝ) (u:0<K)
include h in
lemma possible (N:ℕ): Nonempty (Epoch G (R.step N).p.side):= by
 let t:=(galaxy G 1 one_pos).choose; let L:= habit G R Y h t (lots R N); exact ⟨⟨L,localTruss L,exampleGear L⟩⟩
lemma chosen (N:ℕ): Nonempty (Epoch G (R.step N).p.side):= possible G R (program R 4 le_rfl) rfl N
end YM.FVA2.Hearth
