import YM.Qlocal.Harmony.Conduct
import YM.Qlocal.Dialect.Stack
/-!
 Rank-row re-expression for analytic model labels. Includes chart price of the *cover*
 path, not its torus projection. Can be instantiated separately at every locus without
 choosing a layout depending on what fields will be observed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Harmony
open Function Finset Filter Push Push.AbsoluteSums
open Lattice MeasureTheory Wilson Pressure RG Gauge
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern
open Marker
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {V ι:Type} [DecidableEq V] {R:Census V} {G:Gauge} {s:Senses R}
    {n r m j k:ℕ} {c:Side}
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a C:ℝ}
open Shape Conductor
namespace Melody
variable (Z:Album ℕ s G n) (h:Z.Health a C)
    (ha: 0<a) (p:ℕ→Prop) (o:V→Site c) (t:ℕ)
    (T:E→ Config G c){y:E}(ht:Weather T y) (L:E→ℝ)(hl:ContDiffAt ℝ ω L y)
abbrev Colors (G:Gauge)(n:ℕ):= ℕ × Ranks G n
local notation "Ω"=> Colors G n
noncomputable def coefficient (i:Colors G n)(b:ℝ):= if p i.1 then tanA (Z i.1) i.2 b else 0
noncomputable def fundamental (i:Colors G n)(b:ℝ):= scales (Z i.1) i.2 b
lemma payFactor (i: Ω) (b:ℝ): |coefficient Z p i b| ≤ (Z i.1|>.fare b) * legend i.2:= by
 have he:= price b (Z i.1) i.2; unfold coefficient; split; exact he
 rw [abs_zero]; exact (abs_nonneg _).trans he
abbrev tagCost (B: ℕ→ℝ)(i:Colors G n):= B i.1 * legend i.2
abbrev podCost (G:Gauge)(C:ℝ)(n:ℕ):= C*(∑ i: Ranks G n,legend i)
theorem tags (B:ℕ→ℝ) (he: SumBudget B C): SumBudget (tagCost (G:=G) (n:=n) B) (podCost G C n):= budget_prod he (budget_finite (fun i=> legend_pos i|>.le) le_rfl)
set_option quotPrecheck false
local notation "c₀"=> fun i:ℕ=> (Z i|>.fare a)
local notation "f'"=>fun i:Ω=>fundamental Z i a
local notation "μ'"=>fun i:Ω=>coefficient Z p i a

noncomputable abbrev record (b:ℝ): Album (Colors G n) s G n:= fun i=> Dialect.Stack.mark (Melody.coefficient Z p i b) (fundamental Z i b)
local notation "B"=> record Z p a
lemma solo_mark (A: Vase s G n)(b:ℝ): solo (Dialect.Stack.mark b A) o t= b • solo A o t:=by
 unfold solo; split
 next he=> rw [if_pos (by exact he)]; exact funext fun i=> Dialect.Stack.Workers.moves ..
 next he=> rw [if_neg (show ¬(A.stage.Hears o) from he), smul_zero]
lemma solo_notes (A:Vase s G n)(x:Config G c)(a:ℝ):
    solo A o t x= ∑ i:Ranks G n,tanA A i a* solo (Shape.scales A i a) o t x:= by
 unfold solo
 simp_rw [show ∀ i:Ranks G n,(Shape.scales A i a).stage=A.stage from fun _=>rfl]
 split; exact Shape.imprints a A (o (Sonnet.root s)) x
 next => simp only [Pi.zero_apply,mul_zero, sum_const_zero]

include h
lemma paid : (record Z p a).Health a (podCost G C n):= by
 have ht: SumBudget (tagCost (G:=G) (n:=n) c₀) _:= tags (c₀) h
 exact budget_mono ht (fun i=> mul_nonneg (Vase.nn_size _) (Real.exp_nonneg _)) (fun i=> (by unfold record; rw [Dialect.Stack.Workers.rooms]; exact (mul_le_of_le_one_right (abs_nonneg _) (Shape.freeTicket ..)).trans (payFactor Z p i a)))
include ha
local notation "O"=> o (Sonnet.root s)
local notation "X"=> fun i:Ω => Bay.Hears ((B) i).stage o
lemma varied_color : Album.picture (fun _=>True) (record Z p a) o t= Album.picture p Z o t:= by
 ext U
 let f (i:Ω):= Album.readout (fun i:Ω=>True ∧ X i) B O t i U
 have he := paid Z h p
 have hh: Summable f:= Album.global_sum _ B O U t he ha
 change (∑' i:Ω,f i)=∑' i:ℕ, Album.readout _ Z O t i U
 rw [hh.tsum_prod]; refine tsum_congr fun i=>?_
 rw [utt]; change (∑' c:Ranks G n,f (i,c))=(if p i then solo (Z i) o t else 0) U
 have hh(c:Ranks G n): f (i,c)=μ' (i,c)* solo (f' (i,c)) o t U:=by
    unfold f; rw [utt (p:=fun i:Ω=>True), if_pos trivial]; exact congr_fun (solo_mark o t (f' (i,c)) _) U
 rw [tsum_fintype]; simp_rw [hh,coefficient]
 split_ifs with hb; · exact (solo_notes (n:=n) o t (Z i) U a).symm
 simp

include T ht hl
lemma harmonizes (k:ℕ) :
    HasSum (fun i:Ω=>coefficient Z p i a • iteratedFDeriv ℝ k (L*(solo (f' i) o t ∘ T)) y)
       (iteratedFDeriv ℝ k (L * (Album.picture p Z o t ∘ T)) y):= by
 let Z':=B
 rw [← varied_color Z h ha p o t]
 have he:= Conductor.attendance Z' (paid Z h p) ha (fun _=>True) o t T ht L hl k
 refine he.congr_fun (fun i=>?_); rw [if_pos trivial]; unfold Z'
 change _=iteratedFDeriv ℝ k (L*(solo (Dialect.Stack.mark (μ' i) (f' i)) o t ∘ T)) y
 rw [solo_mark,show L*((μ' i • solo (f' i) o t) ∘ T) = μ' i • (L*(solo (f' i) o t ∘ T)) from funext fun z:E=>mul_left_comm ..]; exact (iteratedFDeriv_const_smul_apply (a:=μ' i) ((hl.mul (Conductor.value o t T ht (f' i))).of_le (le_top (a:=(↑k: WithTop ℕ∞))))).symm
end Melody
end YM.Qlocal.Harmony
