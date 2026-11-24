import YM.FormalOPE.RG10.Shutters.Port
import YM.FormalOPE.RG10.Compass.Frame
/-! Matrix criterion for the Lie perturbations in WilsonX (pre-flow). Type exactly
all real H filtration endos killing unit, no weakening. Respect both horizons. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gazebo
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open RG10.Position RG10.Position.Grade
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d n:ℕ}
local notation "𝓥"=> Deck F d
local notation "T" => PertExtension.Physical.Profile
local notation "ℳ" => Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "💠" => RG10.Position.deck F d
local notation "U"=> (freeTable F)
local notation "motor" => operator (L:=Maxwell.standard F) (💠)
local notation "S" => RG10.Position.Grade.swing (F:=F) d
lemma votes (A:FrameAt (Deck F d) ℝ) : Oriented F d A ↔ Cut (Deck.price F d) (of A) ∧ ∀ s:Signed, of A*S s=S s*of A := by
 constructor; intro h; exact ⟨h.filtration,fun s=> Compass.oriented_top s h⟩
 rintro ⟨h,hS⟩; constructor; exact h; intro s
 let M : Module.End ℂ ((U).Field d):= motor A; change M.comp _ = (ride F s.ortho d).comp M
 let B k i:= (((S s k i):ℝ):ℂ); have he (k): ride F s.ortho d ((💠) k) = ∑ i,B k i • ((💠) i):= by unfold B; simp_rw [Grade.swing_deck]; exact ((💠).sum_repr _).symm
 have ha i:M ((💠) i)=∑ k,(A i k:ℂ) • ((💠) k):= operator_basis (L:=Maxwell.standard F) (💠) A i
 apply (💠).ext; intro i; rw [LinearMap.comp_apply,LinearMap.comp_apply,he,ha]; simp_rw [map_sum,map_smul,ha];
 simp_rw [he]
 have hv j:= Complex.ofReal_injective.eq_iff |>.mpr (congr_fun₂ (hS s) i j)
 simp only [Matrix.mul_apply,of_apply,Complex.ofReal_sum,Complex.ofReal_mul] at hv
 -- compare sums
 simp_rw [Finset.smul_sum,smul_smul]
 rw [sum_comm]; conv_rhs=> rw [sum_comm]
 apply sum_congr rfl; intro j _; simp_rw [← sum_smul]; exact congr_arg (fun q:ℂ=> q • (💠) j) (hv j).symm

/-- Canonical variations. -/
def tents (F:Frames G)(d:ℕ) : Submodule ℝ (FrameAt (Deck F d) ℝ) where
 carrier := {K| Oriented F d K ∧ K (Deck.start F d)=0}
 add_mem' := by
   intro x y hx hy; obtain ⟨⟨hx,h⟩,h'⟩:= (and_congr_left fun _=> votes _).1 (show _ ∧ _ from hx); obtain ⟨⟨hy,hh⟩,h''⟩:= (and_congr_left fun _=> votes _).1 (show _ ∧ _ from hy)
   refine ⟨(votes _).mpr ⟨hx.add hy,fun s=> ?_⟩,?_⟩
   · rw [show of (x+y)=of x+of y from rfl, add_mul,mul_add,h,hh]
   rw [Pi.add_apply,h',h'',add_zero]
 zero_mem' := by
   refine ⟨(votes _).mpr ⟨fun i j hi=>rfl,?_⟩,rfl⟩; intro s; rw [show of (0:FrameAt (Deck F d) ℝ) = 0 from rfl,zero_mul,mul_zero]
 smul_mem' := by
   rintro c K ⟨hx,hy⟩
   obtain ⟨hx,h⟩:= (votes _).1 hx
   refine ⟨(votes _).2 ⟨fun i j hi=> by rw [Matrix.of_apply,Pi.smul_apply,Pi.smul_apply]; exact mul_eq_zero_of_right c (hx _ _ hi),fun s=> ?_⟩,?_⟩
   · rw [show of (c • K)= c • of K from rfl, Matrix.smul_mul,Matrix.mul_smul,h]
   rw [Pi.smul_apply,hy,smul_zero]
lemma pinned (u:FrameAt (Deck F d) ℝ) : u∈ tents F d ↔ Oriented F d u ∧ u (Deck.start F d)=0:= Iff.rfl

-- conjugating perturbations by the installment slot signs
open Shutters
local notation "w"=>Deck.slots F d
private lemma switch_mul (A B:FrameAt (Deck F d) ℝ) : of (glass w (of A * of B))= of (glass w A) * of (glass w B):= by
 ext i j; simp only [of_apply, glass,Matrix.mul_apply,lapse,pow_add, Finset.mul_sum]; apply sum_congr rfl; intro k _
 have hK:= lap_twice («S»:=ℝ) (w k); unfold lapse at hK;
 linear_combination -((-1:ℝ)^w i*A i k * (-1)^w j *B k j)*hK
private lemma switch_signed (s:Signed): of (glass w (S s))=S s:= by
 ext i j; by_cases h:w i=w j
 · change lapse («S»:=ℝ) (w i+w j) * _=_; rw [h,lapse,pow_add, show (-1:ℝ)^w j * (-1)^w j=1 from lap_twice _,one_mul] -- maybe one_mul
 rw [of_apply,glass]; unfold swing; simp only [of_apply]; rw [grade_zero F d j (m:=Deck.grades F d i) (fun H=> h (show (Deck.grades F d i).2=(Deck.grades F d j).2 from congr_arg Prod.snd H)) (Loft.respected d _ _ (grade_written F d i)), Complex.zero_re,mul_zero]
lemma tenant (A:FrameAt (Deck F d) ℝ) (he:A∈ tents F d): glass w A∈ tents F d:= by
 obtain ⟨⟨h,hs⟩,h'⟩:= (and_congr_left fun _=> votes _).1 ((pinned A).1 he)
 refine ⟨(votes _).2 ⟨fun i j hv=> mul_eq_zero_of_right _ (h _ _ hv), fun s=>?_⟩, funext fun i=> mul_eq_zero_of_right _ (congr_fun h' i)⟩
 have ht : of (S s)=S s:= rfl
 conv_lhs=> rhs; rw [← switch_signed s]
 conv_rhs=> lhs; rw [← switch_signed s]
 rw [← switch_mul,← switch_mul,ht,hs]
end YM.FormalOPE.RG10.Gazebo
