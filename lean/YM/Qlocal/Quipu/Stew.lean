import YM.Qlocal.Quipu.Cat
import YM.AllOrder.Kinetic.Connect
/-! Thin extension of AllOrder/Kinetic/{Bridge,Connect} from θ on `E x Y`
 to any extension of exterior E (including Spectators). Cost conditional only
 on same Legendre covariance; arguments passive x*. Real.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu
open AllOrder AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method GaussianScore Module Kinetic
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
variable (e:rule α n≃L[ℝ]X)(v:rule β n≃L[ℝ]Y)
local notation "L"=> (α⊕β)
local notation "I"=> Leaf n L
local notation "E"=> X×Y
local notation "I'"=> Leaf n β
open MeasureTheory Classical
variable [DecidableEq β] (B: Law Y) (V: Stalk β β)(ht:∀ i j,direct V n i j=rowM B (faces v) i j)
local notation "J"=> posture e v
set_option quotPrecheck false
local notation "F"=> faces v
local notation "V'"=> expand V α
variable [MeasurableSpace Y][BorelSpace Y] (μ:Measure Y)[μ.IsAddHaarMeasure] {u:Book (X×Y)}
include ht
lemma tale (i j:Leaf n β) : direct (V') n (peg₀ (α:=α) i) (peg₀ (α:=α) j)=rowM B (faces v) i j:=ht i j
lemma torch_son {f:X×Y→ℝ}(hv:Plausible f) : flicker (expand V α) n (f ∘ J)= infinity B (F) f ∘ J := by
   ext1 x; rw [flicker,Finset.sum_apply,cut_sum]; let K:= V'; let X':= J x;
   have hz(i:Leaf n α)(j:I): direct K n (lead β i) j=0:=(thin V j i).2
   have hs(i:I)(j:Leaf n α): direct K n i (lead β j)=0:=(thin V i j).1
   simp_rw [Finset.sum_apply, Pi.smul_apply]; change (∑ i:Leaf n α,∑ j:I,direct K n (lead β i) j • _)+(∑ j:Leaf n β,∑ l:I,direct K n (peg₀ (α:=α) j) l • _) =_
   simp_rw [hz,zero_smul,Finset.sum_const_zero]; rw [zero_add,Function.comp_apply,duplex,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [cut_sum, Finset.sum_apply]; simp_rw [hs,zero_smul,Finset.sum_const_zero,zero_add]; apply Finset.sum_congr rfl; intro j _; rw [show direct K n _ _=_ from tale v B V ht i j,Pi.smul_apply, d_j e v f hv i, d_j e v _ (hv.ds _) j]; rfl

lemma warm_sons {f g:X×Y→ℝ}(hf:Plausible f)(hv:Plausible g): spark (expand V α) (g ∘ J) (f ∘ J)= connection B (F) f g ∘ J := by
 ext1 x; rw [spark,Finset.sum_apply,cut_sum]; let K:= expand V α; let f' := f ∘ J; let g':=g ∘ J
 have hz(i:Leaf n α)(j:I):direct K n (lead β i) j=0:= (thin ..).2; have hs(i:I)(j:Leaf n α):direct K n i (lead β j)=0:=(thin ..).1
 simp_rw [Finset.sum_apply, Pi.smul_apply]; change (∑ i:Leaf n α,∑ j:I,direct K n (lead β i) j • _) +(∑ j:Leaf n β,∑ i:I,direct K n (peg₀ (α:=α) j) i • _ )= _
 simp_rw [hz,zero_smul,Finset.sum_const_zero]; rw [zero_add,Function.comp_apply,apron,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [cut_sum, Finset.sum_apply]; simp_rw [hs,zero_smul,Finset.sum_const_zero,zero_add]; apply Finset.sum_congr rfl; intro j _; rw [show direct K n _ _=_ from tale v B V ht i j,Pi.smul_apply, Pi.mul_apply, Pi.mul_apply,d_j e v g hv i,d_j e v f hf j,mul_comm]; rfl
-- cast references
local notation "R'"=>arrowR B μ u
variable (hU:u 0=0) (hw:Clear u)
def sojourn (u: Book (X×Y))(k j :ℕ) := arrowR B μ u k j ∘ posture e v
local notation "R" => sojourn e v B μ u
local notation "R0"=> ∑ i∈ range (k+1),∑ j∈range (M+1),spark (expand V α) (sojourn e v B μ u (k-i) (M-j)) (sojourn e v B μ u i j)
include hU hw
lemma torchlight (r:ℕ)(k:ℕ) : R k (r+2) = (↑(r+2:ℕ):ℝ)⁻¹ • ((∑ i∈range (k+1),∑ j∈range (r+1), spark (V') (R (k-i) (r-j)) (R i j)) + flicker (V') n (R k r)) := by
 let M:= Warm B μ u; have hz (k r:ℕ): Plausible (R' k r):= Fire.lighted (eventA B μ hw hU k) r -- names
 ext1 x; rw [sojourn,Function.comp_apply,stepping B F μ hU hw]; simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply]; refine congr_arg ((↑(r+2:ℕ):ℝ)⁻¹ • ·) (congr_arg₂ (·+·) ?_ ?_);
 · refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> ?_; simpa only [Function.comp_apply,connection,spark,Finset.sum_apply, Pi.smul_apply,sojourn] using! (congr_fun (warm_sons e v B V ht (hz i j) (hz (k-i) (r-j))) x).symm
 exact (congr_fun (torch_son e v B V ht (hz k r)) x).symm
omit hw ht in
lemma artist (k:ℕ) (q:rule α n)(H:∀ k,Rank (X×Y) (k+2) (u k)): (∑ j∈range (3*k+1), R k j (know (day α β) n q))= connected B μ u k (e q):= by
 have ht:= final_hot B μ hU H k (e q); rw [←ht,Fire.booked,Finset.sum_apply]; simp_rw [tablet, sojourn,Function.comp_apply,suite,map_zero]

end YM.Qlocal.Quipu
