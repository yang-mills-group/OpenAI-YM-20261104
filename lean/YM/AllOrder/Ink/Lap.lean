import YM.AllOrder.Ink.Bay
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Method
open GaussianScore
variable (F:Stalk α α)  -- remove
local notation "X" => rule α n
abbrev pricePiece (k:Nat)(α:Type)[Fintype α](n:Side):=(Fintype.card (Leaf n α):ℝ)^k -- future
abbrev dab (z:Leaf n α): (rule α n→ℝ)→ rule α n→ℝ:= diff' (spot z)
def flicker (n:Side)(f:rule α n→ℝ) : rule α n→ℝ:= ∑ i:Leaf n α,∑ j:Leaf n α,direct F n i j • dab j (dab i f)
-- Lin test at x
lemma pallet (f:rule α n→ℝ)(x:X)(k:Leaf n α)(j:Leaf n α): (fun f=> dab j (dab k f)) f x=dab j (dab k f) x:= rfl
lemma flicker_plus (f g: X→ℝ)(hf:Plausible f)(hg:Plausible g): flicker F n (f+g) = flicker F n f + flicker F n g:= by unfold flicker dab; simp_rw [adds hf hg,adds (hf.ds _) (hg.ds _), smul_add,sum_add_distrib]
lemma flicker_scale (f: X→ℝ)(r:ℝ)(hf:Rank X k f) : flicker F n (r•f)=r • flicker F n f:= by unfold flicker dab; simp_rw [scalars hf.read,scalars (Rank.read (hf.der _)), Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> smul_comm _ _ _
lemma tool (x:X) : LinTest X k (fun f=>flicker F n f x):= ⟨fun f g hf hg => congr_fun (flicker_plus F f g hf.read hg.read) x, fun f g hf=> congr_fun (flicker_scale F f g hf) x⟩
lemma flicks {ι:Type*}(S:Finset ι)(f:ι→X→ℝ)(hf:∀ i∈S,Plausible (f i)): flicker F n (∑ i∈S,f i)=∑ i∈S,flicker F n (f i):= by
 induction S using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,Finset.sum_empty]; unfold flicker dab; simp_rw [(show ∀ i:Leaf n α,diff' (spot i) 0=0 from fun i=> dift ..),smul_zero,Finset.sum_const_zero]
 | insert i s ht h=> rw [Finset.sum_insert ht,Finset.sum_insert ht, flicker_plus F _ _ (hf i (mem_insert_self ..)) (Plausible.sum (fun i hi=> hf _ (mem_insert_of_mem hi))), h (fun i hi=> hf i (mem_insert_of_mem hi))]

lemma prices_flick {f:rule α n→ℝ}(hz:Belt F a D)(hD:0≤D)(hp:0≤a)(h:Prices k C f) : Prices (k-2) ((Fintype.card (Leaf n α):ℝ) * ((Fintype.card (Leaf n α):ℝ) * (D*((C* honor k)*honor (k-1))))) (flicker F n f):=by
  let P':=(Fintype.card (Leaf n α):ℝ); let b(y:Leaf n α):= spot y;
  have hb (i:Leaf n α): ‖b i‖ ≤1:= le_of_eq (norm_bolt i); have he(i j:Leaf n α):Prices (k-2) (D*((C*honor k)*honor (k-1))) (direct F n i j • dab j (dab i f)):= price_mono (price_scale ((h.taper (spot i) (hb i)).taper (spot j) (hb j)) _) (mul_le_mul_of_nonneg_right (hz.norm_direct hp i j) (mul_nonneg (mul_nonneg h.1 (honor_pos _).le) (honor_pos _).le))
  have hh:= price_sum (univ:Finset (Leaf n α)) (fun i _=> price_sum (univ:Finset (Leaf n α)) (fun j _=>he i j)); unfold flicker; simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh -- k defeq?
end Method
end YM.AllOrder.Ink
