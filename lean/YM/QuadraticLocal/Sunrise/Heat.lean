import YM.AllOrder.Kinetic.Connect
import YM.AllOrder.Floe.Alpine
/-!
# Horizontal extra fields

Key maneuver towards earning general mark `Fk` kernel outputs. No need positive covariance
on all fields — add ONE spurion horizontal field per analytical marker insertion atom (an entire
OWB track in mixed case); keep true vertical Hessian and hence unchanged covariance Law on
that space. We will shift the elementary Mark exponent by enough of the *same* kappa to enter
uniform width bills known for unmarked heat, translating back by exact polynomial identities
later. Never claim this as new choice of approximate coefficient.

Suppliers extending `Kinetic.{Bridge,Connect}` to ANY fix of vertical law and horizontal fields
not mapped to physical classical choice! We still have to instantiate direct `V` obtained from
`pulse` once the real step is set. Don't assume a price from these identities. Then reuse
`Ink.Code` to buy real site pressure kernels even at post horizon, with built-in polynomial
PLUS exp-radius stability and rank limit. No estimates on actual comparison here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method GaussianScore Module
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]
variable (e:rule α n≃L[ℝ]X)(v:rule β n≃L[ℝ]Y)
local notation "L"=> (α⊕β)
local notation "I"=> Leaf n L
local notation "E"=> X×Y
local notation "I'"=> Leaf n β
open MeasureTheory Classical
variable [DecidableEq β] (B:Law Y) (V: Stalk β β) (ht:∀ i j : Leaf n β,direct V n i j= rowM B (faces v) i j)
local notation "J"=> posture e v
set_option quotPrecheck false
local notation "F"=> faces v

local notation "V'"=> expand V α
variable [MeasurableSpace Y][BorelSpace Y] (μ:Measure Y)[μ.IsAddHaarMeasure] {u:Book (X×Y)}
include ht
/-- Tilt net on enlarged ruler. -/
lemma exactDyna (i j:I') : direct (expand V α) n (peg₀ (α:=α) i) (peg₀ (α:=α) j)=rowM B F i j:= by change direct V n i j=_; exact ht _ _
lemma lighting_net {f:X×Y→ℝ}(hv:Plausible f) : flicker (expand V α) n (f ∘ J)= infinity (B) (F) f ∘ J := by
   ext1 x; rw [flicker,Finset.sum_apply,cut_sum]; let K:= V'; let X':= J x;
   have hz(i:Leaf n α)(j:I): direct K n (lead β i) j=0:=(thin V j i).2
   have hs(i:I)(j:Leaf n α): direct K n i (lead β j)=0:=(thin V i j).1
   simp_rw [Finset.sum_apply, Pi.smul_apply]; change (∑ i:Leaf n α,∑ j:I,direct K n (lead β i) j • _)+(∑ j:Leaf n β,∑ l:I,direct K n (peg₀ (α:=α) j) l • _) =_
   simp_rw [hz,zero_smul,Finset.sum_const_zero]; rw [zero_add,Function.comp_apply,duplex,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [cut_sum, Finset.sum_apply]; simp_rw [hs,zero_smul,Finset.sum_const_zero,zero_add]; apply Finset.sum_congr rfl; intro j _; rw [show direct K n _ _=_ from exactDyna (α:=α) v B V ht i j,Pi.smul_apply, d_j e v f hv i, d_j e v _ (hv.ds _) j]; rfl
lemma lighting_mat {f g:X×Y→ℝ}(hf:Plausible f)(hv:Plausible g): spark (expand V α) (g ∘ J) (f ∘ J)= connection (B) (F) f g ∘ J := by
 ext1 x; rw [spark,Finset.sum_apply,cut_sum]; let K:= expand V α; let f' := f ∘ J; let g':=g ∘ J
 have hz(i:Leaf n α)(j:I):direct K n (lead β i) j=0:= (thin ..).2; have hs(i:I)(j:Leaf n α):direct K n i (lead β j)=0:=(thin ..).1
 simp_rw [Finset.sum_apply, Pi.smul_apply]; change (∑ i:Leaf n α,∑ j:I,direct K n (lead β i) j • _) +(∑ j:Leaf n β,∑ i:I,direct K n (peg₀ (α:=α) j) i • _ )= _
 simp_rw [hz,zero_smul,Finset.sum_const_zero]; rw [zero_add,Function.comp_apply,apron,Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [cut_sum, Finset.sum_apply]; simp_rw [hs,zero_smul,Finset.sum_const_zero,zero_add]; apply Finset.sum_congr rfl; intro j _; rw [show direct K n _ _=_ from exactDyna (α:=α) v B V ht i j,Pi.smul_apply, Pi.mul_apply, Pi.mul_apply,d_j e v g hv i,d_j e v f hf j,mul_comm]; rfl
-- cast references
local notation "R'"=>arrowR B μ u
variable (hU:u 0=0) (hw:Clear u)
def pressure_heat (u: Book (X×Y))(k j :ℕ) := arrowR B μ u k j ∘ posture e v
local notation "R" => pressure_heat e v B μ u
local notation "R0"=> ∑ i∈ range (k+1),∑ j∈range (M+1),spark (expand V α) (pressure_heat e v B μ u (k-i) (M-j)) (pressure_heat e v B μ u i j)
include hU hw
lemma heavy_home (r:ℕ)(k:ℕ) : R k (r+2) = (↑(r+2:ℕ):ℝ)⁻¹ • ((∑ i∈range (k+1),∑ j∈range (r+1), spark (V') (R (k-i) (r-j)) (R i j)) + flicker (V') n (R k r)) := by
 let M:= Warm (B) μ u; have hz (k r:ℕ): Plausible (R' k r):= Fire.lighted (eventA (B) μ hw hU k) r -- names
 ext1 x; rw [pressure_heat,Function.comp_apply,stepping (B) F μ hU hw]; simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply]; refine congr_arg ((↑(r+2:ℕ):ℝ)⁻¹ • ·) (congr_arg₂ (·+·) ?_ ?_);
 · refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> ?_; simpa only [Function.comp_apply,connection,spark,Finset.sum_apply, Pi.smul_apply,pressure_heat] using! (congr_fun (lighting_mat e v B V ht (hz i j) (hz (k-i) (r-j))) x).symm
 exact (congr_fun (lighting_net e v B V ht (hz k r)) x).symm
omit hw ht in
lemma full_root (k:ℕ) (q:rule α n)(H:∀ k,Rank (X×Y) (k+2) (u k)): (∑ j∈range (3*k+1), R k j (know (day α β) n q))= connected (B) μ u k (e q):= by
 have ht:= final_hot (B) μ hU H k (e q); rw [←ht,Fire.booked,Finset.sum_apply]; simp_rw [tablet, pressure_heat,Function.comp_apply,suite,map_zero]
omit hU hw ht
section scores
variable {T P:Side→Type}[∀ i,NormedAddCommGroup (T i)][∀ i,NormedSpace ℝ (T i)] [∀ i,FiniteDimensional ℝ (T i)][∀ i, NormedAddCommGroup (P i)][∀ i,NormedSpace ℝ (P i)][∀ i,FiniteDimensional ℝ (P i)]
variable {ι:Type} {Ad:Side→Prop} (X':∀ i:Side,Ad i→ rule α i≃L[ℝ] T i) (Y':∀ i:Side,Ad i→ rule β i≃L[ℝ] P i)
open Ink.Money
variable {Γ:ι→ℝ}
variable (Vs:ι→Stalk β β) (Z: ι → ∀ i: Side,Ad i→ Law (P i))
variable (K:ι → ∀ i:Side,Ad i→ Book (T i× P i))[∀ i,MeasurableSpace (P i)][∀ i,BorelSpace (P i)](μ' :∀ i:Side, Measure (P i))[∀ i,(μ' i).IsAddHaarMeasure]
-- doc.Xtilde.Match.Within.Port.Any Height n
variable (hK : ∀ x i (h:Ad i),K x i h 0=0) (hY:∀ x i (h:Ad i) k,Rank (T i×P i) (k+2) (K x i h k))
def stove (k j:ℕ): ι → Bills (α⊕β):= fun i n=> if hn:Ad n then pressure_heat (X' n hn) (Y' n hn) (Z i n hn) (μ' n) (K i n hn) k j else 0
def cards (k:ℕ) : ι → Bills (α⊕β):=fun i n=> if hn:Ad n then K i n hn k ∘ posture (X' n hn) (Y' n hn) else 0
def chartBook (k:ℕ):ι→ Bills α:= fun i n=> if hn:Ad n then Response.connected (Z i n hn) (μ' n) (K i n hn) k ∘ (X' n hn) else 0 -- uses Y'?
local notation "G" => stove X' Y' Z K μ'
variable (hρ:∀ i n (hn:Ad n) j k, direct (Vs i) n j k=rowM (Z i n hn) (faces (Y' n hn)) j k) -- placeholder.Vs conflicts notation above!
local notation "Φ" => fun i => expand (Vs i) α
include hK hY hρ
lemma iron : Code Ad Φ G:=by
 constructor
 · intro k i n hn; unfold stove; rw [dif_pos hn, pressure_heat, Fire.once (Z i n hn) (faces (Y' n hn)) (μ' n) (hK i n hn) (show Clear (K i n hn) from fun k=>(hY i n hn k).read) k]; rfl
 intro k r i n hn; simp_rw [stove,dif_pos hn]; exact heavy_home (X' n hn) (Y' n hn) _ _ (hρ i n hn) (μ' n) (hK i n hn) (fun k=> (hY i n hn k).read) r k
variable {K₀:ι→ℝ} {l : ℕ} (hf:CreditF Γ 0 K₀) (hp:∀ i,Belt (Vs i) a (K₀ i))(ha:0<a)
include hp ha hf
lemma daylight (hV:∀ i≤ N,License Ad Γ (cards X' Y' K i) a (i+2) l)(k:ℕ)(hk:k≤N): License Ad Γ (chartBook X' Z K μ' k) (chant a N (3*N)) (k+2) (Money.song l (3*N) + 4*(k+2)):=by
 let U:= Φ; let W:= G; let a':= chant a N (3*N); have he i (hi:i≤N): License Ad Γ (W i 0) a (i+2) l:= License.adapt (hV i hi) (by intro x n hn; unfold W cards stove; rw [dif_pos hn,dif_pos hn,pressure_heat,initial (Z x n hn) (μ' n) (hK x n hn) (fun k=> (hY x n hn k).read)])
 let f i n:= W k 0 i n; have ht :0<a':= soprano N ha _; have hx := peakward (N:=N) (iron X' Y' Vs Z K μ' hK hY hρ) hf ha (fun i=> Ink.bank (hp i) α (hf.nonneg i)) l he hk; have hX := hx.squeeze (gestate N ha (Nat.mul_le_mul_left 3 hk)) le_rfl (gesture _ (Nat.mul_le_mul_left 3 hk)); refine License.adapt (License.move («L»:=fun _=> day α β) (P:=fun _=>1) (freeC _ zero_le_one) ht (fun _=>paid_day) hX) ?_ -- bind A vs L
 intro i n hn; ext1 y; unfold chartBook; rw [dif_pos hn,Function.comp_apply,Function.comp_apply,snapshot,Finset.sum_apply]; simp_rw [stove,dif_pos hn]; exact full_root (X' n hn) (Y' n hn) (Z i n hn) (μ' n) (hK i n hn) k y (hY i n hn)
end scores
end YM.AllOrder.Kinetic
