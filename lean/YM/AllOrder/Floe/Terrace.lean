import YM.AllOrder.Floe.Dock
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a b C D Λ σ:ℝ}{k N l:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
set_option quotPrecheck false
local notation "Q[" n "," hn "]"=> (arbitrate P K (n:=n) hn)
variable {ι:Type} [Nonempty ι] (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i)) (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
set_option quotPrecheck false
local notation "A[" i "," n "]"=> clay P K (x i) p n
local notation "u[" i "," n "]"=> Lapis.orbit T[n] (F i n)
variable (V:ι→ Layout G) (T:Finset Age) (hV:∀ i,Legal T (V i)) (Γ:ι→ℝ)
local notation "D[" i "," n "," hn "]"=> (startup T[n] O (label S[n]) (x i) p Q hn (hx i) (h i n hn) hO)
local notation "W"=> License (Ad G P K) Γ
open Iron
variable (hL:CreditF Γ l L) (A:ι→ ℕ→ Positions (Primary n G)→ℝ)
-- real thickness once for all.Applies argument ℝ-space; `Γ field` used by λ after lists. Width `R` arbitrary. integral repayment ∃ witnesses independent of ι.
abbrev leaseF (a:ℝ)(k:ℕ) := small_a (breath a (k+3))
local notation "s"=>leaseF a N
lemma lease_pos (hx:0<a)(k:ℕ) : 0<leaseF a k:=div_pos (breath_pos hx _) (by norm_num)
lemma tess {μ:ℝ} {f:ι→ℝ}{S:ι→∀ n:Side, rule (Lobby P K G) n→ℝ}(X:ι→Fan (Lobby P K G) (Lobby P K G) k)(hl:∀ i, Cap (X i) μ (f i))(hs:0<μ)(hf: CreditF Γ l f)(hx:(z:ι)→(n:Side)→Ad G P K n→ extractF (iteratedFDeriv ℝ (k+1) (S z n) 0)=pieces (X z) n) : W (fun i n=> Radial.jet (S i n) (k+1)) μ (k+1) l := by
 let T i:= Ink.principal (X i); have he i:= pride (X i) (hl i) (hf.nonneg i); let z:ℝ:= ((k+1).factorial:ℝ)⁻¹
 refine License.pure _ (fun i=> (T i).scale z) (fun i=>|z| *(Fintype.card Lℓ*((Fintype.card (Fin k → Lℓ):ℝ)* f i))) hs (by convert (freeC _ (abs_nonneg z)).mul ((freeC _ (Nat.cast_nonneg (α:=ℝ) (Fintype.card Lℓ))).mul ((freeC _ (Nat.cast_nonneg (α:=ℝ) (Fintype.card (Fin k → Lℓ)))).mul hf)) using 1; omega) (fun i=> Ink.Field.scale_good _ (he i) z) (fun i n hn=>?_)
 rw [Ink.Field.scale_table]; funext v; change z* (iteratedFDeriv ℝ (k+1) (S i n) _ _) = z * _; exact congr_arg _ (Ink.beginning (X i) v (hl i) (hf.nonneg i) hs.le (hx i n hn)).symm
include hB hx Q
lemma advance_mote (hk:k ≤ N+2) : W (fun i=> Kinetic.Port.mote P K p (x i) (k+1)) (s) (k+1) 0:= by
 choose f hf h using fun i=> class_payoff P K (x i) p Q (hx i) hB (show k+1≤N+3 by omega)
 let S i (n:Side):= if hn:Ad G P K n then (clay P K (x i) p n) ∘ arbitrate P K hn else 0
 have ht:0<a:= (hx (Classical.arbitrary ι)).width; have hC:0≤ rev P K p Q k := by unfold rev; have ht':= reignQ P K p x L Q hB hx|>.2.2.1; exact mul_nonneg (mul_nonneg ht'.le (Real.exp_pos _).le) (boltC_pos _ (Iron.breath_pos ht ..)).le
 apply License.adapt (tess P K Γ f hf (lease_pos ht _) (freeC _ hC) (S:=S) (fun i n hn=>?_)); · unfold S Kinetic.Port.mote; intros i n hn; rw [dif_pos hn,dif_pos hn] -- intros after unfold?
 unfold S; rw [dif_pos hn,← h i n hn,arbC P K (x i) p hn k]
include hO hL
lemma advance_loop (hk:k ≤ N+2): W (fun i=> wavelet P K O (x i) (k+1)) (s) (k+1) l:= by
 choose h' f hf h using fun i=> shadow_payoff P K (x i) p O Q (hx i) hO hB (show k+1≤N+3 by omega)
 let S i (n:Side):= if hn:Ad G P K n then (morn P K (x i) O n) ∘ arbitrate P K hn else 0
 have ht:0<a:= (hx (Classical.arbitrary ι)).width
 have hb:CreditF Γ l (fun i=> revShadow P K p O Q (L i) k):= by
    let r:= atomCost G Q.Z a (N+3) 2; have hr:0≤r:=atomCost_nn (by have t:=Q.labels; exact ⟨t.1,fun x hx=>(t.2 x hx).order (by omega)⟩ : PaintSupply G (N+3) Q.Z) ht _ -- scope
    let A:=countCost (entryWidth (N+3) P.L a/2); have hv: CreditF Γ l (fun i=>orbC P K Q (L i)):= CreditF.mul (CreditF.mul hL (freeC r hr)) (freeC A (count_pos (half_pos (width_positive ht _ _))).le)
    exact ((hv.add ((freeC (jacC O (N+3)) (by unfold jacC; exact Finset.sum_nonneg (fun _ _=> norm_nonneg _))).up (Nat.zero_le _))).mul (freeC (Real.exp _) (Real.exp_pos _).le)).mul (freeC _ (boltC_pos _ (breath_pos ht ..)).le)
 apply License.adapt (tess P K Γ f hf (lease_pos ht _) hb (S:=S) (fun i n hn=>?_)); · unfold S wavelet; intros i n hn; rw [dif_pos hn,dif_pos hn]
 unfold S; rw [dif_pos hn,← h i n hn,arbS P K (x i) O hn k]
omit hO hL hx
open Extra.Iteration
variable (i:Age) (hK : ∃ f:ι→ℝ,CreditF Γ l f∧ ∀ j, Charged (V j i) σ (f j))(hσ:0<σ)
-- cost under σ.Libel
noncomputable def landV (p: ℕ)(v:ι)(n:Side):rule (Lobby P K G) n→ℝ:= if h:Ad G P K n then Radial.jet (far T[n] (V v) i ∘arbitrate P K h) p else 0
include hK hσ
lemma advance_atom (hk:k ≤ N+2): W (fun i'=>landV P K V i (k+1) i') (leaseF σ N) (k+1) l:= by
 obtain ⟨f,hc,hf⟩:= hK; have hQ:PaintSupply G (N+3) Q.Z:= by have t:=Q.labels; exact ⟨t.1,fun x hx=>(t.2 x hx).order (by omega)⟩
 choose g hg h using fun j=> atom_payoff P K σ Q.Z (f j) (V j i) (hf j) hσ hQ hB (show k+1≤N+3 from (by omega))
 let Gest(v:ι) (n:Side) := if h:Ad G P K n then Iron.atom P K (V v i) n ∘ prom P K G (enough P K h) else 0
 have hh : CreditF Γ l (fun v=>rightsAtom P σ (f v) Q.Z (N+3) i.r k (G:=G)):= by
    exact (((hc.mul (freeC _ (atomCost_nn hQ hσ _))).mul (freeC _ (count_pos (half_pos (width_positive hσ _ _))).le)).mul (freeC (Real.exp _) (Real.exp_pos _).le)).mul (freeC _ (boltC_pos k (breath_pos hσ ..)).le)
 refine License.adapt (tess P K Γ g hg (lease_pos hσ _) hh (fun v n hn=>?_) (S:=Gest)) (fun j n hn=>?_)
 · unfold Gest; rw [dif_pos hn,← h v n hn]; unfold billed tax; rw [dif_pos (enough P K hn)] -- verify orientation
 unfold landV Gest; rw [dif_pos hn,dif_pos hn]; apply congr_arg (fun f=> jet f (k+1)); rw [← Kinetic.Port.arb P K hn]; rfl
end YM.AllOrder.Floe
