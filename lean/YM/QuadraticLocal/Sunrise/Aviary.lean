import YM.QuadraticLocal.Sunrise.Chimney
import YM.QuadraticLocal.Sunrise.Heat
/-!
# Sponsor real heat for all loan tags
Launch before order via Tilt. Calculates the License for K≤Art.N at explicit width. Preserve
 K≥epoch projections.Cosine. ANY mix of labels at fixed Loan factors across lengths and all
 occupancies inside proof. Coframe.Info.C. augmented post stencil installations with all Root
 plane positions across Ad. Still require rendering Γ as invariant curvature.Support etc later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open AllOrder.Floe Kinetic.Port Work.F08
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n m:Side} {a b C D Λ σ:ℝ}{k N l:ℕ}
namespace Aviary
open Bough Chimney Kinetic
variable (P:Patch)(K:KernelChoices)
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
variable {δ H:ℝ} (A : PortPre P K p x b δ H)(ht:0<b)(hs:b≤leaseF a N)
variable (hL : CreditF Γ l L)
local notation "U[" i "," n "," hn "]"=> books T[n] (V i) T D[i,n,hn]
local notation "A₀[" i "," n "," hn "]"=> (rooted P K p x L Q hx F h i (n:=n) hn)
local notation "d₀"=> stalk P K p x A
open Extra.Iteration
variable (j:Age) (hh:∀ j∈T,∃ f:ι→ℝ,∃ s,0<s∧CreditF Γ l f∧b ≤ leaseF s N ∧ ∀ i, Charged (V i j) s (f i))
local notation "A'"=> (fun i:ι=> expand (A.deep i) (Coarse G))
-- vary all extra fields disciplined.We.S. canonical f per Loan.Template ABI. j and i.
variable {M:Type}[Fintype M] (I:M→Loan)(s:ι→ ∀ i:M,Atom G (I i).r)(y:ι→M→ Site P.L)
local notation "I[" _n "]" => ((Coarse G) ⊕ M)
local notation "H'"=> Camp
abbrev doorK (P:Patch)(K:KernelChoices)(G:Gauge)(M:Type) : (Lobby P K G) → (((Coarse G)⊕M) ⊕ RealSlice.Vertical G P K):= door M
local notation "H₁"=>(((Coarse G)⊕M)⊕ RealSlice.Vertical G P K)
local notation "T₀"=> doorK P K G M
local notation "η"=> ramp (doorK P K G M)
local notation "pt[" n "]"=> below P n
def sits (n:Side) (i:ι)(j:M)(z:Site n): Site (below P n):= (shores P n).assemble (z,y i j)
abbrev bark (n:Side) (hn:Ad G P K n)(i:ι):= train I (s i) (sits P y n i) (V i) T T[n] D[i,n,hn]
-- ℕ order setup
local notation "T₁[" i "," n "," hn "]"=> train I (s i) (sits P y n i) (V i) T T[n] D[i,n,hn]
local notation "Ξ₀"=> (fun i n hn=> T₁[i,n,hn])
-- Books may not need K includes.
variable (i':M)
abbrev aurora (G:Gauge)(M:Type)[Fintype M](n:Side) : rule ((Coarse G)⊕M) n ≃L[ℝ]Apex n G × rule M n:= spectrum M (exteriorL G n)
local notation "Y[" n "]"=> (aurora G M n)
local notation "Z'[" n "," hn "]"=> interiorL P K G (n:=n) hn
local notation "Z[" n "," hn "]"=> (posture (aurora G M n) (interiorL P K G (n:=n) hn))
local notation "μ'"=> (cards (Ad:=I₀) (fun i _=> aurora G M i) (fun _ h=> interiorL P K G h) Ξ₀)
variable {μ:ℝ}(hv:0 < μ)(hm:b*(4*(N+1):ℕ)≤ μ/4 * (P.L.val:ℝ)) (J':∀ j:M,CreditF Γ l (fun i=>(s i j).budget μ)) -- post width.M.Budget
local notation "Wb"=> (4*(N+1):ℕ)
-- fresh.Bi.Stalk.H.Spiral
local notation "β'"=> billH (Coarse G) (RealSlice.Vertical G P K) δ H
open Push
set_option maxHeartbeats 200000
include ht hB hv hm J' hO Q A
lemma lampL (j:M)(hk:k≤N) : W (fun i n=> if hn: I₀ n then (∑ z:Site n,Bough.soldier I (s i) (sits P y n i) T[n] D[i,n,hn] j z k) ∘ (Z[n,hn]) else 0) b (k+2) l:= by
   let ξ(i:ι):= d₀ i; let r:=I j; let f(i:ι)(n:Side):= if hn:I₀ n then ((∑ z:Site n,soldier I (s i) (sits P y n i) _ D[i,n,hn] j z k) ∘ (Z[n,hn])) else 0
   by_cases he:r.e+r.toll ≤ k; swap; · refine License.adapt (License.null _ ht) (fun i n hn=>?_); rw [dif_pos hn]; ext1 z; unfold Function.comp; rw [Finset.sum_apply]; apply Eq.symm; refine sum_eq_zero (fun x _=>?_); unfold soldier Loan.alloy; rw [if_neg he]; exact mul_zero _
   let Qξ:= β' -- conflict
   let f₀(i:ι):= s i j; let γ':ℕ:= k-(r.e+r.toll)+r.r; have hk' : γ' ≤ k+1:= by unfold γ'; have ht:=r.crest; omega
   have he':PaintSupply G γ' Q.Z:= ⟨Q.labels.1,fun i hi=> (Q.labels.2 i hi).order (by omega)⟩
   have hb : b*(4*γ':ℕ) ≤ μ/4 * (P.L.val:ℝ):= (mul_le_mul_of_nonneg_left (show (↑(4*γ':ℕ):ℝ)≤(_ : ℝ) from Nat.cast_le.mpr (by omega : 4*γ'≤ Wb)) ht.le).trans hm
   obtain ⟨z,hz,hZ⟩:= Campus.allowance (I j).r P K ht he' hv hB hb
   choose F' hf hp using fun i:ι=> hZ (s i j) (y i j); let L'(i:ι):= confirm (ξ i) (F' i); let b'(i:ι):= confirm η (L' i); let u₀ : H₁:=.inl (.inr j); let L₁(i:ι):= atZero (b' i) u₀
   let C':=Qξ; have hh' : 0 ≤ C':= granted P K p x A ht
   let c':=1+(Fintype.card (Lobby P K G):ℝ)* C'; let c'':= 1+(Fintype.card H₁:ℝ)*(1:ℝ); let g(i:ι):= z*(f₀ i).budget μ; let C₁ i:= (c''^γ') *((c'^γ') *g i)
   have h₀ i: Belt (ξ i) b C':= tide P K p x A ht i; have hg:Belt η b 1:=paid_ramp _
   have hr:0 ≤ c':= by unfold c'; positivity
   have hr':0 ≤ c'':= by unfold c''; positivity
   have hX i :(L' i).Good b (c'^γ'*g i) (γ'):= Method.well _ (h₀ i) ht.le hh' _ (hp i); refine License.pure b L₁ C₁ ht ?_ (fun i=> ((usage _ _ (Method.well _ (hg) ht.le zero_le_one _ (hX i))).debt le_rfl le_rfl (by omega))) ?_
   · simpa only [Nat.zero_add] using! ((freeC _ (pow_nonneg hr' γ')).mul ((freeC _ (pow_nonneg hr γ')).mul ((freeC _ hz.le).mul (J' j))))
   intro i n hn; rw [dif_pos hn]; ext1 v; rw [Function.comp_apply,Finset.sum_apply, Field.table_apply]; refine Finset.sum_congr rfl fun a' _=>?_ ; unfold soldier L₁; rw [Chimney.larger]; change _= v _ *(confirm η (L' i)).site n a' v; rw [Method.looks _ hg _ _ ht.le zero_le_one _ (hX i)]; unfold L'; rw [Method.looks _ (h₀ i) _ _ ht.le hh' _ (hp i), hf i n hn,Loan.alloy,if_pos he] -- order looks arguments?
   let η₀:= (posture (aurora G M n) (interiorL P K G hn)); have hp:= important M (exteriorL G n) (interiorL P K G hn) v; let z':= (η₀) v; let h':= standing P K p x L Q hB hx A hn i; let X':= Loan.leafMatter (I j) (s i j) (sits P y n i j a') T[n]; let y':= Q[n,hn]; let x₀:= know η n v; have hF : Campus.read P K (s i j) a' hn (y i j) = X' ∘ ((y').toContinuousLinearMap):= by
      ext1 x; rw [Campus.read, ← arb P K hn]; rfl
   refine congr_arg₂ (·*·) rfl ?_; rw [hF, pivot ((y').toContinuousLinearMap) X' _ (Loan.healthy (I j) (s i j) (sits P y n i j a') T[n]|>.smooth)]; change Radial.jet X' γ' (goldL _ _ _) = Radial.jet X' γ' _; refine congr_arg _ ?_; have he := luna (exteriorL G n) (interiorL P K G hn) _ _ A₀[i,n,hn] (A.peak i) (A.deep i) (A.deep_bound i) (A.peak_bound i) ht.le A.nonneg.2 h'.2 h'.1 x₀; rw [← hp]; exact he.symm
end Aviary
end YM.QuadraticLocal.Sunrise
