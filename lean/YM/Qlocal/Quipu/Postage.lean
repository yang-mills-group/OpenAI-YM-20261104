import YM.Qlocal.Quipu.Shore
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Tern
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial AllOrder Fire Laplace Laplace.SigmaP Ker Ker.Start
open Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Tilt
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{c r:Side}{a b C D Λ σ:ℝ}{k N l i j n m:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
variable {α:Type}[Fintype α] [DecidableEq α] {B:Marker.Census α}
local notation "Y"=> ((Coarse G⊕α)⊕ J)
local notation "Ω[" n "]"=> rule ((Coarse G⊕α)⊕J) n
-- true REAL inputs Art.authorization on SOLD analytic by unshifted paint opportunity. coordinates include spect.S. Paper knows fixed phase of each slot. not arbitrary θ.
variable {ι:Type}[Nonempty ι](t:Senses B)(p:ι→α→Site P.L) (π:ι→ℕ→Prop)(A:ι→ Album ℕ t G i) -- G implicit, length.Are fixed
set_option quotPrecheck false
local notation "w"=> (funds P G α t i k N σ (a/2))
def γ (N:ℕ)(a:ℝ) (P:Patch) := small_a (weaker N (chip P N a))
open Album Arbor
variable (M L:ι→ℝ) (hM:∀ i,Health (a:=a) (A i) (M i))(hL:CreditF L l M)(ha:0<a)(hQ:PaintSupply G N σ)(hp:P.Branches K G)
local notation "v"=> γ N a P
-- exact.Lensing.K.iq.Lookup. pure. width fee `same general`.Need value n=0.
include hQ hp ha hM hL
local notation "C0"=> rateF P G B t i k N j a σ
def reckoned (i₀:ι) (n:Side) := jet (heightZ P K t (p i₀) (π i₀) (A i₀) n k) j
local notation "H"=> (heightZ P K t)
lemma blessed (hk:j+1≤N) : License (Ad G P K) L (reckoned P K t p π A (j:=j+1) (k:=k)) (γ N a P) (j+1) l:= by
 choose f hf ht using fun i=> qualified P K t (p i) (π i) (A i) (hM i) ha hQ hp (k:=k) hk
 let Γ:=γ N a P; let T i:= principal (f i); have he i:= pride (f i) (hf i) (show 0 ≤ C0*M i from mul_nonneg (fees_ge P K t (A i) (hM i) ha hQ hp) (hL.nonneg i)) -- i shadows macro! C0 include `i` from header.Ph checked flags
 have hx : 0<C0+1 := (by have h:=fees_ge (j:=j) (k:=k) P K t (A (Classical.arbitrary ι)) (hM _) ha hQ hp; linarith); have h0:0≤ C0:= fees_ge P K t (A (Classical.arbitrary ι)) (hM _) ha hQ hp; let r:ℝ:= ((j+1).factorial:ℝ)⁻¹; have h':CreditF L l (fun i=> |r| *(Fintype.card Y*((Fintype.card (Fin j → Y):ℝ)* (C0*M i)))):= by
     simpa only [Nat.zero_add] using! ( (freeC _ (abs_nonneg r)).mul ( (freeC _ (Nat.cast_nonneg (α:=ℝ) (Fintype.card Y))).mul ((freeC _ (Nat.cast_nonneg (α:=ℝ) (Fintype.card (Fin j→Y)))).mul ( (freeC _ h0).mul hL))))
 have hs: 0 < Γ:= div_pos (squeezes P K t (A (Classical.arbitrary ι)) (hM _) ha hQ hp) (by norm_num)
 refine License.pure _ (fun i=>(T i).scale r) _ hs h' (fun i=> Ink.Field.scale_good _ (he i) _) ?_; intro i n hn; rw [Ink.Field.scale_table]; ext1 x; change r* (pageT _ _ _ _ _ (A i) k j n (fun _=>x))= r* (principal (f i)).table n x; exact congr_arg _ (Ink.beginning (f i) x (hf i) (mul_nonneg h0 (hL.nonneg i)) hs.le (ht i n hn)).symm
-- no scalar occupancy. use also at k=0 n=0 κ.Exp (v can depend i?). 
lemma into (hk:j ≤ N): License (Ad G P K) L (reckoned P K t p π A (j:=j) (k:=k)) (γ N a P) j l:= by
 rcases j with _|j; swap; · exact blessed P K t p π A M L hM hL ha hQ hp hk
 refine License.adapt (License.null _ (show 0< γ N a P from div_pos (squeezes P K t (A (Classical.arbitrary ι)) (hM _) ha hQ hp) (by norm_num))) (fun i n hn=> funext fun x=>?_); unfold reckoned; rw [jet_zero, heightZ,dif_pos hn, Finset.sum_eq_zero]
 intro u hu; have he(v₁:Places t n): placard v₁ (lands (G:=G) P K 0)=0:= Finset.prod_eq_zero (i:=pivot t) (Finset.mem_univ _) rfl; unfold ridge Arbor.village Arbor.mass; simp_rw [he,mul_zero,ite_self,tsum_zero]
end YM.Qlocal.Quipu.Sonnet.Tern
