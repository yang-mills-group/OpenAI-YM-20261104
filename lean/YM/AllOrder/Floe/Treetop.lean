import YM.AllOrder.Floe.Terrace
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
variable {δ H:ℝ} (A : PortPre P K p x b δ H)(ht:0<b)(hs:b≤leaseF a N)
variable (hL : CreditF Γ l L)
local notation "U[" i "," n "," hn "]"=> books T[n] (V i) T D[i,n,hn]
local notation "A₀[" i "," n "," hn "]"=> (rooted P K p x L Q hx F h i (n:=n) hn)
local notation "d₀"=> stalk P K p x A
def heat (k j:ℕ)(i:ι)(n:Side):rule (Lobby P K G) n→ℝ:= if hn:I₀ n then Kinetic.outbound (exteriorL G n) (interiorL P K G hn) _ _ A₀[i,n,hn] volume U[i,n,hn] k j else 0
local notation "R"=> heat P K p O x L Q hx hO F h V T
open Kinetic
include hV
lemma revive (i:ι)(n:Side)(hn:Ad G P K n)(k:ℕ): R k 0 i n= U[i,n,hn] k ∘ arbitrate P K hn:= by
 unfold heat; rw [dif_pos hn]; have hz : Clear U[i,n,hn]:= fun j=> (impulse_rank ..).read;
 unfold outbound; rw [Fire.initial (u:=U[i,n,hn]) _ _ (win0 _) hz]
include A ht hB hs hL
open Extra.Iteration
variable (j:Age) (hh:∀ j∈T,∃ f:ι→ℝ,∃ s,0<s∧CreditF Γ l f∧b ≤ leaseF s N ∧ ∀ i, Charged (V i j) s (f i))
omit hB hV hs hL in
lemma river (M:ι→Ink.Money.Bills Lℓ)(hx:W M b (k+2) l) : W (fun i n=> M i n ∘ know (d₀ i) n) b (k+2) (l+4*(k+2)):= License.move (P:=fun _ : ι=> billH (Coarse G) (RealSlice.Vertical G P K) δ H) (freeC _ (granted P K p x A ht)) ht (tide P K p x A ht) hx
omit hV
-- caution river signature auto-includes hB? etc inspect. want macro `river` with minimal params.
include hh hV
lemma carry_in (hk:k≤N)(hj:j∈T) : W (fun i n=> if hn: I₀ n then note_n (i:=j) T[n] (V i) D[i,n,hn] k ∘ arbitrate P K hn else 0) b (k+2) (l+4*(k+2)):= by
 by_cases hK:j.e≤k; swap; · refine License.adapt (License.null _ ht) (fun i n hn=>?_); rw [dif_pos hn,frost_at _ _ T _ (hV i) hj (by omega)]; rfl
 obtain ⟨f,s,hP,hC,hX,hH⟩:= hh j hj; let M:= k-j.e+j.r; have hm : 0<M:= by unfold M Age.r; omega
 have hm' : M ≤ k+2:= by unfold M; have hi:=j.pricey; omega
 obtain ⟨m',he⟩:= Nat.exists_eq_succ_of_ne_zero hm.ne'; have he₁ :k-j.e+j.r=m'+1:=he
 let v:=landV P K V j (m'+1);
 have hv:W v b (k+2) l:= (advance_atom P K Q hB V Γ j ⟨f,hC,hH⟩ hP (k:=m') (by omega)).squeeze hX (by omega) le_rfl
 apply License.adapt (river P K p x Γ A ht v hv); -- arg test
 intro i n hn; unfold v landV; rw [dif_pos hn,dif_pos hn]; let t' :=T[n]; let S':= S[n]; let q:=Q[n,hn]; let X':= far T[n] (V i) j; let F':= D[i,n,hn]
 rw [lush _ _ T _ (hV i) hj hK]; ext1 y; have hx':ContDiffAt ℝ ω X' 0:= (far_capsule T[n] (V i) T (hV i) hj).1; change jet (X'∘(q).toContinuousLinearMap) _ _= jet X' _ (goldL _ _ _); rw [he₁,pivot (q).toContinuousLinearMap X' _ hx']; let a:=A.peak i; let v':=A.deep i; have hv:= standing P K p x L Q hB hx A hn i; have he:= luna _ _ _ _ A₀[i,n,hn] a v' (A.deep_bound i) (A.peak_bound i) ht.le A.nonneg.2 hv.2 hv.1 y; exact congr_arg (jet X' _) he
omit hV hh
include Q hx hO F h
lemma base_fund (hk:k ≤ N) : W (fun i n=> if hn:I₀ n then knight P K p O x F n i k ∘ arbitrate P K hn else 0) b (k+2) (l+4*(k+2)):= by
 by_cases hp:k=0; swap; · obtain ⟨j,hj⟩:= Nat.exists_eq_succ_of_ne_zero hp; subst k; let A' := fun i=> mote P K p (x i) (j+1+2); let Z':= fun i=> wavelet P K O (x i) (j+1); let M:=fun (i:ι) (n:Side)=> (-1:ℝ) • A' i n + (-1:ℝ) • Z' i n; have hm : W M b (j+1+2) l:= License.add (((advance_mote P K p x L Q hB hx Γ (k:=j+2) (by omega)).squeeze hs (le_refl (j+2+1)) (Nat.zero_le _)).scale _) (((advance_loop P K p O x L Q hB hx hO Γ hL (k:=j) (by omega)).squeeze hs (show j+1 ≤ j+1+2 by omega) le_rfl).scale _) ht; apply License.adapt (river P K p x Γ A ht M hm); intro i n hn; unfold M A' Z'; rw [mote,dif_pos hn,wavelet,dif_pos hn,dif_pos hn]; have hv:= standing P K p x L Q hB hx A hn i; obtain ⟨c,hc⟩:=client P K (x i) O (n:=n) hO; exact (roses (exteriorL G n) (interiorL P K G hn) _ _ (morn P K (x i) O n) A₀[i,n,hn] _ (mist_nice T[n] O (x i) p Q (hx i) hO) _ _ (A.deep_bound i) (A.peak_bound i) ht.le A.nonneg.2 hv.2 hv.1 c hc (j+1) hp).symm
 refine License.adapt (License.null _ ht) (fun i n hn=>?_); rw [dif_pos hn,hp,show knight P K p O x F n i 0=0 from win0 _]; rfl
end YM.AllOrder.Floe
