import YM.Qlocal.Quipu.Vector
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Tilt
open AllOrder AllOrder.Ink Floe
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
local notation "R"=> heat P K p O x L Q hx hO F h V T
open Kinetic
open Extra.Iteration
variable (j:Age) (hh:∀ j∈T,∃ f:ι→ℝ,∃ s,0<s∧CreditF Γ l f∧b ≤ leaseF s N ∧ ∀ i, Charged (V i j) s (f i))
variable (α:Type)[Fintype α] [DecidableEq α]
local notation "I[" n "]"=> X[n] × rule α n
local notation "Y[" n "]"=> (I[n] × R[n])
local notation "E'"=> E⊕α
local notation "Q'"=> (E⊕α)⊕J
abbrev portal (G:Gauge)(α:Type)[Fintype α](n:Side): rule (Coarse G⊕α) n≃L[ℝ](Positions (Primary n G)×rule α n):= Kinetic.posture (exteriorL G n) (ContinuousLinearEquiv.refl ℝ (rule α n))
def passB (_ : Type) (v:Lℓ) : Q' := Sum.map (Sum.inl) id v -- need G inferred likely implicit. prefer
abbrev walkB {X Y E₀:Type} [NormedAddCommGroup X][NormedAddCommGroup Y][NormedAddCommGroup E₀] [NormedSpace ℝ X][NormedSpace ℝ Y][NormedSpace ℝ E₀]: ((X×Y)×E₀)→L[ℝ] X × E₀:= ((ContinuousLinearMap.fst ℝ X Y).comp (ContinuousLinearMap.fst ℝ (X×Y) E₀)).prod (ContinuousLinearMap.snd ℝ _ _)
variable (U:ι→(n:Side)→ Book ((Positions (Primary n G) × rule α n) × Poll.Body (Key (trees P K n) G))) -- pose homogenized
local notation "d[" n "]"=> portal G α n
local notation "Λ₀[" n "," hn "]"=> posture d[n] (interiorL P K G hn)
local notation "B[" i "," n "," hn "]"=> (castle A[i,n] u[i,n] A₀[i,n,hn])
set_option quotPrecheck false
def raycut (k:ℕ)(i:ι)(n:Side) : rule Q' n→ℝ:= if hn:I₀ n then U i n k ∘ Λ₀[n,hn] else 0
structure Tanner (U:ι→(n:Side)→ Book ((Positions (Primary n G) × rule α n) × Poll.Body (Key (trees P K n) G))) (Γ:ι→ℝ) (b:ℝ)(N l:ℕ):Prop where
    nil (i n) (hn:Ad G P K n) : U i n 0=0
    due i (h: i≤ N): License (Ad G P K) Γ (raycut P K α U i) b i l
    poses (i n) (hn:Ad G P K n) j : Rank _ j (U i n j) -- ALL orders for Book use.
-- full auxiliary orientation κ.H._F_ofFrame. pose generalized activity.Park.
set_option quotPrecheck false
def husky (i:ι) (n:Side)(hn:I₀ n): Book Y[n]:= fun k=> U[i,n,hn] k ∘ walkB
def action (U:ι→(n:Side)→(Ad G P K n)→ Book ((Positions (Primary n G) × rule α n) × Poll.Body (Key (trees P K n) G))) (k j :ℕ)(i:ι)(n:Side):rule Q' n→ℝ:= if hn: I₀ n then sojourn d[n] (interiorL P K G hn) B[i,n,hn] volume (U i n hn) k j else 0
local notation "V'"=> husky P K p O x L Q hx hO F h V T α
local notation "W'" => (fun i n (hn:I₀ n)=> V' i n hn+ U i n)
local notation "A'"=> action P K p x L Q hx F h α
variable (hU: Tanner P K α U Γ b N l)
section pose
variable (Y:ι→(n:Side)→(Ad G P K n)→ Book ((Positions (Primary n G) × rule α n) × Poll.Body (Key (trees P K n) G)))
    (hY:∀ i n hn, Clear (Y i n hn)∧ Y i n hn 0=0)
local notation "X♯"=> (fun i:ι=> expand (A.deep i) E')
include P Q hB hx F h A hY
lemma issued : Money.Code I₀ X♯ (A' Y):= by
 constructor
 · intro k i n hn; rw [action,dif_pos hn, sojourn, Fire.once (u:=Y i n hn) B[i,n,hn] (faces (interiorL P K G hn)) _ (hY i n hn).2 (hY i n hn).1]; rfl
 intro k r v n hn; unfold action; simp_rw [dif_pos hn]; apply torchlight _ (interiorL P K G hn) _ _ _ volume (hY v n hn).2 (hY v n hn).1; intro i j; rw [(standing P K p x L Q hB hx A hn v).2,spring _ _ _ _ A₀[v,n,hn]]
end pose
private lemma renew (hn:I₀ n): walkB ∘ Λ₀[n,hn]= Q[n,hn] ∘ (know (skirt (passB (G:=G) P K α α)) n) := by
 ext1 v; simp_rw [Function.comp_apply,knead]; rfl -- check passB arg ?
lemma furry (i:ι) (hn:I₀ n): Rank Y[n] (k+2) (V' i n hn k)∧ V' i n hn 0=0:=by
 constructor
 · unfold husky; apply Rank.lead; unfold Floe.books; exact impulse_rank ..
 unfold husky Floe.books; rw [Impulse,win0]; rfl
lemma post_m (i:ι)(hn:Ad G P K n) (y:rule (Coarse G⊕α) n)(P':ι→(n:Side)→(Ad G P K n)→ Book ((Positions (Primary n G) × rule α n) × Poll.Body (Key (trees P K n) G))) (hF:∀ k, Rank _ (k+2) (P' i n hn k))(he:P' i n hn 0=0): snapshot (A' P') k i n (know (day E' J) n y)= connected B[i,n,hn] volume (P' i n hn) k (d[n] y):= by rw [snapshot, Finset.sum_apply]; unfold action; simp_rw [dif_pos hn]; have hQ:= artist d[n] (interiorL P K G hn) B[i,n,hn] volume he k y hF; simp_rw [tablet] at hQ; simp_rw [tablet]; exact hQ
include hU hx Q ht hs hV hB hO A hL hh
local notation "T'"=> (l+8*(N+2))
set_option maxHeartbeats 480000 in
private lemma fareB (hk:k≤N) : W (A' (V') k 0) b (k+2) T':= by
 let v:= passB (G:=G) P K α α; have hz(i n hn):Clear (V' i n hn):=fun k=> ((furry P K p O x L Q hx hO F h V T α (k:=k) i hn).1).read; have ht' i n hn : V' i n hn 0=0:= (furry P K p O x L Q hx hO F h V T α (k:=k) i hn).2
 refine License.adapt (((Floe.corn P K p O x L Q hB hx hO F h V T hV Γ A ht hs hL hh hk).move (P:=fun _=>1) (freeC _ zero_le_one) ht (fun _=>skirt_rents v)).squeeze le_rfl le_rfl (by omega)) ?_; intro i n hn; rw [action, dif_pos hn, sojourn,Fire.initial (u:=V' i n hn) _ _ (ht' i n hn) (hz i n hn), Floe.revive P K p O x L Q hx hO F h V T hV i n hn k]; exact (congr_arg (fun G=> U[i,n,hn] k ∘ G) (renew P K α hn)).symm -- `i` args
local notation "Φ" => ((fun i n (hn:I₀ n) k=> connected B[i,n,hn] volume (W' i n hn) k - connected B[i,n,hn] volume (V' i n hn) k))
def driven (k:ℕ) (i:ι)(n:Side):rule E' n→ℝ:= if hn:Ad G P K n then Φ i n hn k ∘ d[n] else 0
set_option maxHeartbeats 1160000 in
lemma main (hk:k≤N): W (driven P K p O x L Q hx hO F h V T α U k) (chant b N (3*N)) k (Money.song T' (3*N)+4*N):= by
 let v:= V'; let w := W'
 have hv i n hn (k:ℕ): Rank Y[n] (k+2) (v i n hn k):= (furry P K p O x L Q hx hO F h V T α (k:=k) i hn).1; have hm i n hn k : Rank Y[n] (k+2) (w i n hn k):= Rank.add (hv i n hn k) ((hU.poses i n hn k).up (by omega))
 have hp i n hn : Clear (v i n hn) ∧ v i n hn 0=0:= ⟨fun k=> (hv i n hn k).read, (furry P K p O x L Q hx hO F h V T α (k:=k) i hn).2⟩; have hW i n hn : Clear (w i n hn) ∧ w i n hn 0=0:= ⟨fun k=>(hm i n hn k).read, show v i n hn 0+U i n 0=0 from (by rw [(hp i n hn).2,hU.nil i n hn, zero_add])⟩
 let d:=A.deep; let D i:= expand (d i) E'; let U':=A' w; let M':= A' v; have hxx i (h':i≤N) : W ((U'-M') i 0) b i T':= by
    apply License.adapt ((hU.due i h').squeeze le_rfl le_rfl (by omega)); intro j n hn; unfold U' M'; simp only [Pi.sub_apply]; rw [raycut, action, action, dif_pos hn,dif_pos hn,dif_pos hn,sojourn,sojourn,Fire.initial _ _ (u:=v j n hn) (hp j n hn).2 (hp j n hn).1,Fire.initial _ _ (u:=w j n hn) (hW j n hn).2 (hW j n hn).1]; ext1 x'; exact (show V' j n hn i _ + _-_= _ from add_sub_cancel_left _ _).symm -- ordering
 have hy:∀ i≤N,W (M' i 0) b (i+2) T':=fun i hi=>fareB P K p O x L Q hB hx hO F h V T hV Γ A ht hs hL hh α U hU hi -- order
 have hV':= rents_delta (issued P K p x L Q hB hx F h A α v hp) ht (freeC _ A.nonneg.2) (fun i=> Ink.bank (A.deep_bound i) E' A.nonneg.2) hy (issued P K p x L Q hB hx F h A α w hW) hxx hk
 let d' := fun i:ι=> day (E') J; let f:= chant b N (3*N); have hu:= soprano N ht (3*N)
 refine License.adapt ((License.move (hf:=fun i:ι=> (show Belt (d' i) f 1 from paid_day)) (freeC _ zero_le_one) hu hV').squeeze le_rfl le_rfl (by omega)) ?_; intro i n hn; funext y; rw [driven,dif_pos hn]; let Q₀:= know (d' i) n
 exact congr_arg₂ (· - ·) (post_m P K p x L Q hx F h α i hn y w (hm i n hn) (hW i n hn).2) (post_m P K p x L Q hx F h α i hn y v (hv i n hn) (hp i n hn).2)
end YM.Qlocal.Quipu.Tilt
