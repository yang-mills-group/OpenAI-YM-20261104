import YM.AllOrder.Floe.Treetop
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
local notation "R"=> heat P K p O x L Q hx hO F h V T
open Kinetic
open Extra.Iteration
variable (j:Age) (hh:∀ j∈T,∃ f:ι→ℝ,∃ s,0<s∧CreditF Γ l f∧b ≤ leaseF s N ∧ ∀ i, Charged (V i j) s (f i))
local notation "A'"=> (fun i:ι=> expand (A.deep i) (Coarse G))
local notation "I✧"=> snapshot R
include hx F h H A hO
include hB
lemma hearings : Code I₀ A' R:= by
 refine ⟨fun k i n hn=> ?_,fun k j i n hn=> ?_⟩
 · rw [heat,dif_pos hn,outbound]; rw [Fire.once (u:=U[i,n,hn]) _ (Kinetic.faces (interiorL P K G hn)) _ (win0 _) (fun i=> impulse_cost ..)]; rfl
 let W' := U[i,n,hn]; unfold heat; simp_rw [dif_pos hn]; exact light_home (u:=W') (exteriorL G n) (interiorL P K G hn) _ _ A₀[i,n,hn] (A.deep i) ((standing P K p x L Q hB hx A hn i).2) volume (win0 _) (fun k=>impulse_cost ..) j k
include ht hs hL
include hV hh
def diet (l N:ℕ):= Money.song (l+4*(N+2)) (3*N) +4*(N+2)
lemma corn (hk:k≤N) : W (R k 0) b (k+2) (l+4*(N+2)):= by
 let S (i:ι)(n:Side):= if hn:I₀ n then knight P K p O x F n i k ∘ arbitrate P K hn else 0
 let B (j:Age)(i:ι)(n:Side):= if hn:I₀ n then note_n (i:=j) T[n] (V i) D[i,n,hn] k ∘ arbitrate P K hn else 0
 let f (i:ι)(n:Side):= S i n+(-1:ℝ) • (∑ j∈ T,B j i n); let l':= l+4*(k+2);
 have ht' :W S b (k+2) l':= base_fund P K p O x L Q hB hx hO F h Γ A ht hs hL hk -- `B₀`
 refine License.squeeze (License.adapt (A:=f) (License.add ht' ((License.pile T (B) (fun i hi=> carry_in P K p O x L Q hB hx hO F h V T hV Γ A ht hs hL i hh hk hi) ht).scale (-1)) ht) ?_) le_rfl le_rfl (by unfold l'; omega)
 intro i n hn; rw [revive P K p O x L Q hx hO F h V T hV i n hn k, amber T[n] (V i) T _ (hV i)]; unfold f B S; simp_rw [dif_pos hn]; rw [neg_one_smul]; ext1 y; simp_rw [Function.comp_apply, Pi.sub_apply, Finset.sum_apply]; change (knight P K p O x F n i k _ + -_)= (knight P K p O x F n i k _)-_; rw [sub_eq_add_neg,Finset.sum_apply]; rfl
lemma silo (hk:k≤N) : W (I✧ k) (chant b N (3*N)) (k+2) (Money.song (l+4*(N+2)) (3*N)) := by
 refine (peakward (N:=N) (hearings P K p O x L Q hB hx hO F h V T A) (freeC _ A.nonneg.2) ht (fun i=> Ink.bank (A.deep_bound i) E A.nonneg.2) (l+4*(N+2)) (fun i hi=> corn P K p O x L Q hB hx hO F h V T hV Γ A ht hs hL hh hi) hk).squeeze (gestate N ht (by omega)) le_rfl (gesture _ (by omega))
omit H A ht hs hL hh
-- `prePhase` independent of choices proven; unoriented calculates one graph.STATIONARY root.
def prePhase (i:ι)(k:ℕ)(n:Side):rule (Coarse G) n→ℝ:= if hn:I₀ n then distilled (augment T[n] (V i) T D[i,n,hn] (hV i)) k ∘ exteriorL G n - if k=0 then baseStar P K p x F i n else 0 else 0
include H A ht hs hL hh
omit hh hL hV in
lemma full_floor : W (baseStar P K p x F) (chant b N (3*N)) 2 (diet l N):= by
    let f := fun i:ι=> mote P K p (x i) 2; let v:= d₀; let w:= fun i:ι=> day (Coarse G) (RealSlice.Vertical G P K)
    have hh i : Belt (w i) b 1:= paid_day; let Q' :=(advance_mote P K p x L Q hB hx Γ (k:=1) (by omega)).squeeze hs le_rfl (le_refl 0); have hx':License I₀ Γ (fun i n=>f i n∘know (v i) n) b 2 8:= river (k:=0) P K p x Γ A ht f Q'
    have ht':0<chant b N (3*N):= soprano N ht _;
    refine License.adapt ((License.move (P:=fun _=>1) (freeC _ zero_le_one) ht hh hx').squeeze (gestate N ht (show 0≤ 3*N from (by omega))) le_rfl ?_) ?_; swap
    · intro i n hn; ext1 y; unfold f v; -- alias problem
      have hz:= standing P K p x L Q hB hx A hn i; simp_rw [Function.comp_apply,mote,dif_pos hn,show know (w i) n y=mingle y 0 from tablet (β:=J) y]; exact (minimum (exteriorL G n) (interiorL P K G hn) _ _ A₀[i,n,hn] (A.peak i) (A.deep i) (A.deep_bound i) (A.peak_bound i) ht.le A.nonneg.2 hz.2 hz.1 0 y).symm
    unfold diet; have he:= gesture (l+4*(N+2)) (show 0≤3*N from (by omega)); rw [Money.song] at he; omega
local notation "u'" => prePhase P K p O x L Q hx hO F h V T hV
local notation "w₀" => day (Coarse G) (RealSlice.Vertical G P K)
omit hh A H ht hs hL in
lemma distant (i:ι) (hn:Ad G P K n) : u' i k n=(I✧ k i n) ∘ know (w₀) n-(if k=0 then baseStar P K p x F i n else 0):= by
 unfold prePhase; rw [dif_pos hn]; refine congr_arg (·-(if k=0 then baseStar P K p x F i n else 0)) ?_
 let X':= U[i,n,hn]; let B:= A₀[i,n,hn]; let Φ:=I✧ k i n; let v:= know (w₀) n; ext1 y; let y':= exteriorL G n y
 have hv : Φ (v y)= connected (castle _ _ B) volume X' k y':= by
     have H' z (k':ℕ) : R k k' i n z= outbound (exteriorL G n) (interiorL P K G hn) A[i,n] u[i,n] B volume X' k k' z:= by rw [heat,dif_pos hn]
     change (∑ j∈range (3*k+1),R k j i n) (v y)=_; rw [Finset.sum_apply]; simp_rw [H'];
     have hp:= posterior (u:=X') (exteriorL G n) (interiorL P K G hn) _ _ B volume (win0 _) k y (fun j=> impulse_rank ..)
     simp_rw [tablet] at hp; unfold v y'; simp_rw [tablet]; exact hp
 change Response.connected _ _ _ k y'= _; exact hv.symm
lemma awakes (hk:k≤N) : W (fun i=>u' i k) (chant b N (3*N)) (k+2) (diet l N):= by
 let w:= fun i:ι=> day (Coarse G) (RealSlice.Vertical G P K); let t:=chant b N (3*N); let s (i:ι)(n:Side):= if k=0 then baseStar P K p x F i n else 0
 have ht':0<t:=soprano N ht _; have hh' i:Belt (w i) t 1:= paid_day; let Φ (i:ι)(n:Side):= I✧ k i n ∘ know (w i) n; have hp : W s t (k+2) (diet l N):= by by_cases hk:k=0; subst k; unfold s; simp_rw [if_true]; exact full_floor P K p O x L Q hB hx hO F h Γ A ht hs; exact License.adapt (License.null _ ht') (fun i n hn=> by unfold s; rw [if_neg hk]; rfl) -- simplify
 have hv:W Φ t (k+2) (diet l N):= (License.move (P:=fun _=>1) (freeC _ zero_le_one) ht' hh' (silo P K p O x L Q hB hx hO F h V T hV Γ A ht hs hL hh hk)).squeeze le_rfl le_rfl (by unfold diet; omega)
 refine License.adapt (License.add hv (hp.scale (-1)) ht') ?_; intro i n hn; rw [neg_one_smul,← sub_eq_add_neg]; exact (distant P K p O x L Q hB hx hO F h V T hV i hn).symm
end YM.AllOrder.Floe
