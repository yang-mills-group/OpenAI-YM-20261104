import YM.AllOrder.Kinetic.Lily
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic.Port
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a C Λ:ℝ}{k N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)

-- ι neutral. require at least one input context. realized at scheduled Tube and full σ via graph. station choose irrelevance.
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ){L':ℕ}
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
    (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
local notation "Lℓ"=> Lobby P K G
-- frame model indexed k; numeric valuations
include hx Q hB
lemma reignQ : 0< (Z).gap ∧ 0<(Z).width ∧ 0<(Z).value ∧ 0<(Z).rate:= by
 obtain ⟨d,H⟩:= dock_larger P K hB; let c:Side:= ⟨d+1,by omega⟩; have he:= Q.full_pack T[c] (label S[c]) (hx (Classical.arbitrary ι)) (H c (by show d≤d+1; omega)) rfl rfl; exact ⟨he.2.1,he.2.2.1,he.2.2.2.2.1, he.2.2.2.2.2.2.1⟩

lemma basicK : 0< small_a (Z).width ∧ (∀ k:ℕ,0≤ revenue P K p Q k) := by
 let Y:= Z; have h:=reignQ P K p x L Q hB hx; exact ⟨div_pos h.2.1 (by norm_num), fun k=> mul_nonneg (mul_nonneg h.2.2.1.le (Real.exp_pos _).le) (boltC_pos k h.2.1).le⟩
lemma classicalChoice (k:ℕ) (hk:k ≤ N+2): ∃ F:ι→Fan Lℓ Lℓ k,(∀ i,Cap (F i) (small_a (Z).width) (revenue P K p Q k))∧ ∀ i n,Ad G P K n→ Ker.Start.billed P K (classicalT P K (x i) p) k n=pieces (F i) n := by
 choose F hF h using fun i=> class_pay P K (x i) p Q (hx i) hB (show k+1≤N+3 from (by omega)); exact ⟨F,hF,h⟩
include hO in
lemma thermalChoice (k:ℕ)(hk:k≤ N+2): ∃ f:ι→ℝ, Grade L f ∧ ∃ F:ι→Fan Lℓ Lℓ k,(∀ i,Cap (F i) (small_a (Z).width) (f i))∧∀ i n,Ad G P K n→ Ker.Start.billed P K (shadow P K O (x i)) k n=pieces (F i) n:= by
 choose F hF h using fun i=> (shadow_pay P K (x i) p O Q (hx i) hO hB (show k+1 ≤ N+3 from (by omega))).2
 let u:= Classical.arbitrary ι
 refine ⟨fun j=>revS P K p O Q (L j) k,?_, F, hF, h⟩
 let H:= hx u; have hz: 0<a:=H.width; let U:= (Z).width; let r:= atomCost G Q.Z a (N+3) 2;
 have hr:0≤r:= atomCost_nn («Z»:=Q.Z) (n:=N+3) (by have t:=Q.labels; exact ⟨t.1,fun x hx=>(t.2 x hx).order (by omega)⟩) hz _
 let V:=countCost (entryWidth (N+3) P.L a/2); have he: Grade L (fun i=>orbC P K Q (L i)):= Grade.mul (Grade.mul (givenG (fun i=>budget_nonneg (hx i).two)) (gia r hr)) (gia V (count_pos (half_pos (width_positive hz _ _))).le); exact ((he.add (gia (jacC O (N+3)) (by unfold jacC; exact Finset.sum_nonneg (fun _ _=> norm_nonneg _)))).mul (gia (Real.exp _) (Real.exp_pos _).le)).mul (gia (boltC k _) (boltC_pos k (show 0<U from (reignQ P K p x L Q hB hx).2.1)).le)

def mote (R:PathData G)(k:ℕ)(n:Side) : rule (Lobby P K G) n→ℝ:= if h:Ad G P K n then Radial.jet (clay P K R p n ∘arbitrate P K h) k else 0
def wavelet (R:PathData G)(k:ℕ)(n:Side): rule Lℓ n→ℝ:= if h:Ad G P K n then Radial.jet (morn P K R O n ∘ arbitrate P K h) k else 0
lemma neophyte (k:ℕ)(hk:k≤N+2): Apt (Ad G P K) L (fun i=>mote P K p (x i) (k+1)) (k+1) := by
 obtain ⟨F,hF,H⟩:= classicalChoice P K p x L Q hB hx k hk; let T i:= principal (F i); have he i:= pride (F i) (hF i) ((basicK P K p x L Q hB hx).2 k)
 let C' :ℝ:= Fintype.card (Lobby P K G) * ((Fintype.card (Fin k→Lobby P K G):ℝ)*(revenue P K p Q k)); let z:= (↑(Nat.factorial (k+1)):ℝ)⁻¹; refine Apt.pure _ (fun i=>(T i).scale z) (fun _=>|z| * C') (basicK P K p x L Q hB hx).1 (gia _ (mul_nonneg (abs_nonneg _) ((he (Classical.arbitrary _)).nonneg))) (fun i=> Ink.Field.scale_good _ (he i) z) (fun i n hn=>?_)
 rw [mote,dif_pos hn, Ink.Field.scale_table]; ext1 x'; change _*(iteratedFDeriv ℝ (k+1) _ 0 _) = z*(T i|>.table n x'); apply congr_arg (z*·); exact (Ink.beginning (F i) x' (hF i) ((basicK P K p x L Q hB hx).2 k) ((basicK P K p x L Q hB hx).1.le) ((arbC P K (x i) p hn k).symm.trans (H i n hn))).symm
include hO
lemma amortize (k:ℕ)(hk:k≤N+2): Apt (Ad G P K) L (fun i=> wavelet P K O (x i) (k+1)) (k+1) := by
 obtain ⟨f,hG,F,hF,H⟩:= thermalChoice P K p O x L Q hB hx hO k hk; let T i:= principal (F i); have he i:= pride (F i) (hF i) (hG.nonneg i)
 let L':ℝ:= Fintype.card Lℓ; let C':ℝ:= Fintype.card (Fin k→Lobby P K G); let z:= (↑(Nat.factorial (k+1)):ℝ)⁻¹
 refine Apt.pure _ (fun i=> (T i).scale z) (fun i=>|z| *(L'*(C'*f i))) (basicK P K p x L Q hB hx).1 ((gia _ (abs_nonneg _)).mul ((gia _ (Nat.cast_nonneg (Fintype.card Lℓ))).mul ((gia _ (Nat.cast_nonneg _)).mul hG))) (fun i=>Ink.Field.scale_good _ (he i) z) (fun i n hn=>?_)
 rw [wavelet,dif_pos hn, Ink.Field.scale_table]; ext1 x'; change z * (iteratedFDeriv _ _ _ _ _) = z * _; apply congr_arg (z*·); exact (Ink.beginning (F i) x' (hF i) (hG.nonneg i) ((basicK P K p x L Q hB hx).1.le) ((arbS P K (x i) O hn k).symm.trans (H i n hn))).symm
end YM.AllOrder.Kinetic.Port
