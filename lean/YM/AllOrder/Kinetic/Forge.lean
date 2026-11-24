import YM.AllOrder.Kinetic.Office
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
abbrev candidates (P:Patch)(K:KernelChoices)(G:Gauge):= ∀ n:Side, Bid.Dir G n→ AxisChart G (trees P K n)
def proofC (F:ι→ candidates P K G):Prop:=∀ i n,Ad G P K n → Q.Service (S:=dock P K n) (trees P K n) p (x i) (F i n)
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
lemma tens (hx:∀ i,(x i).Bounds p a C (L i)): ∃ F:ι→ candidates P K G,proofC P K p x Q F:= by
 refine ⟨fun i n=> if hn:Ad G P K n then (Q.graph T[n] (S:=S[n]) (hx i) hn rfl rfl).choose else fun x=>0,fun i n hn=>?_⟩; simp only [dif_pos hn]; exact (Q.graph T[n] (S:=S[n]) (hx i) hn rfl rfl).choose_spec -- caution h scope
set_option quotPrecheck false
local notation "A[" i "," n "]"=> clay P K (x i) p n
local notation "u[" i "," n "]"=> Lapis.orbit T[n] (F i n)

include hx Q h
lemma rooted (i:ι)(hn:Ad G P K n) : Steered (clay P K (x i) p n) (Lapis.orbit (S:=S[n]) T[n] (F i n)):= interest T[n] (label S[n]) (x i) p Q hn (hx i) (h i n hn)
-- θTag `F`. may be arbitrary; Boost along real finite all.
omit hx Q h
def knight (n:Side)(i:ι) := ponant (clay P K (x i) p n) (Lapis.orbit (S:=S[n]) T[n] (F i n)) (pale P K (x i) O n)
def sun (k:ℕ)(j:ℕ)(i:ι)(n:Side) : rule Lℓ n→ℝ := if hn:Ad G P K n then outbound (exteriorL G n) (interiorL P K G hn) _ _ (rooted P K p x L Q hx F h i hn) volume (knight P K p O x F n i) k j else 0
-- cumbersome abbreviate
local notation "R"=> sun P K p O x L Q hx F h
variable (T:Passage P K p x Q) {i:ι}(hn:Ad G P K n)
local notation "T0" => heightV P K p Q
include hx Q h hB T
lemma valuation (hn:Ad G P K n) (i:ι) : let A0:=clay P K (x i) p n; let e:=arbitrate P K hn; let F:=x i; direct (T.leading i) n= Kinetic.mail (exteriorL G n) (interiorL P K G hn) A0 ∧ direct (T.inverted i) n=(Kinetic.pulse (exteriorL G n) (interiorL P K G hn) A0)⁻¹ := by
 intros; rw [pcs, meters, T.puts i n hn, T.exterior i n hn]; trivial -- maybe implicit n
include hO
lemma sunrise (hk:k≤N) : Apt (Ad G P K) L (R k 0) (k+2):= by
 let a0 n i:= knight P K p O x F n i; have hX (n i):Clear (a0 n i):= fun k=> impulse_cost ..
 have ht(i:ι)(n:Side)(hn:Ad G P K n) : R k 0 i n=a0 n i k ∘ arbitrate P K hn:= by unfold sun; rw [dif_pos hn,outbound, Fire.initial _ _ (u:= knight P K p O x F n i) (win0 _) (hX n i)]
 rcases k with _|k; · refine Apt.adapt (Apt.null _) fun i n hn=> ?_; rw [ht i n hn,show a0 n i 0=0 from (win0 _)]; rfl
 let A':= fun i=> mote P K p (x i) (k+1+2); let Z':=fun i=> wavelet P K O (x i) (k+1); let U:=fun i=> T.leading i; let V:=fun i=> T.inverted i; let H':=session P K p x Q T
 have hA:= Apt.scale (neophyte P K p x L Q hB hx (k+2) (by omega)) (-1); -- indices bind! (k+2+1) def k+1+2
 have hB':=(Apt.scale (amortize P K p O x L Q hB hx hO k (by omega)) (-1)).grow (show k+1 ≤ k+1+2 from (by omega)); let a':= heightV P K p Q; obtain ⟨hb,hD,hD'⟩:= receipts P K p x L Q hB hx; let he:= apex P K p x L Q hB hx T
 refine Apt.adapt (A:=fun i n=> ((-1:ℝ) • A' i n+(-1:ℝ) • Z' i n) ∘ know (H' i) n) (Apt.move he.1 hb he.2 (Apt.add hA hB')) (fun i n hn=> ?_)
 -- omit Frame.Cash premonition
 unfold A' Z'; rw [mote,dif_pos hn,wavelet,dif_pos hn, ht i n hn]; have hy:= valuation P K p x L Q hB hx F h T hn i; have Ht:= h i n hn; obtain ⟨c,hc⟩:=client P K (x i) O (n:=n) hO;
 exact (roses (exteriorL G n) (interiorL P K G hn) _ _ (morn P K (x i) O n) (rooted P K p x L Q hx F h i hn) _ (mist_nice T[n] O (x i) p Q (hx i) hO) (U i) (V i) (T.summit i) (T.head i) hb.le hD' hy.2 hy.1 c hc _ (by omega)).symm
end YM.AllOrder.Kinetic.Port
