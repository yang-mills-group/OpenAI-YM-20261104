import YM.Qlocal.Quipu.Pristine
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
namespace Macarons
-- global price of raw gauge estimates by unit tests & sums.Torus Orient. τ-derivatives. Lenses.Interfaces.
section sum
variable {Z X₀ : Type}[NormedAddCommGroup X₀][NormedSpace ℝ X₀] {f:Z→ℝ→X₀}
lemma billJ (s: Finset Z) (hf:∀ i∈s,ContDiffAt ℝ ω (f i) 0): someJ (fun x=>∑ i∈s,f i x) k=∑ i∈s,someJ (f i) k:=by
 unfold someJ; simp only [iteratedDeriv_eq_iteratedFDeriv]; rw [iteratedFDeriv_fun_sum_apply (fun i hi=> (hf i hi).of_le le_top), _root_.sum_apply]; exact Finset.smul_sum ..
lemma hourglass {f:ℝ→ℝ} (hf:ContDiffAt ℝ ω f 0)(Q:ℝ):someJ (fun t=>Q*f t) k=Q*someJ f k:= ((eo_Act k hf).smul Q).writes _ le_rfl
end sum
-- relevance α arbitrary
local notation "S"=> Coarse G
local notation "Z"=> Coarse G ⊕α
local notation "K"=>rule S n
open Tender
variable (s:Senses R)(z:α→ Site n) {c r:ℝ→ Ker.rule (Coarse G) n} (he:ContDiffAt ℝ ω c 0) (T:Tune ((Coarse G)⊕α))(h:T.typeR.Good a b k)(ha:0<a)
local notation "U"=> crystal R s.val z
include he in
lemma portraitMap {f:rule ((Coarse G)⊕α) n→ℝ} (hf: Rank _ k f): ContDiffAt ℝ ω (crystal R s.val z f ∘ c) 0:= by
 let g(x:rule (S⊕α) n):=|f x|; let B0:=Metric.closedBall (0:rule (Coarse G⊕α) n) 1; obtain ⟨v, hv⟩:= (isCompact_closedBall (0:rule (Coarse G⊕α) n) 1).image (continuous_abs.comp hf.read.smooth.continuous)|>.bddAbove; let h':= Tracks.embark hf (fun i hi=>(show |f i| ≤ v from hv (Set.mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hi)))); have ht':= ((Tender.charged z s.val h').2.1.read).smooth; exact ht'.contDiffAt.comp (f:=c) _ he
noncomputable def sampler (c:ℝ→ Ker.rule (Coarse G) n) (F:rule (Coarse G ⊕α) n →ℝ) (k:ℕ) := someJ (crystal R s.val z F ∘ c) k
local notation "Q"=> fun f :rule (Coarse G ⊕α) n→ℝ=> sampler s z c f N
include he
lemma reader : LinTest (rule ((Coarse G)⊕α) n) k (fun f=> sampler s z c f N):= by
 refine ⟨fun f g h1 h2=>?_, fun f t h=>?_ ⟩
 · have ht(x:ℝ): U (f+g) (c x)= U f (c x)+U g (c x):= (Tender.coin (c x) z _ k).add f g h1 h2; unfold sampler; rw [show (U (f+g)) ∘ c=_ from (show U (f+g) ∘ c=(U f ∘ c) +(U g ∘ c) from funext ht)]; exact jo_sum (portraitMap s z he h1) (portraitMap s z he h2)
 have ht(x:ℝ) : U (t• f) (c x)= t*U f (c x) := (Tender.coin (c x) z _ k).scale f t h; unfold sampler; rw [show U (t•f) ∘ c=(fun x:ℝ=>t*(U f ∘ c) x) from funext ht,hourglass (portraitMap s z he h)]
-- sum of all heart tissue.
abbrev unmapped (c:ℝ→ Ker.rule (Coarse G) n)(i:ℕ):ℝ→ℝ:=
     if hv:Dais.good s.val (chain (T.slip i)) then if Bay.Hears (hold hv) z then Ink.invoice (there z hv) (Dais.coin (T.slip i)) ∘ c else 0 else 0
-- heading lemma exact.
local notation "P₀"=> (T.typeR)
set_option quotPrecheck false
include h ha
lemma tissue : HasSum (fun i:ℕ=> T.fee i* someJ (unmapped s z T c i) N) (sampler s z c (T.typeR.table n) N):= by
 let Q' (f:rule (S⊕α) n→ℝ):= sampler s z c f N; let f i (j:Site n):= Ink.invoice j (T.slip i); let ht(j : Site n) := h.tests ha.le j (reader s z he (k:=k) (N:=N)); unfold Ink.Field.table; rw [ (reader s z he (k:=k)).finiteTest (Finset.univ:Finset (Site n)) _ (fun i _=>(Ink.Field.Good.site h ha.le i).2.1) (k:=k)]; refine ((hasSum_sum (s:=univ) (fun j (_:j∈(Finset.univ:Finset (Site n)))=> ht j))).congr_fun (fun i=>?_)
 change T.fee i * someJ (unmapped s z T c i) N= ∑ j:Site n, T.fee i*Q' (Ink.invoice j (T.slip i)); rw [← Finset.mul_sum]; apply congr_arg (T.fee i * ·); let x (j:Site n):ℝ→ℝ:= (U (f i j)) ∘ c; change _= ∑ j:Site n,someJ (x j) N; have hv(j):ContDiffAt ℝ ω (x j) 0:= portraitMap s z he (Ink.Field.ticket j (T.slip i)|>.2.1); rw [← billJ _ (fun j _=> hv j)]; apply congr_arg (fun f:ℝ→ℝ=> someJ f N); unfold unmapped; split
 next he=> ext1 y; split <;> rename_i hh
           · exact ((Dais.established z he (c y)).trans (if_pos hh)).symm
           exact ((Dais.established z he (c y)).trans (if_neg hh)).symm
 next hh=> exact funext fun y=>(faded z (c y) hh).symm
-- any policy σ
lemma priced(i:ℕ) : ContDiffAt ℝ ω (unmapped s z T c i) 0:= by
 unfold unmapped; split; swap; · exact contDiffAt_const
 split; · exact (Ink.Field.ticket ..|>.2.1.read.smooth.contDiffAt).comp _ he
 exact contDiffAt_const
-- helpers flop
end Macarons
end Incline
end YM.Qlocal.Quipu.Eluder
