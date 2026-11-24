import YM.QuadraticLocal.Poetry.Vernal
import YM.AllOrder.Haiku.Trunk
/-!
# Transfer of painted **aug workspace** across all windows
 From the existing pump comparison.Of.Rank. Allows overhead arbitrary in N and r.
 Need not keep sign, only any Life.Aug.P.S.Fore. for stationary coordinate path including gradient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary Ink.Echo Pointwise Further.PhysicalPeriodLimitF933 Shingle Macrame
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N p:ℕ} {ι:Type}[Fintype ι]
local notation "X"=> (Coarse G⊕ι)
local notation "E"=> Stationary.Link G n
variable {F: ℕ→Bills (Coarse G⊕ι)}{A: ℕ→ Ink.Field (Coarse G⊕ι)}
    {Ad:Side→Prop}{V : ℕ→ℝ}{Y : ℕ→ Side→ℝ}{b:ℕ→ℝ}{w:ℕ→ℕ}(H:∀ i≤N,Pert Ad (F i) (A i) (b i) (V i) (Y i) (w i))
    (hB:∀ i≤N,0<b i)(hV:∀ i≤N,Ink.Echo.Pulsed (Y i)) (hO:Often Ad)
open Ink.Field
namespace Glass
variable (n:Side)(v:ℝ→ rule (Coarse G) n)(s:rule ι n)(hv:ContDiffAt ℝ ω v 0)
local notation "W"=> Ink.Echo.amplify n
local notation "Ω"=> rule X n
local notation "E₀"=>Coarse G
abbrev loft (i:ℕ)(z:rule ι n)(T: ℕ→Bills (Coarse G ⊕ ι)) (x:Stationary.Link G n):=T i n (mingle x z)
def chord (x:ℝ):= mingle (v x) s
lemma jumped {m:Side}(q: Macrame.Window n m p)(x: rule (E₀) n): convey q (mingle x s)= mingle (convey q x) (convey q s):= by ext1 i; cases i with | mk z a=> cases a <;> rfl
include hv
lemma tacit : ContDiffAt ℝ ω (chord n v s) 0:= by
    unfold chord; exact ContDiffAt.comp (f:=fun r:ℝ=>(v r,s)) (g:=(desks (Coarse G) ι n).symm) _ ((desks E₀ ι n).symm.contDiff.contDiffAt) (hv.prodMk contDiffAt_const)
include H hB hV hO
set_option quotPrecheck false
local notation "T" i:max=> ((↑((i+1)^4:ℕ):ℝ)⁻¹)
lemma inspector {k:ℕ}(hk:k≤N): Tendsto (fun i=> (T i)*weigh (convey (Ink.Echo.arm n i) ∘ v) (fun j=> loft (W i) j (convey (Ink.Echo.arm n i) s) F) k) atTop (𝓝 (weigh v (fun j x=> ((A j).table n) (mingle x s)) k)):= by
 let v':=chord n v s; let A₀ l := fun f:(Ω→ℝ) => someJ (f ∘ v') l; let σ (i:ℕ):Window n (W i) ((i+1)^4):= Ink.Echo.arm n i
 unfold weigh; simp_rw [Finset.mul_sum]; apply tendsto_finsetSum; intro j hj; have hh:= (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hk; let L i:= F j (W i) ∘ convey (Ink.Echo.arm n i); have hχ:= familiar (k-j) v' (tacit n v s hv) (w j)
 have hq:= Ink.Echo.transported (Ink.Echo.arm n) (H j hh) (hV j hh) (Ink.Echo.limitless n) (hB j hh) hO (fun i=> pow_pos (Nat.succ_pos _) _) (A₀ (k-j)) hχ
 refine hq.congr' ?_; change ∀ᶠ i in atTop,A₀ (k-j) ((T i) • L i)= _; rcases hO with ⟨d,hx⟩; filter_upwards [(Ink.Echo.limitless n).eventually (eventually_ge_atTop d)] with i hi;
 have hz:Rank Ω (w j) (L i):= (((H j hh).fees (F j) (fun n=> by obtain ⟨f,d,v,h⟩:= hV j hh; exact (h _).1) (hB j hh) (hx _ hi)).2.1.lead (convey ..)); rw [show A₀ (k-j) ((T i) • L i)= _ from hχ.scale _ (T i) hz]; refine congr_arg ((T i) * ·) ?_; let q:=σ i; unfold v' L; apply congr_arg (fun p':ℝ→ ℝ=>someJ p' (k-j)); exact funext fun r=> congr_arg (F j (W i)) (jumped n s q (v r))
-- pump. hp independent enn; replicate ANY sizes. enough.Ad.
variable (hF:∀ c (z:rule ι c),Ad c→∀ k≤N,Vernal G c (fun i=> loft c i z F) k)
omit hv
include hF
lemma tomorrow {k:ℕ}(hk:k≤N): Haiku.Vernal G n (fun j x=> (A j).table n (mingle x s)) k:= by
 refine ⟨fun x y p z hx hy h he => tendsto_nhds_unique_of_eventuallyEq (inspector H hB hV hO n x s hx hk) (inspector H hB hV hO n y s hy hk) ?_⟩;
 rcases hO with ⟨d,hq⟩; filter_upwards [(Ink.Echo.limitless n).eventually (eventually_ge_atTop d)] with i hi;
 let Q:=Ink.Echo.arm n i; let x':= convey (α:=Coarse G) Q ∘ x; let y':= convey Q ∘ y; let P:ℝ→Site (W i)→G.El:= fun y=> (p y) ∘ Q.cut; have hP:Tendsto P (𝓝 0) (𝓝 (fun _=>z)):= tendsto_pi_nhds.mpr (fun j=> tendsto_pi_nhds.mp h _); apply congr_arg ((T i) * ·) ((hF (W i) (convey Q s) (hq _ hi) k hk).leaf x' y' P z ((convey Q).contDiff.contDiffAt.comp _ hx) ((convey Q).contDiff.contDiffAt.comp _ hy) hP ?_); -- bad placeholder
 have hQ (x:ℝ→Link G n)(v:ℝ):Haiku.life (convey Q ∘ x) v=Q.links (Haiku.life (G:=G) x v):= by unfold Haiku.life Response.echo; simp only [Function.comp_apply]; rw [← _root_.map_smul, billing]
 filter_upwards [he] with v hv; change Haiku.life y' v=Lattice.gauge (P v) (Haiku.life x' v); unfold x' y'; rw [hQ,hQ,hv,colored]
end Glass
end YM.AllOrder.Haiku
