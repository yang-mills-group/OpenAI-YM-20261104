import YM.AllOrder.Ink.Echo
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Echo
open Money Pointwise Further.PhysicalPeriodLimitF933 Shingle Macrame
variable (n:Side)
def amplify (n:Side)(k:ℕ):Side:= ⟨n.val*(k+1),Nat.mul_pos n.property (Nat.succ_pos k)⟩
def arm (n:Side)(j:ℕ) : Window n (amplify n j) ((j+1)^4):= Macrame.normal ⟨j+1,rfl⟩ rfl
lemma limitless (n:Side) : Tendsto (fun i=> (amplify n i).val) atTop atTop:= by
 refine tendsto_atTop_mono ?_ tendsto_id; intro i; change i≤ n.val*(i+1); exact (Nat.le_succ i).trans (Nat.le_mul_of_pos_left _ n.pos)
local notation "W"=>amplify n
local notation "Ω"=>rule α n
variable {F : ℕ→Bills α}{P D : ℕ→ℝ}{A:ℕ→Field α}{K:ℕ→Side→ℝ}{Ad:Side→Prop}
    (H:∀ k≤N,Pert Ad (F k) (A k) (D k) (P k) (K k) (k+2)) (h:∀ k≤N,Pulsed (K k)) (hD:∀ k≤N,0<D k) (h0:Often Ad)
variable (v:ℝ→ rule α n)(hv:ContDiffAt ℝ ω v 0)
include H h hD h0 hv
lemma inspect {k:ℕ}(hk:k≤N): Tendsto (fun i=> ((↑((i+1)^4:ℕ):ℝ)⁻¹)*weigh (convey (arm n i) ∘ v) (fun j=> F j (W i)) k) atTop (𝓝 (weigh v (fun j=> (A j).table n) k)):= by
 let A₀ l := fun f:(rule α n→ℝ) => someJ (f ∘ v) l; let T (i:ℕ): ℝ:= ((↑((i+1)^4:ℕ):ℝ)⁻¹); let σ (i:ℕ):Window n (W i) ((i+1)^4) := arm n i
 unfold weigh; simp_rw [Finset.mul_sum]; apply tendsto_finsetSum; intro j hj; have hh:= (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hk; let L i:= F j (W i) ∘ convey (arm n i); have hq:= transported (arm n) (H j hh) (h j hh) (limitless _) (hD j hh) h0 (fun i=> pow_pos (Nat.succ_pos _) _) (A₀ (k-j)) (familiar _ v hv _) -- order explicit n?
 refine hq.congr' ?_; change ∀ᶠ i in atTop,A₀ (k-j) (T i • L i)= T i * A₀ (k-j) (L i); rcases h0 with ⟨d,hx⟩; filter_upwards [(limitless n).eventually (eventually_ge_atTop d)] with i hi;
 have hz:Rank _ (j+2) (F j (W i)):= ((H j hh).fees (F j) (fun n=> by obtain ⟨f,v,d,h⟩:= h j hh; exact (h _).1) (hD j hh) (hx _ hi)).2.1; exact (familiar (k-j) v hv (j+2)).scale _ (T i) (hz.lead _)
lemma index {w:ℝ→ rule α n}(hw:ContDiffAt ℝ ω w 0) (hk:k≤N) (he: ∀ c, ∀ p,∀ t:Macrame.Window n c p,Ad c→ weigh (convey t ∘ v) (fun j=> F j c) k= weigh (convey t ∘ w) (fun j=> F j c) k): weigh v (fun j=> (A j).table n) k=weigh w (fun j=>(A j).table n) k := by
 refine tendsto_nhds_unique_of_eventuallyEq (inspect n H h hD h0 v hv hk) (inspect n H h hD h0 w hw hk) ?_; rcases h0 with ⟨d,hd⟩; filter_upwards [(limitless n).eventually (eventually_ge_atTop d)] with i hi; exact congr_arg _ (he _ _ _ (hd _ hi))
end Echo
end YM.AllOrder.Ink
