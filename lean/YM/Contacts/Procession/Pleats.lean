import YM.Contacts.Procession.Bowling
import YM.Contacts.Procession.Conduit
/-!
# Projection authority & call eligibility on genuine Mark requests.

Here each epoch optional source address is still an input label, no silently
paying for all closed channels. Π reads `(outputGrade, input-test-letter θ,
order n)` etc. Low-charge and horizon integer inequalities are used as Clock.
Not announcing the complete Mark RG estimate here.Field coordinates.real etc.
-/
noncomputable section
namespace YM.Contacts.Procession.Cartons
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open MeasureTheory Labels Source Drops Analysis Finset Bloch Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine Origin
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor MultiNext.SignedSource Pattern Shuttle Tide Morning Mediator Next.Foundations
open Barrage Barrage.Reserve Barrage.Reserve.Oasis Welcome Birth Catch Port Larch
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff Matrix.Norms.Frobenius
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000
set_option autoImplicit false
variable {G:Gauge}{F:Cohort G}{h d k p i n v:ℕ}{X Y:Type}{σ:ℝ≥0}{b:ℝ}(B: Labels.Frame G d)
section warm
variable (e:Oasis G)
def hose (q:ℕ)(i:ℕ):ℝ:= q.factorial * Real.exp 1*(e.Z i)^q
lemma hail_caps (i b:ℕ): hail b (e.ξ i)≤ hose e b i:= by
   let u:ℝ:= e.Z i; let t:=(e.ξ i:ℝ); have hu:0<u:=e.z_pos _; have h:t=u⁻¹:=rfl; have ht:t≤1:= NNReal.coe_le_coe.mpr (e.ξ_one _); change _ ≤ _*u^_; unfold Shuttle.hail; change (_*Real.exp t/t^b) ≤ _; rw (occs:=.pos [2]) [h]; rw [inv_pow]; rw [div_inv_eq_mul]; gcongr
def joss (h n k i:ℕ) : ℝ:= ∑ r:Fin (k+1), ( (h:ℝ)+1)^r.val* hose e (h*r.val) i -- n dummy
lemma fair_hose (k:ℕ): e.Fair (hose e k) := (e.fair_const ((k.factorial:ℝ)*Real.exp 1) (by positivity)).mul (e.fair_z.pow k)
lemma fair_joss (h k i:ℕ): e.Fair (joss e h h k):= Fair.sum univ (fun i _=> (e.fair_const _ (by positivity : 0 ≤ ((h:ℝ)+1) ^(i.val:ℕ))).mul (fair_hose e (h*i.val)))
private lemma runner {E Z:Type}[NormedAddCommGroup E](v:Z→E){a:ℝ}(h:SumBudget (fun i=> ‖v i‖) a): ‖∑' i,v i‖ ≤ a:= (norm_tsum_le_tsum_norm h.2.1).trans h.2.2
private lemma dash (F: Field (Fin k) (Node (Dyes G))) (b:ℝ)(x:Dyes G) (hf:Rest (terrain (e.ξ i) _) (0,x) F b)(n:ℕ): ‖sheet k F (Tide.lens G n)‖≤ b * (( (n:ℝ)+1)^k* hose e (n*k) i):= by
   let H:= blanket_spend hf (e.ξ_pos i) (by positivity : 0≤(n:ℝ)+1) (glaze G n); unfold Shuttle.sheet; refine (runner (blanket k F (Tide.lens G n)) H).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hail_caps e i _) ?_) hf.cash); positivity
lemma hefty (k i:ℕ)(hd:0≤b) (x:Dyes G)(h:∀ r≤k,Rest (terrain (e.ξ i) _) (0,x) (F r) b): ‖tower F d k‖ ≤ b*joss e (d*(d+1)) (d*(d+1)) k i:= by
   let z:= (d*(d+1)); let w:= joss e z z k; have hl(r:Fin (k+1)):0≤ ((z:ℝ)+1)^r.val*hose e (z*r.val) i:= mul_nonneg (by positivity) ((fair_hose e (z*r.val)).bank i); refine (pi_norm_le_iff_of_nonneg (mul_nonneg hd ((fair_joss e z k 0).bank i))).2 ?_; intro u; exact (dash e _ b x (h u.val (by have hv:=u.isLt; omega)) z).trans (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun r:Fin (k+1)=> ((z:ℝ)+1)^r.val*hose e (z*r.val) i) (fun A _=>hl A) (Finset.mem_univ u)) hd)
-- economy issuance actual through all periods arbitrary eligibility.Reserve.H. ξ marker.Fair. no scaling loss N-coordinates. number h=grade output, threshold offset not burning real ex.
theorem vp_funding (v:B.Index) : e.Permit (fun i c=>∀ (T:Cohort G), Tags T→∀ x:Dye G,∀ b≥(0:ℝ),(∀ r≤ (B.grades v).2, Rest (terrain (e.ξ i) _) (0,x) (T r) b) → ‖velum B T v‖ ≤ c*b) := by
    obtain ⟨a,ha,h⟩:= prices v; let k:=(B.grades v).2; let w:= d*(d+1); refine ⟨(fun i=>a*joss e w w k i),(e.fair_const a ha).mul (fair_joss e w k 0), fun i T ht x b hb hh=> ?_⟩; exact (h T ht).trans ((mul_le_mul_of_nonneg_left (hefty (d:=d) e _ i hb x hh) ha).trans_eq (by unfold k w; ring))
end warm
section evening
open Pigment
variable {B}
abbrev streams (B:Labels.Frame G d)(X: Cards→bore G)(p:ℕ)(h:ℕ):(Cards → ℕ→B.Index→ℝ):= fun v i j=> fill B p (X v) i j -- h dummy
-- Marker vanishing. Tickets hold for this actual sector.
theorem stem_mark {V: Cards → bore G}(h:Puppet G p V) (y:Dye G)(n k r:ℕ)(hn:n≤d)(hp:r=n+1-k) (H:∀ j<r,∀ f:Cards,Powers.home f.val j →∀ (q:B.Index), (B.grades q).1 ≤ n-j → ∀ i, fill B p (V f) i q=0): Clear (fun v=>coil (V v) p i k) r := by
    choose s U hs ht using h.forecast y; have hx b l := coil_tags (h.holds b) (ht b) (hs b) l;
    apply Clear.across (u:=d*(d+1)) (d:=d) (h:=n) (n:=d) (f:=fun v=>coil (V v) p i) (fun v=>hx v i) (by omega) hn hp le_rfl le_rfl; intro b j hj he; apply silent_projection B (hx b i) (by omega) le_rfl le_rfl; intro t ht'; rw [← charter (hx b i) t,fueled (h.holds b) y (hs b) (ht b) _ t]; split; rw [H j hj b he t ht']; all_goals rfl
end evening
end YM.Contacts.Procession.Cartons
