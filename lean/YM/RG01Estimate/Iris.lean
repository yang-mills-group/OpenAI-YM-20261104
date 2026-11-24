import YM.RG01Estimate.Abacus
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Haul
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir
/-!
 # Exact stencil plus mask operation at prerealignment. Width reaches z.

   Path or residual log computations require per-label symmetries after regrouping --
   on the SAME complete polynomial. This is Vacuum only. Scalar α stays exact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Abacus.Rack
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Meadow Marlin Trio Slide
open Geo Footprint Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge}{c:Side}{A:Listing G c}{w r:ℕ} (B:BudgetPoint)
    (F : Collection.Source G c) {P U V: ℕ→ Config G c→ℝ} (p:Rack A r U)
    {Y : Stars→ Side} (a : ∀ i:Stars,Trio.Offer G (Y i)) (Q:∀ i: Stars,(Y i).val=2*(w+i.val))
    (k z:ℕ) (x:Site c) (W:Config G c)
local notation "θ" => (Trio.ornament Q a)
local notation "U₀" => p.polygon

def gap : Trio.Offer G c:= fun x W=> p.maskedEntry B x W - p.polygon x 1 - Trio.unearned B Q z (Trio.rip a) x W

local notation "g" => p.gap B a Q z
variable (hG: F.logRead=P+V+U) {sf v' e : ℝ} (hq: Meadow.Budget B A.reg U sf)
    (hP : Meadow.Budget B A.reg P v') (hV: Meadow.Budget B A.reg V e) (hM : Trio.Mirrors p.polygon)
include hG hV hM hP hq
lemma toll : (A.read F).additive B W = (A.read (revise F (P+V))).additive B W + (Fintype.card (Site c):ℝ) * p.polygon 0 1 +
   (∑ i:Site c, masked B.threshold (neighbors z i) (θ i) W) + ∑ i:Site c,g i W := by
   have h : (A.read F).additive B W=(A.read (revise F (P+V))).additive B W+∑ i:Site c,p.maskedEntry B i W:= by
     rw [← p.routes B W (revise F (P+V)),← adds_pow B W (show Meadow.Budget B A.reg (revise F (P+V)).logRead (v'+e) from pay_bundle B hP hV) hq]
     congr 3; exact congr_arg₂ Collection.Source.mk hG rfl
   have hv i : p.polygon i 1=p.polygon 0 1:= by
      have he:= hM (0:Site c) 1 i 1
      rw [show Lattice.affine 1 i (0:Site c)=i from by simp [Lattice.affine], show (pull 1 i 1:Config G c)=1 from by funext i; simp [Lattice.pull,Lattice.Step.read]] at he -- edit
      exact he.symm
   unfold ornament; rw [Trio.parade];  simp_rw [gap,hv,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,h]; ring

omit hG hP hV hM
variable (hk : 2*z ≤ k) (hw:w+4 ≤ z) {f : Stars → ℝ} (he: ∀ i j,B.Regular univ (a i j))
include hk hw he
lemma gap_tidy (h : r≤k) : Trio.Tidy B (neighbors k x) (g x) := by
  refine tidy_sub B (v:=Trio.unearned B Q z (Trio.rip a) x) (u:=p.maskedEntry B x- fun _ : Config G c=> (U₀) x 1) ?_ ?_
  · apply tidy_sub B _ (tidy_const ..); unfold Rack.maskedEntry
    apply tidy_sum; intro i hi
    by_cases h' : p.seat i x=0; · simp_rw [h',zero_mul]; exact tidy_const ..
    obtain ⟨_,_,hf⟩:=hq
    exact Trio.tidy_scale _ _ (tidy_mask _ (hf i).1 (fun j hj=>(neighbors_mem ..).mpr (((neighbors_mem ..).mp (p.priced i hi x h' hj)).trans h)))
  unfold Trio.unearned
  refine Trio.tidy_sum _ _ _ _ fun i hi=> Trio.tidy_scale _ _ (Trio.tidy_sum _ _ _ _ fun j hj=> Trio.tidy_mask _
     (Trio.unit_m B Q z a he hw (Trio.emerge Q i j x) i j) (Trio.patch Q z hw i j x hk))
omit he hq
lemma gap_fails (hp : 0<r) (hb:2*r ≤ w) (hc:4*r+16≤ c.val)(hY : Trio.CompatibleP B r p.polygon a) (h: g x W≠0): ¬Healthy B.threshold (neighbors k x) W:= by
   intro he; have h':= Trio.cruising B Q z (Trio.rip a) W x hw hb hk hc he _ (Trio.tinted _ _ hY) hp
   apply h; unfold gap; rw [h']; change _- (p.polygon x W - p.polygon x 1)=_; rw [p.chip_healthy _ _ _ (he.mono_left (fun j hj=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp hj).trans (by omega))))]; ring

omit hk
include hq
-- No derivative on Vacuum mask partners. Pay at full query V.
def beans {c:Stars→Side}(r:ℕ)(h:ℝ)(f:Stars→ℝ):= ((ballCost r:ℝ)*h+(ballCost r:ℝ)*h)+ ∑ i:Stars, |ray i| * (Fintype.card (Site (c i))*(f i+f i))
lemma priced_all (hf : ∀ i (W:Config G (Y i)), flags B.threshold W=∅ → ∀ j, ‖a i j W‖ ≤ f i):
    ‖g x W‖ ≤ beans (c:=Y) r sf f:= by
  have hv:= p.reserveW B W hq x
  have hs:(1:Config G c)∈ Boulevard.sunny B:= by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using B.threshold_pos -- parsing
  have hp:= p.grain B 1 hq x (Boulevard.smoky hs)
  exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add hv hp)) (Trio.stipends B W Q z a _ hf hw x))

end YM.RG01Estimate.Abacus.Rack
