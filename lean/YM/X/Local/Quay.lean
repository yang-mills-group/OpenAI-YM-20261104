import YM.X.Shelf.Corn
import YM.X.Chili.Cumin
/-!
# Passing to local aperture on periodic Cover kernels. Crystal analytic estimates. Use normalized BOTE scaling tower. ζ orientation later.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crystal
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Stems Hinge Clove Haze Grow Shelf Ocean Fielding
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d :ℕ}{G:Gauge}{R r:ℝ}
local notation "e"=>epsilon q
local notation "L"=> (atTop:Filter ℕ)
variable (φ: Floor R)
local notation "θ" => Floor.maskL q φ
local notation "K"=>Curly G
local notation "H"=> Hair G

def load (q:ℕ+)(P: Word G): ℕ→ Curly G:= fun i=>milk (flow G (side q i)) (bookMark P 0)
abbrev warp (q:ℕ+)(P:Word G)(φ:Floor R): ℕ→ Curly G:= fun i=> crisp P (Floor.maskL q φ i) (side q i)
variable {A:ℕ→Brush G}{B:Rich G} (P:Word G)
def ember (q:ℕ+)(P:Word G): Deck G:= purseM q (fun i _=> load q P i) (∑ x:PlaqAxes,floatP true (vertex x))
include hq φ in
lemma ember_cost (hr:R<r)(h:Tide q r A)(hs:Grasp B)(ht:Fill (gate q r) (fun i=>e i^(d+1)) d 0 A (emerge q B)): Grove q R A B d (P.d+4) (ember q P):= by
   apply (mixed_gr hq (φ.positive.le) hr h hs ht (self_ping hq P (φ.positive.le)) (Jar.fin Finset.univ (fun i _=>Jar.venue (q:=q) (R:=R) true (fire_verse (G:=G) i)))).2 -- include φ
lemma ember_point : multi (flow G (side q k)) (load q P k) (fireMask (θ k))= beadR (θ k) ((ember q P) k):= by
   unfold fireMask; let f(z:Cover) :=∑ i:PlaqAxes, flashVertex (G:=G) (z,i); let p:= (flow G (side q k)); let M:= (toned p (load q P k)).restrictScalars ℝ; change M (beadR _ f) = _ ; rw [beadLm]; apply congr_arg; funext z; unfold ember; simp_rw [purseM, Finset.sum_apply]; unfold f; simp_rw [dress_fire];rfl
lemma warp_embryo: warp q P φ k= milk (flow G (side q k)) (bookMark P 1)- beadR (θ k) ((ember q P) k):= by rw [warp,crisp, ← show load q P k=milk _ _ from rfl, ember_point]
variable {p: Deck G}
def clockLeaf {d:ℕ}(i:ℕ)(B:Long G):Curly G →ₗ[ℂ] ℂ := (probeL B).toLinearMap ∘ₗ (weightedHomogeneousComponent (vapor G) i) ∘ₗ (trumpet (Okay G) (valP (G:=G)) d).toLinearMap -- uses d implicit (includes? !)
def shineP (B:Long G)(d:ℕ): Curly G→ₗ[ℂ] ℂ:= (probeL B).toLinearMap ∘ₗ bloom d
lemma clock_sample (p:Deck G) (d i j:ℕ)(f:Rich G): wreath j d f p i= fun z=> clockLeaf (d:=d) j (f i) (p i z) := rfl
-- Li calculations
variable {S:ℕ→Lane}
lemma loaf (u:ℝ)(m:Lane) (p:Deck G)(f:Rich G): u • clockLeaf (d:=d) k (f n) (beadR m (p n)) = beadR m (fun z=> u • wreath k d f p n z):= by
    let c:= u • (clockLeaf (d:=d) k (f n)).restrictScalars ℝ; change c _= _; exact beadLm m c (p n)
lemma load_sauce {j:ℕ}(X:Rich G)(U:ℕ→Brush G)(u:ℝ): u • (snap (U j) (beadR (S j) (p j))-shineP (X j) d (beadR (S j) (p j)))= beadR (S j) (fun z=> u • ((exitP U p - cake d X p) j z)):= by
    let c:= u • (((snap (U j)).toLinearMap-shineP (X j) d).restrictScalars ℝ); exact beadLm (S j) c _

include hq φ
variable (hr:R<r)(h:Tide q r A)(hs:Grasp B)(ht:Fill (gate q r) (fun i=>e i^(d+1)) d 0 A (emerge q B))
lemma drift (hz:Grove q R A B d (d+4) p): Released (fun i=> e i ^(-(d:ℤ)) • (snap (A i) (beadR (θ i) (p i))-shineP (emerge q B i) d (beadR (θ i) (p i)))) := by
   simp_rw [load_sauce (S:=θ)]; let X:= exitP A p - cake d (emerge q B) p; have hh := (Visa.asPow (c:=(-(d:ℤ))) hz.2); exact mask_won hq φ hh (by omega) (by omega)
lemma hum (hh:Grove q R A B d (d+4) p)(he:k≤d){f:Rich G}(hv:Grasp f): Tendsto (fun i=> e i • clockLeaf (d:=d) k (f i) (beadR (θ i) (p i))) atTop (𝓝 0):= by
   have hz := Visa.asPow (c:=(1:ℤ)) (imprint hh hv he); have ht := mask_special hq φ hz (by omega) (by omega); unfold influx at ht; simp_rw [zpow_one] at ht;simp_rw [loaf];exact ht
end YM.PositionX.Crystal
