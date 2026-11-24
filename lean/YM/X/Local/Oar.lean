import YM.X.Local.Rack
import YM.X.Local.Oni
/-!
# aperture limit on nonphysical Ward slots as convergent sequences (explicit θ tilt and boundary terms, not Gram fitting).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crystal
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Stems Hinge Clove Haze Grow Shelf Ocean Fielding CellsInt
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d:ℕ}{G:Gauge}{R r:ℝ}
local notation "Λ"=>(atTop:Filter ℕ)
local notation "K"=>Curly G
local notation "e"=>epsilon q
variable (A: Okay G k) (φ:Floor R) (P:Word G) (x:Long G)
local notation "Θ"=> Floor.maskL q φ
local notation "D"=> P.d
local notation "Q"=> (warp q P φ)
def deliver (q:ℕ+)(A: Okay G k)(a:Axis)(P:Word G): Deck G:= purseM q (fun i _=> load q P i) (fun (i:ℕ) z=> epsilon q i ^ (k+1) • stepCloud (Reed.phase A) a z)
include hq φ in
lemma delivers (hd:m≤P.d)(a:Axis)(p:Rich G)(he:Grasp p): Visa q R (m-P.d:ℤ) (m-(P.d+3:ℕ):ℤ) (fun i z=> e i ^(m-P.d:ℤ) • wreath m P.d p (deliver q A a P) i z):= by
   obtain ⟨B,hB,h⟩:= Grasp_cover (d:=P.d) hq (show 0<R+1 from by linarith [φ.positive]) (Tide.empty (q:=q) (G:=G)); have hm := imprint (mixed_gr (n:=P.d) (m:=3) hq φ.positive.le (lt_add_one R) Tide.empty hB h (self_ping hq P φ.positive.le) (step_L hq A φ a)).2 he hd; simpa only [add_zero] using! Visa.asPow (c:= (m-P.d:ℤ)) hm
lemma recipro : (((k+1+m:ℕ):ℤ)-D)=(m-D:ℤ)+(k+1:ℕ):= by omega -- n retained? D P references ok
lemma deals (p:Rich G)(a:Axis)(i:ℕ) :
    (e i)^(((k+1+m:ℕ):ℤ)-P.d) • clockLeaf (d:=P.d) m (p i) (multi (flow G (side q i)) (load q P i) (beadR (changed (Θ i) a) (stepCloud (phase A) a)))= beadR (changed (Θ i) a) (fun z=> e i ^(m-P.d:ℤ) • wreath m P.d p (deliver q A a P) i z):= by
    let L:= (clockLeaf (d:=D) m (p i)).restrictScalars ℝ; let T:= (toned (flow G (side q i)) (load q P i)).restrictScalars ℝ; let u:=((e i)^(((k+1+m:ℕ):ℤ)-D)); let v:Cover→Curly G:= stepCloud (phase A) a; let w:= (e i)^(m-D:ℤ); change u • L (T _) =_
    change (u • (L ∘ₗ T)) (beadR (changed (Θ i) a) v) = _; rw [beadLm]; apply congr_arg; ext1 z; rw [clock_sample];
    change u • L (T (v z))=w • L (T ((e i)^(k+1) • v z)); rw [map_smul,map_smul,smul_smul]; unfold u w; rw [recipro P,zpow_add₀ (epsilon_pos q i).ne',zpow_natCast]
include hq
lemma situation (p:Rich G)(h:m≤P.d)(hp:Grasp p) : Released (fun i=> (e i)^(((k+1+m:ℕ):ℤ)-P.d) • clockLeaf (d:=P.d) m (p i) (multi (flow G (side q i)) (load q P i) (cutoffShell (Θ i) (phase A)))):= by
    simp_rw [cutoffShell,show ∀ (i:ℕ) g, multi (flow G (side q i)) (load q P i) g = toned (flow G (side q i)) (load q P i) g from fun _ _=> rfl,map_sum,Finset.smul_sum]
    -- convert toned terms
    change Released (fun i=> ∑ x:Axis,(e i)^(((k+1+m:ℕ):ℤ)-P.d) • clockLeaf (d:=P.d) m (p i) (multi (flow G (side q i)) (load q P i) _)); apply Released.sumR; intro a _; simp_rw [deals]; exact shell_release hq φ a (delivers hq A φ P h a p hp) (by omega)
lemma curved (h:m+(k+1)≤P.d): Released (fun i=> (e i)^(((k+1+m:ℕ):ℤ)-P.d) • clockLeaf (d:=P.d) m x (stroke (raised (Reed.phase A)) (Q i))):= by
    let v(i:ℕ):=((e i)^(((k+1+m:ℕ):ℤ)-D)); let L:= clockLeaf (d:=P.d) m x; let p:ℕ→ℂ:= fun i=> v i • L (multi (flow G (side q i)) (load q P i) (cutoffShell (Θ i) (Reed.phase A))); let r:ℕ→ℂ:= fun i=>v i • L (tilt (str (Reed.phase A)) (load q P i));
    have hr:= clock_released (d:=P.d) hq A x P h -- check order
    have hp: Released p:= situation (m:=m) hq A φ P (fun _=>x) (by omega) (fun i=> ⟨x i,tendsto_const_nhds⟩)
    obtain ⟨c,hc⟩:= hp.sub (show Released r from hr); refine ⟨c,hc.congr' ?_⟩; filter_upwards [φ.covers hq (bookMark P 0)] with i hi; unfold warp; rw [Ward_power P]; unfold p r load; simp only [Pi.sub_apply,map_add,map_neg,smul_add,smul_neg]; unfold v L; abel; exact hi
end YM.PositionX.Crystal
