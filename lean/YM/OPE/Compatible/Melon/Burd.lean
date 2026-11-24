import YM.OPE.Compatible.Melon.Creme
/-!
# No contribution from orbit gauges through linear order. First benefit of color simplicity. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock
attribute [local instance] Gauge.frobInner
variable {H: Even n.val} (T: Plot H)
local notation "TK" => Keys G (Limb H)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
local notation "W" => Chart.tangent G T.Stable
local notation "Jq" => compass H T G
lemma three_name (x:TK): treeP (cubicP T) x=jet (tall T) 3 x:= by
      rw [jet,show (fun _ :Fin 3=>x)=![x,x,x] from funext fun i=>by fin_cases i<;>rfl]; rfl
lemma wingBond (x:FD): Bond fun y:DK=> jet (tall T) 3 (compass H T G (x,y)) := by
    let p(y:DK):= compass H T G (x,y); have ht: Bond (jet (tall T (G:=G)) 3) := Bond.scale _ (Bond.multiline _ (fun _ :Fin 3=> id) (fun _ c=>Bond.glyph c))
    refine ht.comp fun v=> ?_; let L:= v.comp (compass H T G).toLinearMap
    let c:= L.comp (LinearMap.inr ..); convert (Bond.keep (L (x,0))).add (Bond.glyph c) using 1; funext i; exact (congr_arg L (show (x,i)=(x,0)+(0,i) by simp)).trans (L.map_add ..)
private lemma negLaw {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X](μ:Measure X)[μ.IsAddHaarMeasure](L:Law X)(f:X→ℝ)(h:Bond f): L.average μ f=L.average μ (fun x=> f (-x)):=by
    let k:X ≃ₗ[ℝ] X:= LinearEquiv.neg ℝ -- name?
    refine meanFit μ μ L L k.toLinearMap (dual_wick k L L fun i=>?_) f h; change L.P i i=L.P (-i) (-i);simp
lemma woolI (p:FD): let F(y:DK):= jet (tall T) 3 (compass H T G (p,y)); let Q:=fond H T G
                     Q.average W (fun y=>F y+F (-y))=2*Q.average W F:=by
       intro F Q; have he : Bond F:= wingBond T p; have hh: Bond (fun y:DK=> F (-y)):= he.compLinear (- LinearMap.id)
       change Q.average W (F+(fun y=>F (-y)))=_; rw [sun W Q he hh, ← negLaw W Q F he];ring
abbrev brush (x:FD)(y:DK):= jet (tall T) 3 (compass H T G (x,y)) +jet (tall T) 3 (compass H T G (x,-y))
lemma brush_ray (x:FD)(y:DK):brush T x y=
      let p:= cubicP T (G:=G); let v:= compass H T G (x,0); let u:=compass H T G (0,y); 2*(p v u u + p u v u + p u u v):=by
       unfold brush; let w:= compass H T G; let p:=cubicP T (G:=G); simp only [← three_name]; change treeP p (w (x,y))+treeP p (w (x,-y))=_; rw [show (x,y)=(x,(0:DK))+(0,y) by simp,show (x,-y)=(x,(0:DK))-(0,y) by simp,w.map_add,map_sub,movement]; rw [show treeP p (w (x,0))=0 from (three_name T _).trans (h_touched T x),mul_zero,zero_add]
lemma shower (x: FD): Bond (brush T x):=by let f(y:DK):= jet (tall T) 3 (compass H T G (x,y)); have h:Bond f:= wingBond T x; exact h.add (h.compLinear (- LinearMap.id))
def super (G:Gauge) : Keys G T.Free→ₗ[ℝ] ℝ where
   toFun p:= (fond H T G).average (Chart.tangent G T.Stable) (brush T p)
   map_add' x y:=by rw [show brush T (x+y)= brush T x+brush T y from funext (fun i=>?_),sun _ _ (shower T x) (shower T y) ]; dsimp only [Pi.add_apply]; rw [brush_ray,brush_ray,brush_ray,show (x+y,0)=(x,0)+(y,(0:Keys G T.Stable)) by simp]; simp only [map_add,LinearMap.add_apply];ring
   map_smul' c x:= by rw [show brush T (c • x)= c • brush T x from funext (fun i=> ?_), scooted]; rfl; dsimp only [Pi.smul_apply]; rw [brush_ray,brush_ray,show (c • x,0)= c • (x,(0:Keys G T.Stable)) by simp]; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]; ring
lemma super_roll (g:G.El)(x:FD): super T G (glint _ g x)=super T G x:=by
      change (fond H T G).average _ _ = _; let L:=glint T.Stable g; rw [meanFit W W _ _ L.toLinearMap (dual_wick _ _ _ (fun i=>(carriage T g i i).symm)) _ (shower ..)]; change _=(fond H T G).average W (brush T x); congr 1; funext i; unfold brush; change jet (tall T) 3 (compass H T G ((glint _ g) x,(glint (Stand.Stable T) g) i))+jet (tall T) 3 (compass H T G ((glint _ g) x, -((glint (Stand.Stable T) g) i)))=_; rw [rises_dir,jet_R,← map_neg (glint _ g) i,rises_dir,jet_R]
lemma quenching (x:FD)(h:G.Simple): (fond H T G).average W (fun y:DK=> jet (tall T) 3 (compass H T G (x,y)))=0:=by
      let f:=super T G; let A:= f.toContinuousLinearMap; have ht:f x=0:= YM.Stationary.slot_fixed h A (super_roll T) x; have hu : (fond H T G).average W (brush T x)=0:= ht; have he:= woolI T x; rw [show f x= _ from woolI T x] at ht; linarith only [ht]
end YM.OPE.Cascade.Glass
