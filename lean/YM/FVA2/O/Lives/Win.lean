import YM.FVA2.O.Lives.Slide
/-!
# Lifts to the space of all external parameters and n-rows
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Lives
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire
open scoped Topology ContDiff
variable {G:Gauge}{I:Type}{i:I}{F F' H H' : Glade G I}{U V:Planet G I}{y:I→ℝ}{s:ℝ}{q n:ℤ}{r:ℕ}
def both (G:Gauge)(I:Type) : GridR (Glade G I):={
    J:= Puff.varied I (fun _=> Puff.varied ℝ (fun s=> (Φ G s).J)), P:= Puff.varied I (fun _=> Puff.varied ℝ (fun s=> (Φ G s).P)), L:= Puff.varied I (fun _=> Puff.varied ℝ (fun s=> (Φ G s).L)), X:= Puff.points I (fun _=> Puff.points ℝ (fun s=> (Φ G s).X)), C:= Puff.points I (fun _=> Puff.points ℝ (fun s=> (Φ G s).C)), D:= Puff.points I (fun _=> Puff.points ℝ (fun s=> (Φ G s).D)) }
def Z (G:Gauge)(I:Type): Signal.MH (Glade G I):= Puff.varied I fun _=> Puff.varied ℝ (fun _=> (Q G 0).raise)
def Rcy (U:Planet G I) : Signal.MH (Glade G I):= Puff.varied I fun i=> Puff.varied ℝ fun s=> Heat.orbit (U i s) planeF
lemma front (G:Gauge)(I:Type): (both G I).J= Z G I + Rcy (fun _=> lineB G):= LinearMap.ext fun _=> rfl
lemma spine (hF:Warm F false)(hU:BackF U): Rcy U F=sailP (fun _=>planeF) U F:= funext (fun _=> funext fun _=> finite_cc planeF ( passes hU hF ))
-- Unevaluated boosts. Lens cap identity.
lemma cfire (h:Warm F false): Warm (Z G I F) false:= by
    constructor
    · intro i T hT E _ _ w hw hp; let S:= single ( camp T ); unfold Cape Chart; simp only [tap]; simp_rw [show ∀ v,Z G I F i v= _ from fun v=> (show Z G I F i v= (Q G 0).raise (F i v) from rfl),visit_Z, visit_sail]; simp only [ Pi.one_apply,cw,one_zpow,one_mul ]; refine visit_bound (fun _=>zero_le_one) (fun l k ℓ hk=>?_); refine Costs.sum _ (fun c hc=>?_) (fun i p _=> zero_le_one); obtain hv:= h.cost i T hT E (l++(c,k.2)::ℓ) (fun x=>Bool.noConfusion x) (fun x=>Bool.noConfusion x);
      obtain he:= send_cost (A:=Axis) (S:=S) (a:=phaseDiff _) (fun _=>le_rfl) (fun _=>le_rfl) k.1 c; let q:=net w; obtain hL:= he.std; unfold Cape at hv; unfold S at hL; simp only [cw,one_zpow,Pi.one_apply,mul_one] at hv hL; convert! (Bound.linear k.2 hL).mul hv using 1; · funext i t; simp only [tap,Chart,sail_join,sail_cons]; rfl -- unfold tap order
      ext; simp
    intro i l _; have hx : ∀ k:Law G→ℂ,k∈Centre _→Continuous fun t=>k (F i t):= by
       intro v hv; refine Submodule.span_induction (p:=fun v _=>Continuous fun t=> v (F i t)) ?_ continuous_const (fun _ _ _ _ a b=> a.add b) (fun c v _ hv=> continuous_const.mul hv) hv; rintro l ⟨j,rfl⟩; exact h.walk _ _ (fun i=> Bool.noConfusion i)
    exact hx _ ((sense_Q (Q G 0)).reaches l)
lemma cdrop (h:Warm F false)(he:Diversity F n)(hm:BackF U): Diversity (Rcy U F) (n-2) := by
    intro i t l hx; rw [spine h hm]; unfold sailP cycle; simp_rw [at_trc, show ∀ i' j':Lane4 G,F i t (i'::j'::l)=0 from fun _ _=> he i t ( _ :: _ :: _) (by simp; omega),mul_zero, Finset.sum_const_zero]; rw [integral_zero]
lemma moreHeat (h:Warm F false): Warm F true:= ⟨ fun i s hs=> (h.cost i s hs).snow, fun i s _=> h.walk i s (fun x=>Bool.noConfusion x)⟩
lemma cF (hF:Warm F false)(hU:BackF U): Warm ( Rcy U F ) false:= by rw [ spine hF hU ]; exact warmCycle (fun _=> Geo.Coherent) hU hF
lemma WH (hF: Warm F false) : Warm ((both G I).P F) false:= cF hF realityA
lemma WJ (hF: Warm F false) : Warm ((both G I).J F) false:= by rw [front G I, LinearMap.add_apply]; exact CabinF.warm_zip (cfire hF) (cF hF realityB)
lemma WX (hF:Warm F false)(h:Warm H false): Warm ((both G I).X F H) false:= walk_tree (sugar _ _ realityA) (moreHeat hF) h
lemma WB (hF:Warm F false)(h:Warm H false): Warm ((both G I).C F H) false:= walk_tree (sugar _ _ realityB) (moreHeat hF) h
-- recall mk_add/map lemma via defeq.P. rank uniform in all
lemma collectQ (h:collect F): collect (Z G I F):= by obtain ⟨k,h⟩:=h; exact ⟨k,fun i t=> Wind.Modeled.Qmax _ (h i t)⟩
lemma gasF (h:collect F)(hF:Warm F false)(hU:BackF U): collect ( Rcy U F ) := by obtain ⟨k,h⟩:= h; exact ⟨k, behind (cdrop hF h hU) (by omega)⟩
lemma gasP (h:collect F)(hF:Warm F false): collect ((both G I).P F):= gasF h hF realityA
lemma gasJ (h:collect F)(hF:Warm F false): collect ((both G I).J F):= by rw [ front G I, LinearMap.add_apply ]; exact collect_p (collectQ h) (gasF h hF realityB)
end YM.FVA2.O.Lives
