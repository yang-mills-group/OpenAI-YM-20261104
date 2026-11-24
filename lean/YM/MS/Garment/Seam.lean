import YM.MS.Alps.Recoil
/-!
# Symmetries, project at stable dimensions not on 4-space marks

At nuisance regulators and Cut implementations. Direct linear tests of singular properties via Tally. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{b:Bool}{m n:ℕ}{i:ℂ}{U:Rip G}{F:Mob G}
lemma plain_small (E F:Type)[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]: Ultra (0:E×F→ℂ):= fun k=> Costs.zero (fun i p _=> by change 0≤1/_; exact div_nonneg zero_le_one (pow_nonneg (Scale.weight_pos ..).le _))
lemma plain_scale {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{f:E×F→ℂ}(c:ℂ)(h: Ultra f): Ultra (c • f):= h.L (ContinuousLinearMap.mul ℝ ℂ c)
def strand (L: Rack G m→ℂ)(U: Rip G)(F: Mob G)(z:ℂ): Arc.Tree ℝ ℂ:= fun p=> L (fun l=> carpet (Px m) (wing z U F (ray l)) p)
abbrev pulls (h:m≤n)(R:Rack G n): Rack G m:= fun w=> R (Arts.lift h w)
variable (hU:Knot b U)(hF:Form0 b F)(hi:i∈Town)
include hU hF hi
lemma catalog {L:Rack G m→ℂ}(H:L∈ Heat.Centre _): Ultra (strand L U F i)∧Reflect (strand L U F i) ∧ coreC (cloud i) m (strand L U F i) 1=L (ocean i U F m):= by
   refine Submodule.span_induction (p:=fun L _=> Ultra (strand L U F i)∧Reflect (strand L U F i)∧ coreC (cloud i) m (strand L U F i) 1=L (ocean i U F m)) ?_ ?_ ?_ ?_ H
   · rintro p ⟨l,rfl⟩; exact ⟨carpet_test hF.price hU.price (ray l) i, mirror_r (Px _) (wing_mirror hF.token hU.token i (ray l)), rfl⟩
   · have h0 : ∀ n,pruning n (0: Arc.Tree ℝ ℂ)=0:= by intro n; induction n with|zero=>rfl|succ n ih=> rw [spent, ih]; unfold chop Arc.d; simp; rfl
     refine ⟨plain_small ℝ ℝ,fun _ _=>rfl,?_⟩; rw [show strand (0:Rack G m→ℂ) U F i=0 from rfl]; simp_rw [coreC,h0]; simp [fetching, fetchP]
   · intro L K Hv Hk ha hb; rw [show strand (L+K) U F i=strand L U F i+ strand K U F i from rfl]; refine ⟨ha.1.add hb.1, fun x y=>by simp only [Pi.add_apply, ha.2.1 x y,hb.2.1 x y],?_ ⟩; simp_rw [core_pl ha.1 ha.2.1 hb.1 hb.2.1 hi, Pi.add_apply,ha.2.2,hb.2.2]
   intro c L H ht; rw [show strand (c • L) U F i=c • strand L U F i from rfl]; exact ⟨plain_scale c ht.1,fun x y=> by simp only [Pi.smul_apply,ht.2.1 x y],by rw [core_m ht.1]; simp [ht.2.2]⟩
lemma erase {L:Rack G m→ℂ}(hL:L∈ Centre _) (H:∀ x,L (pulls (Nat.le_succ m) (Wtr i U F x))=0) : L (ocean i U F m)=0:= by
   let S:Arc.Tree ℝ ℂ:= strand L U F i; obtain ⟨he,hm,Hw⟩:= catalog hU hF hi hL; rw [← Hw];
   have hp x : S (x,(1:ℝ))=0:= by
       unfold S strand; have hu:= fun k:Legs (Shore G m)=> (Arc.Q.Gmajor (Px m) ( Path.exact_test hF.price hU.price (ray k) i ) ()).values (x,1); -- integrable q but variable name i shadows
       unfold carpet; rw [← (cent_arguments (Px m) hL (f:=fun p l=> wing i U F (ray l) ((p,x),1)) ?_).2]; swap; · exact hu
       simp_rw [wing,ray_sail,show ∀ p, L (fun l=> (Wtr i U F p) (Arts.lift (Nat.le_succ m) l))=0 from H]; exact integral_zero ..
   have hx : ∀ x:ℝ, pruning (m+1) (strand L U F i) (x,1)=0:= by
       intro x; refine Eq.trans (Path.Fiber.pruneC 1 (0:ℝ) (f:=strand L U F i) (g:=0) (he.smooth ()) contDiff_const hp _ x) ?_; rw [show pruning (m+1) (0:Arc.Tree ℝ ℂ)=0 from ?_]; rfl;
       have h0 : ∀ n,pruning n (0: Arc.Tree ℝ ℂ)=0:= by intro n; induction n with|zero=>rfl|succ n ih=> rw [spent, ih]; unfold chop Arc.d; simp; rfl
       exact h0 (m+1)
   unfold coreC; rw [Pi.smul_apply]; unfold fetching fetchP; simp_rw [hx]; simp
end YM.MS.Garment
