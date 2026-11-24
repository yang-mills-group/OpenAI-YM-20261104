import YM.X.Clear.Null
import YM.Work.E01
/-!
# Discrete near-eye/away-eye coordinate for center-comparison of periodic and orbital first jets.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Interval.Size
open Function Filter Set Metric MeasureTheory Lattice PertExtension LatticePT
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {q:ℕ+} {G:Gauge} {R: Side} {j:ℕ} {n:ℕ}
open Pert.Align Asymptotics Real
local notation "r"=> (atTop:Filter ℕ)
local notation "ε"=> epsilon q
local notation "s"=> side q
variable (hq:1<q.val)

abbrev Beam (q:ℕ+):= (k:ℕ)→Site (side q k)
def raysD (x y:Beam q)(i:ℕ):ℝ:= separation (x i) (y i)
lemma rays_cycle (x y:Beam q): raysD x y=raysD y x:= by funext i; unfold raysD; rw [separation_comm];
def rounds (v:Cover) : ℕ:= Finset.univ.sup fun i:Axis => (v i).natAbs
lemma round_fee (v:Cover): pdist (wrap R v) ≤ rounds v:= by
   apply Work.E01.pdist_wrap_le; rw [box_iff_layers]; intro i; apply Finset.mem_Icc.mpr; have h : (v i).natAbs≤rounds v:= by unfold rounds; exact Finset.le_sup («s»:=Finset.univ) (f:=fun i:Axis=> (v i).natAbs) (Finset.mem_univ _)
   omega -- scope rounds private? others need fixed. turn public

def Near (x y:Beam q):= Charged q (raysD x y)
namespace Near
variable {x y z:Beam q}
lemma circ (h:Near x y):Near y x:= by rwa [Near, rays_cycle]
lemma around (x:Beam q):Near x x:= by rw [Near,show raysD x x=0 from funext fun i=> by simp [raysD]]; exact Charged.zero
lemma onward (h:Near x y)(g:Near y z): Near x z:= by
   obtain ⟨d,L⟩:= Charged.add h g; refine ⟨d, IsBigO.trans (IsBigO.of_norm_eventuallyLE (g:=raysD x y+raysD y z) ?_) L⟩
   apply Eventually.of_forall; intro k; change ‖(separation (x k) (z k):ℝ)‖ ≤ raysD x y k+raysD y z k; rw [Real.norm_of_nonneg (by positivity)]; unfold raysD; exact_mod_cast separation_triangle (x k) (y k) (z k)
lemma bound {C:ℝ}(h:∀ᶠ i:ℕ in atTop,raysD x y i ≤ C): Near x y:= by apply Charged.of_pay (Ripe.costed (a:=C) _); simpa [raysD,Real.norm_of_nonneg (Nat.cast_nonneg _)] using h
lemma tours (v:Cover) : Near x (fun k=>wrap (side q k) v + x k):= by
   apply Near.circ (bound (C:=(rounds v:ℝ)) _); apply Eventually.of_forall; intro k; unfold raysD separation; rw [add_sub_cancel_right]; exact_mod_cast (round_fee (R:=side q k) v)
lemma negative (h:Near x y): Near (-x) (-y) := by rw [Near, show raysD (-x) (-y) = raysD y x from funext fun i=> by simp [raysD,separation,sub_neg_eq_add,sub_eq_add_neg,add_comm]]; exact h.circ
end Near

def Away (x y:Beam q): Prop:= ∃ c:ℝ,c>0∧ ∀ᶠ i in r, c*((side q i).val:ℝ) ≤ raysD x y i
lemma notAway (hq:1<q.val){x y:Beam q}(h:Near x y)(hw: Away x y): False:= by
   obtain ⟨c,hc,H⟩:=hw; obtain ⟨d,h⟩:=h
   have he : Vanished q (fun k => raysD x y k/((side q k).val:ℝ)) := Vanished.right (f:=raysD x y) ⟨d,h⟩ (Vanished.side_small hq)
   obtain ⟨k,Hk,Hc⟩:= (H.and ((he.goes hq).eventually (gt_mem_nhds hc))).exists; exact not_lt_of_ge ((le_div_iff₀ (by positivity)).mpr Hk) Hc
namespace Away
variable {x y z:Beam q}
lemma circ (h: Away x y):Away y x:= by unfold Away; rw [rays_cycle y];exact h
lemma smaller (hq:1<q.val)(h: Away x y)(g: Near x z):Away z y:= by
   obtain ⟨c,hc,H⟩:= h; have he : Vanished q (fun k=> raysD x z k/((side q k).val:ℝ)):= Vanished.right (f:=raysD x z) g (Vanished.side_small hq); refine ⟨c/2, by positivity,?_⟩; filter_upwards [H, (he.goes hq).eventually (ge_mem_nhds (half_pos hc))] with k hk h'
   have ht : raysD x y k ≤ raysD x z k+ raysD z y k:= by unfold raysD; exact_mod_cast separation_triangle (x k) (z k) (y k)
   change raysD x z k /((side q k).val:ℝ)≤c/2 at h'; rw [div_le_iff₀ (by positivity)] at h'; linarith [ht]
lemma negative (g: Away x y): Away (-x) (-y):= by
   unfold Away;rw [show raysD (-x) (-y)=raysD y x from funext fun i=>by simp [raysD,separation,sub_neg_eq_add,sub_eq_add_neg,add_comm]]; exact g.circ
end Away

variable (O:ℕ→Cover)(hO:Screens.Placement q O)
-- `lift` on 2*o; no upper issue at tie since O positive
include hO
lemma buffered (k:ℕ) : lift (wrap (side q k) (O k+O k))= O k+O k:= by
   refine lift_eq_iff.mpr ⟨rfl,fun i=> ?_⟩; obtain ⟨ht,hb⟩:=hO k i
   simp_rw [Pi.add_apply]; have hk:= Nat.cast_pos (α:=ℝ).mpr (side q k).pos; constructor
   · exact_mod_cast (show -((side q k).val:ℝ)<2*((O k i:ℝ)+O k i) from by linarith)
   exact_mod_cast (show 2*((O k i:ℝ)+O k i)≤((side q k).val:ℝ) from by linarith)

def stared : Beam q:= fun k=> wrap (side q k) (O k)
lemma stares : Away (stared (q:=q) O) (-stared (q:=q) O):= by
   refine ⟨1/4,by norm_num,Eventually.of_forall fun k=> ?_⟩; let i:Axis:=0; unfold raysD separation stared; rw [Pi.neg_apply,sub_neg_eq_add,← map_add]; apply le_trans ?_ (Nat.cast_le.mpr (component_le (wrap (side q k) (O k+O k)) i)); rw [buffered O hO,Pi.add_apply]; have h:= (hO k i).1; set v:= O k i + O k i; have he : 1/4*((side q k).val:ℝ)≤(v:ℝ):= by unfold v; push_cast; linarith only [h]
   exact he.trans (by rw [←Int.cast_natCast (R:=ℝ) v.natAbs]; exact Int.cast_le.mpr (by omega))
end YM.PositionX.Interval.Size
