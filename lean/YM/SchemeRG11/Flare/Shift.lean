import YM.SchemeRG11.Flare.Eddy
/-! Integrated total derivative term for 3 distinct apexes. -/
set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.SchemeRG11.Flare
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4

lemma house (p : Time) (hp : p∈tripod) (l:List Bit) (x:Tri) (t:E4) :
    series (trio p) (l.map atEye) (x +fun _=>t)=series (trio p) (l.map atEye) x := by
  rw [ruby _ hp,ruby _ hp,← integral_add_right_eq_self (f:=vault l p (x+fun _ => t)) t]
  apply integral_congr_ae; filter_upwards with w
  simp [vault,brick]

lemma shifts (p : Time) (hp:p∈tripod) (l : List Bit) (u : Axis) (x : Tri) :
    series (trio p) (((0,u)::l).map atEye) x+series (trio p) (((1,u)::l).map atEye) x+series (trio p) (((2,u)::l).map atEye) x=0 := by
  let K:= atEye (0,u)+atEye (1,u)+atEye (2,u)
  have hx : K=fun _=>basis u:=by ext1 i; fin_cases i <;> first | rfl | norm_num [K,atEye,Pi.single_apply,Fin.ext_iff,Eye]
  let g := series (trio p) (l.map atEye)
  have he := drift_step x K ((series_calm (trio_diff p) (l.map atEye)).differentiable (by simp) x)
  have hh t : (t:ℝ) • K=fun _=> t • basis u:=by rw [hx]; rfl
  simp_rw [hh,house _ hp] at he
  have ht:= he.unique (hasDerivAt_const 0 (g x)); simp only [K,map_add] at ht; exact ht

lemma packed (d : Bit) (p : Time) (hp : p∈tripod) (l m n:Sl) (x:Tri) :
    series (trio p) ((d::sumBits l m n).map atEye) x=
       orb (if d.1=0 then d.2::l else l) (if d.1=1 then d.2::m else m) (if d.1=2 then d.2::n else n) p x := by
  rw [ruby _ hp,grape _ _ _ p hp]
  refine integral_congr_ae (Eventually.of_forall (fun w=>?_)); simp only [juice,vault,brick,Steam.own,sumBits,own_add,own_mk,show ∀ i, d.1=i ↔ i=d.1 from fun _=>eq_comm]; norm_num [Eye,Fin.ext_iff]; rfl

lemma stations (u : Axis) (l m n:Sl) {x:Tri} (hx:x∈clearance 4) : yolk (u::l) m n x +yolk l (u::m) n x+yolk l m (u::n) x=0 := by
  unfold yolk; rw [← integral_add (oak _ _ _ hx) (oak _ _ _ hx),← integral_add (show IntegrableOn (fun p=>orb (u::l) m n p x +orb l (u::m) n p x) tripod volume from (oak (u::l) m n hx).add (oak l (u::m) n hx)) (oak l m (u::n) hx)]
  suffices hh:∀ p∈tripod, orb (u::l) m n p x+orb l (u::m) n p x+orb l m (u::n) p x=0 by rw [integral_congr_ae (f:=fun p=> orb (u::l) m n p x+orb l (u::m) n p x+orb l m (u::n) p x) (g:=fun _=>0) (ae_restrict_of_forall_mem tripod_meas hh),integral_zero]
  intro p hp
  have he:=shifts p hp (sumBits l m n) u x
  rw [packed _ _ hp,packed _ _ hp,packed _ _ hp] at he; exact he
end YM.SchemeRG11.Flare
