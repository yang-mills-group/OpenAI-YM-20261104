import YM.AveragedStep.Stokes.Loops
import YM.Lattice.Support
/-! Paths based at a reporting root on either torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.Loops
open Lattice Wilson
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {n:Side}
-- from root x to y
def ray (x y:Site n): Walk := route 0 (lift (y-x)) 1
lemma stop_add {R:Type*}[AddCommGroup R][One R](x y:Four R)(w:Walk):
    stop (x+y) w =x+stop y w:=by
  induction w generalizing y with
  | nil=>rfl
  | cons i w ih=> rw [stop,add_assoc,ih,stop]
lemma ray_end (x y:Site n) : stop x (ray x y)=y := by
  nth_rw 1 [← add_zero x]
  rw [stop_add,← map_zero (wrap n),← wrap_stop_cover,ray,route_end,wrap_lift]
  abel
lemma ray_bound (x y:Site n) : List.length (ray x y) ≤ 4*separation x y := by
  have H (l : List Axis) : List.length (axisRoute 0 (lift (y-x)) l) ≤ l.length * pdist (y-x) := by
    induction l with
    | nil=> simp [axisRoute]
    | cons a l ih=>
      simp_rw [show axisRoute 0 (lift (y-x)) (a::l)=straight a (lift (y-x) a -0) ++ axisRoute 0 (lift (y-x)) l from rfl,List.length_append,straight,List.length_replicate,List.length_cons,add_mul,one_mul,sub_zero,Nat.add_comm _ (pdist ..)]
      exact Nat.add_le_add (component_le _ _) ih
  rw [separation_comm]; unfold ray route
  apply (H (allAxes 1)).trans_eq; simp [allAxes,separation]
lemma sep_next (x y:Site n)(i:Axis):separation x (y+step i) ≤ separation x y+1:=by
  apply (separation_triangle x y _).trans (Nat.add_le_add_left _ _)
  unfold separation; rw [show y-(y+step i)=-step i by abel,pdist_neg]; exact pdist_step i

def strung {G:Gauge}(x:Site n)(U:Config G n)(y:Site n):G.El:=travel U x (ray x y)
@[fun_prop] lemma strung_cont {G:Gauge}(x y:Site n):Continuous fun U:Config G n=>strung x U y:=continuous_travel ..
def setGauge {G:Gauge}(x:Site n)(U:Config G n):= Lattice.gauge (strung x U) U
@[fun_prop] lemma gauge_cont {G:Gauge}(x:Site n):Continuous fun U:Config G n=>setGauge x U:=by unfold setGauge Lattice.gauge; fun_prop

def Nearest (x y:Site n): Prop:= 4 * (separation x y+1)< n.val

lemma ray_append_near (x y:Site n)(h:Nearest x y)(a : Axis):
    lift (y-x)+step a=lift (y+step a-x):=by
  symm; apply lift_eq_iff.mpr
  rw [map_add, wrap_lift, wrap_step]; refine ⟨by abel,fun i=>?_⟩
  have he:=component_le (y-x) i; change _≤separation y x at he
  rw [separation_comm y x] at he
  unfold Nearest at h; simp_rw [Pi.add_apply,step_apply]; split <;> omega

/-- Chord of a nonwrapping gauge-fixed bond controlled by a list of full
plaquettes of polynomial cardinality, selected before the background.
Wrapping bonds in this global choice need different (distance-weighted) cost. -/
lemma gauge_list (x:Site n)(e:Edge (Site n))(h:Nearest x e.1):∃ L:List (Face (Per n)),
    L.length ≤ (8*separation x e.1+5)^2 ∧
    ∀ (G:Gauge)(U:Config G n),G.chord (setGauge x U e) ≤ bill U L:=by
  rcases e with ⟨y,i⟩
  let R:=ray (n:=n) x; let z:Site n:=y+step i
  let q:=R y ++ [posDir i] ++ Lattice.reverse (R z)
  have he : stop (0:Cover) q=0:=by
    unfold q
    simp_rw [stop_append]
    change stop (stop (stop (0:Cover) (route _ _ _)) _) _=0
    rw [route_end,stop,stop,Step.vec_pos,ray_append_near _ _ h]
    have ht:stop (0:Cover) (R z)=lift (z-x):=route_end ..
    exact ht ▸ reverse_stop (R z) (0:Cover)
  obtain ⟨L,hL,H⟩:=closed (R:=Per n) _ he x
  have ht : List.length q ≤ 8*separation x y+5:=by
    have hf:=ray_bound x y; have hg:List.length (R z) ≤ 4*(separation x y+1):=
      (ray_bound _ _).trans (Nat.mul_le_mul_left _ (sep_next x y i))
    simp only [q,List.length_append,Lattice.reverse,List.length_reverse,List.length_map,
      List.length_cons,List.length_nil]; change List.length (R y) ≤ _ at hf; omega
  refine ⟨L,hL.trans (by change _≤(8*separation x y+5)^2; gcongr),fun G U=>?_⟩
  apply le_trans (le_of_eq _) (H G U)
  congr 1; unfold q
  simp_rw [travel_append,R,stop_append,ray_end,travel,stop,Step.pos_read,Step.vec_pos]
  have hh:=travel_reverse (ray x z) U x; rw [ray_end] at hh
  rw [show y+step i=z from rfl,hh]
  simp only [setGauge,Lattice.gauge,strung,mul_one]; rfl
end YM.AveragedStep.Loops
