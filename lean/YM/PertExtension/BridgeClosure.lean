import YM.PertExtension.AirLimits

/-! Exact endpoint Wilson-Laplacian pair responses as curvature cochains. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Next.Rank.Beamer Air Orb Orbit GaussianScore Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
open Projection
variable {G : Gauge} {n : Side} {d : ℕ}

def echo (n : Side)(u v: Cover): Bridge G:= direct G n u v + reflected G n u v
protected def colorBasis (k:G.ColorIndex) : G.Color:= EuclideanSpace.basisFun G.ColorIndex ℝ k
variable {e : Even n.val} {u v:Cover} (x y:Address G)

lemma signals (e:Even n.val):
 (saddle (G:=G) e).wick (signal (stem _ n v y) (LatticePT.colorBasis y.2.2)) (signal (stem _ n u x) (LatticePT.colorBasis x.2.2))=echo n u v x y:= by
   rw [curl_covariance]
   change _ * inner ℝ _ _= _ + _
   rw [show Inner.inner ℝ (LatticePT.colorBasis x.2.2) (LatticePT.colorBasis y.2.2)=(if x.2.2=y.2.2 then 1 else 0) from ?_]
   · unfold direct reflected; split_ifs <;> simp only [mul_one,mul_zero,Complex.zero_re,zero_add]
   rw [LatticePT.colorBasis, EuclideanSpace.basisFun_inner, LatticePT.colorBasis,EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]

variable (e)
include e
lemma echo_comm : echo n u v x y= echo n v u y x := by
   rw [← signals x y e, ← signals y x e]
   unfold Law.wick
   let Γ:=saddle (G:=G) e
   let X:= Γ.inverse (signal (stem _ n u x) (LatticePT.colorBasis x.2.2))
   let Y:= Γ.inverse (signal (stem _ n v y) (LatticePT.colorBasis y.2.2))
   calc
    _ = Γ.P X Y:= by rw [show X= Γ.inverse _ from rfl,Γ.applies]
    _ = Γ.P Y X:=Γ.turns ..
    _ = _:= by rw [show Y= Γ.inverse _ from rfl,Γ.applies]

omit e
lemma brightness_swap (B:SheetLink G n) z i j : Orb.Curl B z i j = -Orb.Curl B z j i := by unfold Orb.Curl;abel
lemma brightness_shut (B:SheetLink G n) (u : Cover) : shutter fun x : Address G=> crease G B (stem G n u x) x.2.2:=by
   let F: Horizon G:= fun x=> crease G B (stem G n u x) x.2.2
   intro a b c; ext1 z
   change stepValue (Beamer.polar F b c) a z + stepValue (Beamer.polar F c a) b z + stepValue (Beamer.polar F a b) c z= _
   have h (i j:Axis)(z:Cover): Beamer.polar F i j z=Orb.Curl B (wrap n (u+z)) i j:=by
       unfold Beamer.polar Beamer.light;split_ifs with H L L
       · ext1 k; rfl
       · change -_ = _; rw [brightness_swap B _ i j]; congr 1
       replace H:i=j:= le_antisymm (le_of_not_gt L) (le_of_not_gt H)
       rw [H,Orb.Curl]; abel
   unfold stepValue; simp_rw [h, ← add_assoc u, map_add (wrap n), wrap_step]
   change _+_+_=(0:G.Color); unfold Orb.Curl; -- commute displacements
   abel

lemma closure_link {T : Horizon G}(u:Cover)(X:Dir G n)(hT:∀ x :Address G,T x=signal (stem G n u x) (LatticePT.colorBasis x.2.2) X): shutter T:=by
   have h: T=(fun x=> crease G (variation X) (stem G n u x) x.2.2):=by
      ext x;rw [hT,signal_eq,LatticePT.colorBasis,EuclideanSpace.basisFun_inner];rfl
   rw [h]; exact brightness_shut (variation X) u
include e
lemma echo_shut : (∀ x,shutter (G:=G) (echo n u v x)) ∧ ∀ y, shutter (G:=G) (fun x=>echo n u v x y) := by
   have H (u v)(y:Address G):shutter (G:=G) (fun x=>echo n u v x y) := by
      let X:= (saddle e).inverse (signal (stem _ n v y) (LatticePT.colorBasis y.2.2))
      apply closure_link u X
      intro x;exact Eq.symm (signals x y e)
   exact ⟨fun x=>by rw [show echo n u v x=(fun y=>echo n v u y x) from funext fun y=>echo_comm e x y];exact H v u x,H u v⟩
end YM.PertExtension.LatticePT
