import YM.Integration.WilsonPhysicalAnchoredPaths
import YM.Next.FLUCTUATIONS.Charts

/-! The Wilson bond with its two specified paths to the same base point.
All read edges and the whole noncommutative loop stay explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalLocalPlaquetteLoop
open Lattice RG Wilson WilsonPhysicalAnchoredGauge
open scoped Classical
variable {n:Side} {G:Gauge}

def word (A:Roads n) (e:Edge (Site n)):Walk:=
  (Lattice.reverse (A.arm e.1)++[posDir e.2])++A.arm (e.1+step e.2)

theorem closed (A:Roads n) (e:Edge (Site n)):stop A.root (word A e)=A.root:=by
  have back:=reverse_stop (A.arm e.1) e.1
  rw [A.closed] at back
  rw [word,stop_append,stop_append,back]
  simpa only [stop,Step.vec_pos] using A.closed (e.1+step e.2)

theorem read (A:Roads n) (e:Edge (Site n)) (U:Config G n):
    based A U e=travel U A.root (word A e):=by
  have back:=reverse_stop (A.arm e.1) e.1
  have arm:=travel_reverse (A.arm e.1) U e.1
  rw [A.closed] at back arm
  rw [word,travel_append,travel_append,stop_append,back,arm]
  simp only [based,Lattice.gauge,transport,inv_inv,travel,stop,Step.vec_pos,Step.pos_read,mul_one]

theorem lengths (A:Roads n) (e:Edge (Site n)):(word A e).length=
    (A.arm e.1).length+1+(A.arm (e.1+step e.2)).length:=by simp [word,Lattice.reverse,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem chord (A:Roads n) (e:Edge (Site n)) (U:Config G n) (φ:Site n→G.El)
    (r:ℕ) {b:ℝ} (hb:0≤b) (fund:∀i:Edge (Site n),separation A.root i.1<r→G.chord (gauge φ U i)≤b)
    (inside:∀y∈visits A.root (word A e),separation A.root y<r):
    G.chord (based A U e)≤((word A e).length:ℝ)*b:=by
  let V:=gauge φ U
  let V':Config G n:=fun i=>if separation A.root i.1<r then V i else 1
  have cap (i:Edge (Site n)):G.chord (V' i)≤b:=by
    by_cases hi:separation A.root i.1<r
    · simpa only [V',if_pos hi] using fund i hi
    · simpa only [V',if_neg hi,G.chord_one] using hb
  have change:travel V A.root (word A e)=travel V' A.root (word A e):=by
    apply travel_local
    intro i hi _
    simp only [V',if_pos (inside _ hi)]
  have physical:=travel_gauge φ U A.root (word A e)
  rw [closed] at physical
  rw [read]
  calc
    G.chord (travel U A.root (word A e))=G.chord (travel V A.root (word A e)):=by
      unfold V;rw [physical,G.chord_conj]
    _=G.chord (travel V' A.root (word A e)):=congrArg G.chord change
    _≤_:=Next.Fluctuations.travel_chord V' _ _ b cap

end YM.Integration.WilsonPhysicalLocalPlaquetteLoop
