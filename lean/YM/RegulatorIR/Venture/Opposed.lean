import YM.RegulatorIR.Venture.Linear

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Epoch
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
namespace VacDay
variable {X V : Type}{W:X→Type}{A:(x:X)→Tariff (W x)}{L:Meter X}{F:X→ℝ≥0∞}{r s:ℕ}
variable {T U : (x:X)→Packet (W x) r} {P R:(x:X)→Layer (W x) (W x)}
lemma bills_b (h: Beam L A P)(x:X): Billed (P x):=by obtain ⟨c,H,h⟩:=h; exact billed_supp (h x).1 (H.cost _)
lemma knows_l (H:Workday L A T) (w:X) : Knows (A w) (T w) :=by obtain ⟨a,h,H⟩:=H;exact ⟨_,h.cost _,H _⟩
lemma ray_v (i:Fin r)(h:Workday L A T)(hp:Workday L A U)(ht:VacDay F L A (fun x=>T x-U x))(H:Beam L A P)(Hz: Beam L A R)(H':RailDay F L A (fun x=>P x-R x)): VacDay F L A (fun x=> Packet.ray i (T x) (P x)-Packet.ray i (U x) (R x)):=by
 simp_rw [fun x:X=> ray_minus (K:=T x) (K':=U x) i (bills_b H x) (bills_b Hz x) (limits_r (plain h) _ ENNReal.one_ne_top) (limits_r (plain hp) _ ENNReal.one_ne_top)]; exact (rays_t h H' i).add (ht.rays Hz i)
lemma draft_v (h:Workday L A T)(hp:Workday L A U)(H:Beam L A P)(Hz:Beam L A R)(H':RailDay F L A (fun x=>P x-R x))(ht:VacDay F L A (fun x=>T x-U x)): VacDay F L A (fun i=> Packet.draft (P i) (T i)-Packet.draft (R i) (U i)):= by
 have hv {P T}(hp: Workday L A (r:=r) T)(h:Beam L A P) :∀ p:List (Fin r),Workday L A (fun i=>Packet.drawing (T i) (P i) p):=by
    intro p; induction p with
    | nil=>exact hp
    | cons j p ih=> exact plain_r (rays (plain ih) h j)
 have hX(p: List (Fin r)) : VacDay F L A (fun i=> Packet.drawing (T i) (P i) p- Packet.drawing (U i) (R i) p):=by
    induction p with
    | nil=> exact ht
    | cons i p ih=> exact ray_v i (hv h H p) (hv hp Hz p) ih H Hz H'
 unfold Packet.draft; simp_rw [← Diagram.symmetry_sub]; exact (hX (List.finRange r)).sym
lemma loop_v {T U: (x:X)→Packet (W x) (r+2)}(h:Workday L A T)(hp:Workday L A U)(H:Beam L A P)(Hz: Beam L A R)(H':RailDay F L A (fun x=>P x-R x))(ht:VacDay F L A (fun i=> T i-U i)):VacDay F L A (fun x=>Packet.loop (T x) (P x)-Packet.loop (U x) (R x)):=by
 by_cases hx:0 < r; swap
 · have hr:r=0:=by omega
   subst r; exact void_r
 simp_rw [fun i:X=>loop_re hx (knows_l h i) (knows_l hp i) (bills_b H i) (bills_b Hz i)]; exact (loop_t h H').add (ht.loop_p Hz)
lemma splice_v {T U:(x:X)→Packet (W x) (r+1)}{N M:(x:X)→Packet (W x) (s+1)} (h:Workday L A T)(hp:Workday L A U)(H:Workday L A N)(Hz:Workday L A M)(ht:VacDay F L A (fun x=>T x-U x))(hv:VacDay F L A (fun i=> N i-M i)) : VacDay F L A (fun x=> Packet.splice (T x) (N x)- Packet.splice (U x) (M x)):=by
 by_cases hx:0 < r+s; swap
 · have hr:r=0:=by omega
   have hs:s=0:=by omega
   subst r s; exact void_r
 simp_rw [fun i:X=> splice_re hx (knows_l h i) (knows_l hp i) (knows_l H i) (knows_l Hz i)]; exact (ht.splice_m H).add (splice_p hp hv)
lemma knot_v {T U:(x:X)→Packet (W x) (r+1)}{N M:(x:X)→Packet (W x) (s+1)} (h:Workday L A T)(hp:Workday L A U)(H:Workday L A N)(Hz:Workday L A M)(ht:VacDay F L A (fun x=>T x-U x))(hv:VacDay F L A (fun i=> N i-M i))(hc:Beam L A P)(hR:Beam L A R)(H':RailDay F L A (fun x=>P x-R x)): VacDay F L A (fun x=>Packet.knot (P x) (T x) (N x)-Packet.knot (R x) (U x) (M x)):=splice_v h hp (plain_r (rays (plain H) hc 0)) (plain_r (rays (plain Hz) hR 0)) ht (ray_v 0 H Hz hv hc hR H')
end VacDay
end YM.RegulatorIR.Epoch
