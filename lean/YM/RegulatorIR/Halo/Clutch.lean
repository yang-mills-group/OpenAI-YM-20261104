import YM.RegulatorIR.Halo.Elect
import YM.RegulatorIR.Halo.Trail

/-! Positive rank multiplicities on a repeated torus. Use absolute held
copies to avoid assuming symmetry of dents. Works for arbitrary leg pivot, no local
transporter truncations. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{I J X:Type}{f c n m:Side}{r i a:ℕ}
variable {l P:ℝ}
section Val
variable [Fintype J] (A:Deck P I J) (T:Packet I r)
-- read at one leg; hold present. no decay norm req in equality except actual budget, sufficient for multiplying arbitrary bounded orbit args.
def kissed (w:J→ℝ) (i: Fin r)(p:J):= ∑' z: Hold i p,A.deckSum T z.val *noodle w z.val
lemma parcel_v (c:I)(w:J→ℝ)(j:Fin r)(h: A.Ready T)(hh: Summable (fun x: Hold j c=>T x.val)):
 kissed A T w j (A.orbit c)=∑' v:Hold j c,T v.val*noodle (bridge A w) v.val:=by
 let U:= Hold j (A.orbit c);let F(v:Hold j c):=T v.val*noodle (bridge A w) v.val;let g (v:Hold j c):=A.dyed T v.val
 have he v : F v=g v*noodle w (A.project v.val):=by unfold F g noodle bridge dyed; rw [Finset.prod_mul_distrib]; unfold polish project; simp [mul_assoc]
 have hs: Summable F:=by
    apply quota_summable (w:=1) (fun _=>le_rfl); let M:= Finset.univ.sup (fun q:Tuple J r=> ‖noodle w q‖ₑ)
    have hp:M≠⊤:= ne_of_lt (Finset.sup_lt_iff (by simp)|>.mpr (fun i _=>enorm_lt_top)); rw [quota_base]
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (tsum_enorm_ne_top_iff_summable_norm.mpr hh.norm) hp)
    rw [← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum;intro i; rw [he,enorm_mul, show ‖g i‖ₑ= _ from A.dyed_cost ..]; exact mul_le_mul_right (Finset.le_sup (f:=fun q:Tuple J r=> ‖noodle w q‖ₑ) (Finset.mem_univ _)) _
 let p:= A.projectedHold j c
 change _=∑' v,F v; rw [← Stalk.collected_sum p hs]; apply tsum_congr;intro v
 rw [A.deck_pivot h v.val j c v.property.symm,A.parcel T j c v];unfold Stalk.collect; rw [← tsum_mul_right]; apply tsum_congr;intro b; rw [he]; exact congr_arg (fun x=>g b.val*noodle w x) (Subtype.ext_iff.mp b.property).symm
lemma evaluates (w:J→ℝ)(j:Fin r): MvPolynomial.eval w (render (A.deckSum T))=∑ i:J, kissed A T w j i := by
 rw [← pluck]; unfold strum kissed
 rw [← Stalk.collected_sum (fun p:Tuple J r=>p j) (hasSum_fintype ..).summable, tsum_fintype];rfl
end Val
section PlayQ
variable (H:Even f.val)(hp:l*f.val=P) (m:Side) {Q:Tariff (Foot G)} (T:Packet (Foot G) r)
local notation "S" => Carto G l P H hp
local notation "U" => playS m (G:=G) H hp

lemma replic (h:(S).Ready T) : (U).Ready T:= by
 apply (ready_iff ..).mpr; intro d x; rw [show (U).wind d=(S).wind (filling m d) from Equiv.ext fun i=>Halo.steering m H hp d i, (ready_iff ..).mp h,sign_fill]
lemma lowers (b:Book G (m*f)): (S).orbit ((U).place b)=(shadow f m b.1,b.2):=by
 change (index (around f (Geometry.position b.1)),b.2)= _
 rw [← fallen (m:=m) (n:=f) _,position_edge];rfl
lemma perched (x:Horizon G f)(j: Fin r)(h: (S).Ready T) (b:Book G (m*f))
 (hh:∀ c:Foot G,Summable (fun p:Hold j c=> T p.val)):kissed U T (paper G _ (stamped f m x)) j b= kissed S T (paper G f x) j (shadow f m b.1,b.2):=by
 let c: Foot G:= (U).place b
 rw (occs:=.pos [1])[← (U).placed b]
 rw [← lowers H hp m b, parcel_v _ T c _ j (replic H hp m T h) (hh c), parcel_v _ T c _ j h (hh c), time_v]
lemma projected (h:(S).Ready T) (j:Fin r) {b:ℝ≥0∞} (hc: b≠⊤)(hh: localQ Q T b)(x:Horizon G f):
 MvPolynomial.eval (paper G (m*f) (stamped f m x)) (render ((U).deckSum T))= counts m*MvPolynomial.eval (paper G f x) (render ((S).deckSum T)):= by
 have hp' (c:Foot G) : Summable (fun p:Hold j c=> T p.val):=quota_summable (fun p=> Q.diameter_unit p.val) (ne_top_of_le_ne_top hc (hh j c))
 rw [evaluates _ _ _ j,evaluates _ _ _ j];simp_rw [fun p=> perched H hp m T x j h p hp']; exact echoes f m H .. 

end PlayQ
end YM.RegulatorIR.Halo
