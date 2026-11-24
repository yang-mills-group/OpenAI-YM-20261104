import YM.RegulatorIR.Profiles.Trek
import YM.RegulatorIR.Halo.Trail

/-! Absolute opening costs for actual translated finite stencils. The
common origin can range over the whole safe part of the inversion board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentRawWordGeometry
open Lattice RegulatorIR RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.Prim
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Budget.Tuple
open RegulatorIR.Gain RegulatorIR.Cluster RegulatorIR.Cluster.Collapsed
open RegulatorIR.Motion
open scoped Classical ENNReal BigOperators
variable {G:Gauge}{r:ℕ}

def root (x:Room)(u:ℕ) :=
  ((Premium.rooted (Tariff.native 1 zero_lt_one u) x).uses (localL (G:=G) 1))

def district (x:Room)(u:ℕ) :=
  ((realm (l:=1) zero_lt_one u {x}).uses (localL (G:=G) 1))

def displacement (x:Room)(p:Cover)(u:ℕ) := Tariff.amount 1 u (dist x (slide 1 p))

theorem recenter (x:Room)(u:ℕ)(T:Packet (Foot G) r)(p:Cover) :
    markQ (district x u) (echo (carryX p) T) ≤
      markQ (root 0 u) T * displacement x p u := by
  unfold markQ
  rw [←quota_raised,←quota_perm (Tuple.winding (carryX p) r)]
  have same: (echo (carryX p) T) ∘ Tuple.winding (carryX p) r = T :=
    funext (fun v=>echos (carryX p) T v)
  rw [same]
  apply quota_mono
  intro v
  apply highest zero_lt_one u {x} _
  · exact one_le_mul (Premium.width_unit ..) (Tariff.amount_unit zero_lt_one u dist_nonneg)
  · intro i
    rw [Metric.infDist_singleton]
    change Tariff.amount 1 u (dist (localL 1 (carryX (G:=G) p (v i))) x) ≤ _
    rw [show localL 1 (carryX (G:=G) p (v i)) = slide 1 p + localL 1 (v i) from dis_seat ..]
    have H := dist_triangle (slide 1 p + localL 1 (v i)) (slide 1 p) x
    have dist_eq : dist (slide 1 p + localL 1 (v i)) (slide 1 p) = ‖localL 1 (v i)‖ := by
      rw [dist_eq_norm,add_sub_cancel_left]
    rw [dist_eq] at H
    apply (Tariff.amount_tri H zero_lt_one u (norm_nonneg _) dist_nonneg).trans
    rw [dist_comm (slide 1 p) x]
    apply mul_le_mul_left
    have er: (root (G:=G) 0 u).mark (v i)=Tariff.amount 1 u ‖localL 1 (v i)‖ := by
      change Tariff.amount 1 u (dist 0 (localL 1 (v i)))=_
      rw [dist_zero_left]
    exact er.symm.trans_le (Premium.width_ge (root (G:=G) 0 u) v i)

theorem joined_root (x:Room)(u:ℕ)(T:Packet (Foot G) r) :
    markQ (root x u) T ≤ markQ (district x (u+u)) T := by
  apply quota_mono
  intro v
  simpa only [root,district,Tariff.amount_zero,mul_one] using
    (final_price (l:=1) zero_lt_one le_rfl u {x} x (Set.singleton_nonempty _)
      isClosed_singleton (d:=0) (by rintro y ⟨⟩; exact (dist_self x).le)
      le_rfl (localL (G:=G) 1) v)

theorem finite (u:ℕ)(T:Packet (Foot G) r)(h:Bounded T) :
    markQ (root 0 u) T≠⊤ := Aug.support_cost _ _ _ zero_lt_one _ h

end YM.Integration.WilsonIndependentRawWordGeometry
