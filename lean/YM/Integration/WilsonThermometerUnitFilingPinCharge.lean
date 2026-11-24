import YM.Integration.WilsonThermometerUnitFilingCoverRoom
import YM.Integration.WilsonThermometerUnitFilingCoverEra

/-! Translate every angular bond of one captured row to the same genuine cover site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPinCharge
open Function Finset Lattice RG Gauge RegulatorIR Prim Budget Budget.Packet Budget.Tuple
open Halo Taping Geometry Spatial
open WilsonThermometerUnitFilingCoverRoom
open scoped ENNReal Classical BigOperators
variable {G:Gauge}{r:ℕ}

def grid (l ρ:ℝ)(hr:0<ρ)(u:ℕ)(x:Room):=
    (Premium.rooted (Tariff.native ρ hr u) x).uses (plot (G:=G) l)

theorem site (l:ℝ)(z:Cover)(a:Foot G):
    plot l (carryX z a)=Motion.slide l z+plot l a:=by
  change Geometry.seat l (Geometry.dis z a.1)=_
  rw [Geometry.dis_seat]
  rfl

theorem moved (l:ℝ){ρ:ℝ}(hr:0<ρ)(u:ℕ)(x:Room)(z:Cover)(h:dist x (Motion.slide l z)≤ρ)
    (w:Tuple (Foot G) r):
    (grid l ρ hr u x).width (Tuple.winding (carryX z) r w)≤
      (grid l ρ hr u 0).width w*(2:ℝ≥0∞)^u:=by
  let A:=Tariff.native ρ hr u
  let t:=Motion.slide l z
  let V:=grid (G:=G) l ρ hr u 0
  have two:1≤(2:ℝ≥0∞)^u:=one_le_pow₀ (by norm_num)
  have floor: V.width w≤V.width w*(2:ℝ≥0∞)^u:=le_mul_of_one_le_right (by positivity) two
  have drift:A.road x t≤(2:ℝ≥0∞)^u:=by
    change ENNReal.ofReal (1+dist x t/ρ)^u≤_
    apply pow_le_pow_left'
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by linarith [((div_le_one hr).2 h)])
  apply Premium.width_le
  · apply Tariff.diameter_le
    · exact (V.width_unit _).trans floor
    · intro i j
      change Tariff.amount ρ u (dist (plot l (carryX z (w i))) (plot l (carryX z (w j))))≤_
      rw [site,site,dist_add_left]
      exact ((Tariff.diameter_ge (A.uses (plot (G:=G) l)) w i j).trans (V.width_diameter _)).trans floor
  · intro i
    change A.road x (plot l (carryX z (w i)))≤_
    rw [site]
    calc
      _ ≤ A.road x t*A.road t (t+plot l (w i)):=A.tri ..
      _ ≤ (2:ℝ≥0∞)^u * V.width w:=by
        apply mul_le_mul' drift
        change Tariff.amount ρ u (dist t (t+plot l (w i)))≤_
        rw [show dist t (t+plot l (w i))=dist (0:Room) (plot l (w i)) by simp]
        exact V.width_ge w i
      _ = _:=mul_comm ..

theorem original (l:ℝ){ρ:ℝ}(hr:0<ρ)(u:ℕ)(x:Room)(z:Cover)(h:dist x (Motion.slide l z)≤ρ)
    (T:Packet (Foot G) r):
    markQ (grid l ρ hr u x) (echo (carryX z) T) ≤ markQ (grid l ρ hr u 0) T*(2:ℝ≥0∞)^u:=by
  unfold markQ
  let D:=carryX (G:=G) z
  rw [← quota_perm (Tuple.winding D r),← quota_raised]
  apply (show quota (echo D T ∘ Tuple.winding D r) _ = quota T _ by
    congr 1;funext q;exact echos D T q).trans_le
  exact quota_mono _ (moved l hr u x z h)

end YM.Integration.WilsonThermometerUnitFilingPinCharge
