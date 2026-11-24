import YM.Integration.WilsonMaxwellThermometerChiralSlots
import YM.Next.MAXWELL.House
import YM.Integration.WilsonMaxwellThermometerTrace

/-! A same-chirality Wick line, including derivatives of either physical
curvature, vanishes off the coincidence diagonal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerLines
open Analysis WilsonMaxwellThermometerTrace Set Maxwell Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerChiralSlots
open WilsonMaxwellThermometerRotations
open scoped BigOperators Topology
variable {G : Gauge}

private theorem evaluated (x : E4) (hx : x≠0) (c : G.ColorIndex) (a b i j : Axis) :
    fare c (cell a b) (cell i j) x = curl (fun k l => grad k (grad l Green) x) a b i j := by
  rw [show fare c (cell a b) (cell i j) x = K (omegaLeg c a b) (omegaLeg c i j) x 0 by
    rw [K, sub_zero]; rfl, omega_K_eq _ _ _ _ _ _ hx, if_pos rfl, sub_zero, bareCurl,
    Pi.sub_apply, Bare.opp_grad hx, Bare.opp_grad hx]
  simp only [curl, eq_comm]

theorem vanish (x : E4) (hx : x≠0) (c : G.ColorIndex) (s : Bool) (a b : P) :
    fare c (slot s a) (slot s b) x = 0 := by
  rw [← fare_pair c _ _ hx]
  simp only [slot, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    fare_pair, evaluated x hx c]
  convert balance _ (Hess_sym hx) (harmonic hx) s a b using 1; ring

theorem derivative {j : ℕ} (c : G.ColorIndex) (p : Flavor j) (q : Flavor 0) (u : E4)
    (h : ∀ x : E4, x≠0 → fare c p q x = 0) {x : E4} (hx : x≠0) :
    fare c (feed u j p) q x = 0 := by
  have hh := K_left_D (flavor j c p) (flavor 0 c q) hx u
  rw [← consecutive] at hh
  simp only [K, sub_zero] at hh
  have hd : (fun z => fare c p q z) =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    filter_upwards [open_away.mem_nhds (show x ∈ away from hx)] with z hz using h z hz
  exact hh.symm.trans ((GermD u hd).trans (by simp [D]))

end YM.Integration.WilsonMaxwellThermometerLines
