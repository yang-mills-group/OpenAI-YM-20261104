import YM.UVExt.PathJet
import YM.UVExt.RealProduct

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Function Set Lattice Laurent Wilson Bloch Exterior Precision RG Bid Matrix NormedSpace
open scoped Classical Topology BigOperators ComplexConjugate ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (v : Dir G n)
local notation "𝒱" => G.Mat

def part (i : G.ColorIndex) : G.Color →L[ℝ] ℝ := PiLp.proj (𝕜:=ℝ) 2 (fun _=>ℝ) i
def matPart (i : G.ColorIndex) : G.Mat →L[ℝ] ℝ := ((part i).comp G.projectColor.toContinuousLinearMap).comp ((1/2:ℝ) • ((ContinuousLinearMap.id ℝ 𝒱) - (starL ℝ : 𝒱≃L[ℝ]𝒱).toContinuousLinearMap))

def sprout (x : Site n) (s : Slot) (i : G.ColorIndex) (t : ℝ) := s.atSite (represent (t • v)) x i

def bud (x : Site n) (s : Slot) (t : ℝ) := s.atSite (represent (t • v)) x

def scion (x : Site n) (s : Slot) : ℝ→𝒱 := G.colorMat ∘ bud v x s

def magnitude (L : G.Mat →L[ℝ] ℝ) := ContinuousLinearMap.opNorm (E:=G.Mat) L -- replaced
def pack (G : Gauge) (i : G.ColorIndex) := ‖part (G:=G) i‖ + magnitude (G:=G) (matPart i) * ‖(1:G.Mat)‖

def K (G : Gauge) := (1 + G.colorScale) + ∑ i : G.ColorIndex, pack G i

lemma pack_pos (G : Gauge) (i) : 0 ≤ pack G i := by exact add_nonneg (norm_nonneg _) (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
lemma pack_one (G : Gauge) (i) : pack G i ≤ K G := by unfold K; rw [add_comm]; exact le_add_of_le_of_nonneg (Finset.single_le_sum (fun j (_:j∈Finset.univ) => pack_pos G j) (Finset.mem_univ i)) (by positivity [G.colorScale_pos])
lemma K_pos (G : Gauge) : 1 ≤ K G := by unfold K; exact (le_add_of_nonneg_right G.colorScale_pos.le).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=> pack_pos ..)))
lemma K_color (G : Gauge) : G.colorScale ≤ K G := (le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=> pack_pos ..)))
lemma matPart_price (i : G.ColorIndex) : magnitude (G:=G) (matPart i) * ‖(1:G.Mat)‖ ≤ K G := (le_add_of_nonneg_left (norm_nonneg _)).trans (pack_one G i)
lemma part_price (i : G.ColorIndex) : ‖part (G:=G) i‖ ≤ K G := (le_add_of_nonneg_right (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))).trans (pack_one G i)
lemma sprout_mat (x s i) : sprout v x s i = matPart i ∘ curve v (Work.F02.slotWalk s) x := by
  funext t
  dsimp only [sprout,Function.comp_apply,matPart,curve]
  rw [Work.F02.atSite_curvature]; rfl

lemma sprout_diff (x s i) : ContDiff ℝ ω (sprout v x s i) := by rw [sprout_mat]; exact (matPart i).contDiff.comp (curve_smooth ..)

def tempo (len : ℝ) := K G * (1+2*len) * linkRate v
lemma tempo_pos (x : ℝ) (hx : 0 ≤ x) : 0 ≤ tempo v x := by unfold tempo linkRate; positivity [G.colorScale_pos,K_pos G]
lemma tempo_le {x y} (hr : x≤y) : tempo v x ≤ tempo v y := by unfold tempo linkRate; gcongr <;> positivity [G.colorScale_pos,K_pos G]

lemma linear_successor {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℝ→X} (h : ContDiff ℝ ω f) (L : X →L[ℝ] Y) (k : ℕ) (t : ℝ) : iteratedDeriv k (L ∘ f) t = L (iteratedDeriv k f t) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  rw [L.iteratedFDeriv_comp_left h.contDiffAt (by simp)]; rfl

lemma sprout_rate (L : ℝ) (x s i t k) (hq : (s.length:ℝ) ≤ L) :
    ‖iteratedDeriv k (sprout v x s i) t‖ ≤ K G * ((1+2*L)*linkRate v)^k := by
  have hlen : ((Work.F02.slotWalk s).length:ℝ) ≤ 2*L := by
    unfold Work.F02.slotWalk Slot.length Lattice.reverse at *
    simp only [List.length_append,square,List.length_cons,List.length_map,List.length_reverse,List.length_nil,Nat.cast_add,Nat.cast_ofNat] at *
    norm_num; linarith
  rw [sprout_mat]
  let w := Work.F02.slotWalk s
  change ‖iteratedDeriv k (matPart i ∘ curve v w x) t‖ ≤ _
  rw [show iteratedDeriv k (matPart i ∘ curve v w x) t= _ from linear_successor (X:=G.Mat) (curve_smooth v w x) (matPart (G:=G) i) k t]
  have hv : 0 ≤ linkRate v := mul_nonneg G.colorScale_pos.le (norm_nonneg _)
  calc
    _ ≤ magnitude (G:=G) (matPart i) * ‖iteratedDeriv k _ _‖ := ContinuousLinearMap.le_opNorm ..
    _ ≤ (magnitude (G:=G) (matPart i)*‖(1:G.Mat)‖) * ((w.length:ℝ)*linkRate v)^k := by
        exact (mul_le_mul_of_nonneg_left (curve_rate v w x t k) (show 0 ≤ magnitude (matPart (G:=G) i) by exact ContinuousLinearMap.opNorm_nonneg (matPart (G:=G) i))).trans_eq (by ring)
    _ ≤ _ := mul_le_mul (matPart_price _) (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hv) (mul_le_mul_of_nonneg_right (hlen.trans (le_add_of_nonneg_left zero_le_one)) hv) _) (by unfold linkRate; positivity [G.colorScale_pos]) (zero_le_one.trans (K_pos G))

lemma sprout_zero (x s i) : sprout (G:=G) v x s i 0=0 := by
  unfold sprout; rw [Work.F02.atSite_curvature,zero_smul,Push.stroll_zero,G.curvature_unit]; rfl
lemma sprout_first (x s i) : deriv (sprout v x s i) 0 = Work.F03.faceCurl (Work.F03.slotFace s x) v i := by
  exact ((part (G:=G) i).hasFDerivAt.comp_hasDerivAt 0 (Work.F03.slot_deriv s x v)).deriv

lemma sprout_bill (x s i L) (hq : (s.length:ℝ) ≤ L) : Tri (tempo v L) (‖part (G:=G) i‖*‖dColor G n 1 v‖) (sprout v x s i) := by
  refine ⟨⟨tempo_pos v _ ((Nat.cast_nonneg ..).trans hq), (sprout_diff v x s i).contDiffAt,fun k=>?_,fun k hk=>?_⟩,?_⟩
  · cases k
    · rw [iteratedDeriv_zero,sprout_zero]; norm_num
    next k =>
     exact (sprout_rate v L x s i 0 (k+1) hq).trans (by
       unfold tempo
       rw [mul_assoc _ _ (linkRate v)]
       have he : K G ≤ K G ^ (k+1) := (pow_one _).symm.trans_le (pow_le_pow_right₀ (K_pos G) (by omega))
       have hL := (Nat.cast_nonneg (α:=ℝ) s.length).trans hq
       have h : 0 ≤ ((1+2*L)*linkRate v) ^ (k+1) := by unfold linkRate; positivity [G.colorScale_pos,hL]
       simpa only [mul_pow] using mul_le_mul_of_nonneg_right he h)
  · obtain rfl : k=0 := by omega
    exact sprout_zero ..
  rw [iteratedDeriv_one,sprout_first]
  exact ((part (G:=G) i).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm (dColor G n 1 v) _) (norm_nonneg _))


theorem bud_smooth (x s) : ContDiff ℝ ω (bud v x s) := by
  refine ContDiff.comp (f:=fun p=>fun i=>sprout v x s i p) (g:=WithLp.toLp 2 (V:=G.ColorIndex→ℝ)) ?_ (contDiff_pi.mpr fun i=>sprout_diff ..)
  exact ContinuousLinearEquiv.contDiff (𝕜:=ℝ) (F:=G.Color) (PiLp.continuousLinearEquiv 2 ℝ _).symm

lemma attach_back (x : Site n) (w : Walk) : stop x w=x+wrap n (stop (0:Cover) w) := by
  have h (y : Cover) : stop (x + wrap n y) w=x+wrap n (stop y w) := by
    induction w generalizing y with
    | nil => rfl
    | cons d w ih => rw [stop,stop, ←ih (y+d.vec),map_add,wrap_vec,add_assoc]
  simpa using h 0

lemma ribbon (a b : Slot) (ha : a.offset=b.offset) (x : Site n) :
    ‖linkSum (collect G v) x a.walk - linkSum (collect G v) x b.walk‖ ≤ ((a.walk.length+b.walk.length:ℕ):ℝ)^2 * ‖dColor G n 1 v‖ := by
  have h : stop x a.walk = stop x b.walk := by rw [attach_back x a.walk,attach_back x b.walk,show stop (0:Cover) a.walk=stop 0 b.walk from ha]
  have hr : stop (0:Cover) (a.walk++Lattice.reverse b.walk)=0 := by rw [stop_append, show stop (0:Cover) a.walk = stop (0:Cover) b.walk from ha, reverse_stop]
  rw [show _ - _=linkSum (collect G v) x (a.walk++Lattice.reverse b.walk) by
       apply Multiplicative.ofAdd.injective; change (Multiplicative.ofAdd (linkSum (collect G v) x a.walk)) * (Multiplicative.ofAdd (linkSum (collect G v) x b.walk))⁻¹ = Multiplicative.ofAdd _
       rw [link_travel, link_travel,link_travel, travel_append,h, travel_reverse]]
  simpa only [List.length_append,Lattice.reverse,List.length_map,List.length_reverse,Nat.cast_add] using basket_bound v _ x hr

end YM.UVExt.Paths
