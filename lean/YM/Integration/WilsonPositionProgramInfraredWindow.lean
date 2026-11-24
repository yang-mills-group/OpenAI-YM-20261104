import YM.Integration.WilsonPositionProgramInfraredRoom
import YM.Integration.WilsonPositionProgramInfraredBlocks

/-! Fit the full auxiliary period and fine mesh on the chronological original blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramInfraredWindow
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler WilsonPositionProgramCommonWindow
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Run G) (simple : G.Simple) (D : XSpace.Run) {a : Axis} {ε : ℝ}
local notation "Λ" => RG16.Lambda C.family.path.levels

def next (w : ℕ → ℕ) (n k : ℕ) := w (n+k)

theorem append (w : ℕ → ℕ) (n j : ℕ) : elapsed w (n+j)=elapsed w n+elapsed (next w n) j := by
  exact Finset.sum_range_add w n j

private theorem uniform (L : ℝ) (hL : 0 < L) (v : ℕ) (ell : ℝ) (h : 1 ≤ ell) (i : ℕ)
    (upper : (i:ℝ)*L ≤ ell^((3:ℝ)/2)+2*ell) :
    (v*i*i:ℕ) ≤ (v:ℝ)*(3/L)^2*ell^4 := by
  have sq : ell^((3:ℝ)/2) ≤ ell^2 := by
    rw [←Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)
  have base : ell ≤ ell^2 := by nlinarith only [mul_nonneg (zero_le_one.trans h) (sub_nonneg.mpr h)]
  have cnt : (i:ℝ) ≤ (3/L)*ell^2 := by
    apply (le_div_iff₀ hL).2 at upper
    calc _ ≤ (ell^((3:ℝ)/2)+2*ell)/L := upper
         _ ≤ (3*ell^2)/L := by apply div_le_div_of_nonneg_right _ hL.le; linarith
         _ = _ := by ring
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg i) cnt 2) (Nat.cast_nonneg v)
  push_cast
  nlinarith only [hs]

/-- All prices use this single index. The physical infrared date is exact as well as the top. -/
theorem chosen (purchase : WilsonPositionProgramNestedElection.course simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (ratio : D.ratio=(3:ℕ)^d) (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) :
    ∃ start : ℕ, ∃ w : ℕ → ℕ, (∀ k, (C.family.S.block (start+k)).val=D.ratio^(w k)) ∧
      ∀ᶠ n in atTop, ∃ b ≤ n, ∃ j > 0, let i := elapsed (next w n) j
        C.family.S.a ((start+n)+j)/C.family.S.a (start+n)=(D.step i).spacing ∧
        Λ (start+n)^((3:ℝ)/2) ≤ (i:ℝ)*Real.log D.ratio ∧
        (i:ℝ)*Real.log D.ratio ≤ Λ (start+n)^((3:ℝ)/2)+2*Λ (start+n) ∧
        elapsed w b + D.reserve*i*i = elapsed w n ∧
        elapsed (next w b) (n+j-b)=D.reserve*i*i+i := by
  obtain ⟨start,w,stamps,dv⟩ := WilsonPositionProgramInfraredBlocks.nested C D purchase hd ratio
  refine ⟨start,w,stamps,?_⟩
  have grow : Tendsto (fun n : ℕ => start+n) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left n start) tendsto_id
  let L := Real.log D.ratio
  have hp : 1 < D.ratio := lt_of_lt_of_le (by decide) D.large
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp)
  have top := grow.eventually (WilsonPositionProgramInversion.chosen C simple D
    (WilsonPositionProgramNestedElection.prior purchase) hd ratio pace)
  have room := WilsonPositionProgramInfraredRoom.capacity C simple D start w stamps ((D.reserve:ℝ)*(3/L)^2) 4
  filter_upwards [top,room] with n top enough
  obtain ⟨weights,j,jpos,file,_,low,high⟩ := top
  have increasing : StrictMono fun k : ℕ => D.ratio^k := strictMono_nat_of_lt_succ fun k => by
    rw [pow_succ]; exact lt_mul_of_one_lt_right (pow_pos (Nat.zero_lt_of_lt hp) _) hp
  have same : weights=next w n := by
    funext k
    apply increasing.injective
    exact (file k).symm.trans (by simpa only [next,Nat.add_assoc] using stamps (n+k))
  subst weights
  let i := elapsed (next w n) j
  have big : 1 ≤ Λ (start+n) := by
    have pos := WilsonAdmissionScale.logarithm_pos C.family.path.levels (start+n)
    change 1 ≤ 2+Real.log _
    change 0 < Real.log _ at pos
    linarith
  have available : D.reserve*i*i ≤ elapsed w n := by
    exact_mod_cast (uniform L hL D.reserve (Λ (start+n)) big i high).trans enough
  have portions (k : ℕ) (hk : k < n) : w k ∣ D.reserve*i*i := by
    have hi : w k ∣ i := Finset.dvd_sum fun l _ => dv k (n+l) (by omega)
    exact dvd_mul_of_dvd_right hi _
  obtain ⟨b,hb,till⟩ := WilsonPositionProgramInfraredBlocks.close w dv n _ available portions
  have actual (k : ℕ) : (C.family.S.block ((start+n)+k)).val=D.ratio^(next w n k) := by
    simpa only [next,Nat.add_assoc] using stamps (n+k)
  refine ⟨b,hb,j,jpos,fine_spacing C D _ _ actual j,low,high,till,?_⟩
  have both := append w b (n+j-b)
  rw [show b+(n+j-b)=n+j by omega,append w n j] at both
  change elapsed w n+i=elapsed w b+elapsed (next w b) (n+j-b) at both
  change elapsed (next w b) (n+j-b)=D.reserve*i*i+i
  exact Nat.add_left_cancel (calc
    elapsed w b+elapsed (next w b) (n+j-b) = elapsed w n+i := both.symm
    _ = elapsed w b+(D.reserve*i*i+i) := by rw [←till,Nat.add_assoc])

end YM.Integration.WilsonPositionProgramInfraredWindow
end
