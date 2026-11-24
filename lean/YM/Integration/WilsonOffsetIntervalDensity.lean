import YM.Integration.WilsonOffsetConditionalCharge
import YM.Integration.IntrinsicProductLinearity

/-! The genuine nonlinear push, pointwise on the lower configuration. The
interval's whole offset discrepancy is one signed pair of original UV fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetIntervalDensity
open Function Set MeasureTheory Lattice Wilson RG Source Push.GridApprox RG16.Literal
open Extraction WilsonTranslatedFactory WilsonOffsetTraceHistory
open scoped Classical
variable {G : Gauge} {C : Family G} (H : C.Makes) {d N p : ℕ}

def scaled {m : ℕ} (hm : m ≤ N) (z : Site (C.side m p)) (v : C.label d) :=
  (((C.S.a m:ℂ)^d)⁻¹) • material H hm z v

theorem adjacent {m : ℕ} (hr : C.ref d ≤ m) (hm : m < N) (z : Site (C.side m p)) (v : C.label d) :
    scaled H hm.le z v = (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
      (scaled H hm ((C.path.levels.clock.op m p).ratio.embed z) v) := by
  let S := C.path.levels.clock.op m p
  have law := transfer H hr hm z v
  have step : (C.S.a (m+1):ℂ)^d * ((C.S.block m).val:ℂ)^d = (C.S.a m:ℂ)^d := by
    rw [← mul_pow,C.S.a_step,Complex.ofReal_div,Complex.ofReal_natCast]
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (C.S.block m).pos.ne')]
  have non : (((C.S.block m).val:ℂ)^d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (C.S.block m).pos.ne')
  have bought : ((C.S.a m:ℂ)^d)⁻¹ * ((C.S.block m).val:ℂ)^d = ((C.S.a (m+1):ℂ)^d)⁻¹ := by
    rw [← step,mul_inv,mul_assoc,inv_mul_cancel₀ non,mul_one]
  have good := WilsonOffsetTraceHistory.integrable H hm (hr.trans (Nat.le_succ _)) (S.ratio.embed z) v
  unfold scaled
  rw [StepData.push_smul _ _ _ _ good]
  change (((C.S.a m:ℂ)^d)⁻¹) • (entry H hm.le z v).density z (C.localSection d) (C.path.rep N p m) = _
  rw [law,smul_smul,bought]; rfl

theorem along {k : ℕ} (hr : C.ref d ≤ k) (hk : k ≤ N) (y : Site (C.side k p)) (v : C.label d) :
    scaled H hk y v = pushTo C.path N p hk (scaled H (le_refl N) (anchor C.S p hk y) v) := by
  have all (i : ℕ) (ki : k ≤ i) (hi : i ≤ N) : scaled H hk y v =
      pushTo C.path N p ki (scaled H hi (anchor C.S p ki y) v) := by
    induction i,ki using Nat.le_induction with
    | base => simp [anchor,Schedule.toDepth,Ratio.embed,Schedule.steps]
    | succ m km ih =>
      rw [pushTo_next C.path N p km,←anchor_next C.S p km]
      exact (ih (Nat.le_trans (Nat.le_succ m) hi)).trans (congrArg (pushTo C.path N p km)
        (adjacent H (p:=p) (hr.trans km) hi (anchor C.S p km y) v))
  exact all N hk le_rfl

theorem aligned {k : ℕ} (hr : C.ref d ≤ k) (hk : k ≤ N) (y : Site (C.side k p)) (x : C.label d) :
    material H hk y ((C.factory d N p).terminal.symm x) =
      credit C N p d (C.O N p x (anchor C.S p hk y)) k hk := by
  let v := (C.factory d N p).terminal.symm x
  have zero : ((C.S.a N:ℂ)^d) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')
  have seed : scaled H (le_refl N) (anchor C.S p hk y) v =
      fun U => (bare (C.beta N p) U:ℂ)*C.O N p x (anchor C.S p hk y) U := by
    funext U; unfold scaled material; simp only [Pi.smul_apply,smul_eq_mul]
    rw [born H (hr.trans hk),←mul_assoc,←mul_assoc,inv_mul_cancel₀ zero,one_mul,(H.wilson.starts N p).2]
    rfl
  have turn := along H hr hk y v
  rw [seed] at turn
  unfold credit
  rw [←turn,scaled,smul_smul,mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos k).ne')),one_smul]

theorem credit_difference {k : ℕ} (hk : k ≤ N) (f g : Cut C N p) (cf : Continuous f) (cg : Continuous g) :
    credit C N p d (f-g) k hk = credit C N p d f k hk - credit C N p d g k hk := by
  let weight (b : Bool) : ℂ := if b then 1 else -1
  let taps (b : Bool) : Cut C N p := if b then f else g
  have live (b : Bool) : Continuous (taps b) := by cases b <;> simp [taps,cf,cg]
  have all := IntrinsicProductLinearity.credit_sum C N p d k hk weight taps live
  simpa [Fintype.sum_bool,weight,taps,sub_eq_add_neg] using all

theorem physical {k : ℕ} (hr : C.ref d ≤ k) (hk : k ≤ N) (y : Site (C.side k p))
    (o : Site (C.side N p)) (x : C.label d) :
    credit C N p d (C.O N p x o) k hk - material H hk y ((C.factory d N p).terminal.symm x) =
      credit C N p d (C.O N p x o-C.O N p x (anchor C.S p hk y)) k hk := by
  rw [aligned H hr hk,credit_difference hk]
  all_goals exact continuous_const.smul ((C.localSection d).continuous_places _ _)

end YM.Integration.WilsonOffsetIntervalDensity
