import YM.RegulatorIR.Oracle.Calendar
import YM.PertExtension.FiltrationRule

/-! The centered inversion regulator for the common fixed-ratio measurement. The physical
period, top spacing, and top side are exactly those of the original bare Wilson arrays. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.MSFixedRatioGeometry
open Lattice RG RegulatorIR.Ledger RegulatorIR.Oracle PertExtension.LatticePT

def history (k : ℕ) : ℕ := k + 1 + k^2

def window (p : Patch) (w : Page history) : Side :=
  ⟨8*p.L.val^(history w.bindW-w.downW), by positivity⟩

/-- The original top period in lattice and physical units on a whole blocking history. -/
def circuit (p : Patch) : Circuit history (window p) where
  l w := epsilon p.L w.bindW * (p.L.val : ℝ)^w.downW
  P := period p.L
  sizeL _ := p.L
  J _ := p.J
  seats w := by
    apply Subtype.ext
    change 8*p.L.val^(history w.volW-w.offset) =
      (8*p.L.val^(history w.volW-(w.offset+1)))*p.L.val
    rw [show history w.volW-w.offset = history w.volW-(w.offset+1)+1 by have h := w.ok; omega,
      pow_succ, mul_assoc]
  odd _ := p.odd_side
  holds _ := p.coarse
  stands w := by
    have h : 0 < p.L.val^(history w.bindW-w.downW) := pow_pos p.L.pos _
    change 4≤8*p.L.val^(history w.bindW-w.downW)
    omega
  dual w := even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (by norm_num : 2∣8) _)
  week _ := p.order_cut
  shakes _ := le_rfl
  slow _ := Nat.le_succ _
  l_p w := mul_pos (inv_pos.mpr (pow_pos (by exact_mod_cast p.L.pos : (0:ℝ)<p.L.val) _))
    (pow_pos (by exact_mod_cast p.L.pos : (0:ℝ)<p.L.val) _)
  comet w := by
    change (epsilon p.L w.bindW*(p.L.val:ℝ)^w.downW)*
      ((8*p.L.val^(history w.bindW-w.downW):ℕ):ℝ) =
      ((8*p.L.val^(w.bindW+1)*p.L.val^(w.bindW^2):ℕ):ℝ)*epsilon p.L w.bindW
    push_cast
    calc
      _ = 8*(p.L.val:ℝ)^(w.downW+(history w.bindW-w.downW))*epsilon p.L w.bindW := by rw [pow_add]; ring
      _ = _ := by rw [Nat.add_sub_of_le w.good,history,pow_add]; ring

/-- Registration at the ultraviolet end uses the original size, spacing, and period. -/
theorem original (p : Patch) (k : ℕ) :
    window p (Page.opening history k) = side p.L k ∧
    (circuit p).l (Page.opening history k) = epsilon p.L k ∧
    (circuit p).P k = period p.L k := by
  refine ⟨Subtype.ext ?_, by simp [circuit,Page.opening], rfl⟩
  change 8*p.L.val^(history k-0) = 8*p.L.val^(k+1)*p.L.val^(k^2)
  rw [Nat.sub_zero, history, pow_add, mul_assoc]

/-- The centers of the inversion chart are the middle box in each coordinate. -/
def centers (n : Side) : Finset (Site n) := Finset.univ.filter fun x=>
  ∀ a, n.val/8 ≤ (x a).val ∧ (x a).val ≤ 2*(n.val/8)

/-- The top center average in the MS detector and this circuit range over the same sites. -/
theorem original_centers (p : Patch) (k : ℕ) :
    HEq (centers (window p (Page.opening history k))) (origins p.L k) := by
  rw [(original p k).1]
  rfl

/-- The circuit applies exactly the original smoothing, block factor, and branches at every step. -/
theorem patch (p : Patch) (w : Flap history) : (circuit p).pactP w = p := by cases p; rfl

/-- The first and next measurement spacing in old physical units. -/
def pair (k : ℕ) : Flap history := ⟨k,k,by unfold history; omega⟩

theorem measurement_lengths (p : Patch) (k : ℕ) :
    (circuit p).l (pair k).prev = 1 ∧ (circuit p).l (pair k).next = p.L.val := by
  have h : (p.L.val:ℝ)≠0 := by exact_mod_cast p.L.pos.ne'
  constructor
  · change ((p.L.val:ℝ)^k)⁻¹*(p.L.val:ℝ)^k=1
    exact inv_mul_cancel₀ (pow_ne_zero _ h)
  · change ((p.L.val:ℝ)^k)⁻¹*(p.L.val:ℝ)^(k+1)=p.L.val
    rw [pow_succ,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ h),one_mul]

/-- The same neighboring lengths as the two pullbacks at levels one and zero, with
one more fine step and the exact same torus throughout. -/
def inversePair (k : ℕ) : Flap history := ⟨k+1,k,by unfold history; omega⟩

theorem pullback_lengths (p : Patch) (k : ℕ) :
    (circuit p).l (inversePair k).prev = (p.L.val:ℝ)⁻¹ ∧
    (circuit p).l (inversePair k).next = 1 := by
  have h : (p.L.val:ℝ)≠0 := by exact_mod_cast p.L.pos.ne'
  constructor
  · change ((p.L.val:ℝ)^(k+1))⁻¹*(p.L.val:ℝ)^k=(p.L.val:ℝ)⁻¹
    rw [pow_succ, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h), mul_one]
  · exact (measurement_lengths p (k+1)).1

end YM.Integration.MSFixedRatioGeometry
