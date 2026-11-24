import YM.Integration.WilsonThermometerCourseHearing
import YM.Integration.WilsonMacroscopicForwardTransfer

/-! An original seven-face thermometer heard through the older Wilson posterior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCourseResidual
open Finset Function MeasureTheory Lattice Wilson RG Source Marker FVA1 OPE.Therm
open Extraction Table Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open OriginalForcedAddresses MergeProof MergeProof.Accent MergeProof.East Extra.Trajectories
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerCourseIntake
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open scoped Classical BigOperators Topology

local notation "J" => Stock.census (Fin 3)
def face (s : Finset (Fin 3)) : (J).Mode := ⟨s,mem_univ _⟩
local notation "whole" => face univ

/-- The correction is in the top square-free coordinate of the original census. -/
def edit (x : Poly J) (q : ℂ) : Poly J := x + Poly.send whole (q - (logTo 3 x).part whole)

private theorem room (s : (J).Mode) : s.val.card ≤ 3 := by
  simpa only [Fintype.card_fin] using Finset.card_le_univ s.val

private theorem top_mul (x : Poly J) (hx : x.part (J).quiet = 1) (z : ℂ) :
    x * Poly.send whole z = Poly.send whole z := by
  calc
    _ = (∑ s : (J).Mode, Poly.send s (x.part s)) * Poly.send whole z := by rw [Poly.studs]
    _ = _ := by
      rw [sum_mul,Finset.sum_eq_single (J).quiet]
      · have join : Poly.merges (J).quiet whole whole := ⟨by simp [Census.quiet],by simp [Census.quiet]⟩
        rw [tagged_mul _ _ _ join,hx,one_mul]
      · intro s hs ne
        by_contra bad
        obtain ⟨_,joint⟩ := merges_of_tagged_mul bad
        apply ne
        apply Subtype.ext
        apply eq_empty_iff_forall_notMem.mpr
        exact fun a ha => Finset.disjoint_left.mp joint.1 ha (mem_univ a)
      · exact fun h => (h (mem_univ _)).elim

/-- Prescribing the full conditional log changes its raw triple by exactly the
same amount. The six lower faces and the quiet denominator are kept. -/
theorem amended (x : Poly J) (hx : x.part (J).quiet = 1) (q : ℂ) :
    (logTo 3 (edit x q)).part whole = q ∧
    ∀ s : (J).Mode, (edit x q).part s =
      x.part s + if s = whole then q - (logTo 3 x).part whole else 0 := by
  let z := q - (logTo 3 x).part whole
  let a := Poly.send whole z
  have apart : whole ≠ (J).quiet := fun e => by
    have bad : (univ : Finset (Fin 3)) = ∅ := congrArg Subtype.val e
    exact univ_nonempty.ne_empty bad
  have a0 : a.part (J).quiet = 0 := by simp [a,Poly.part_send,Ne.symm apart]
  have factor : edit x q = x * Poly.pass a := by
    rw [show Poly.pass a = 1 + a from pass_send (i:=whole) univ_nonempty z,mul_add,mul_one]
    change x+ a = x+x * Poly.send whole z
    rw [top_mul x hx]
  have a1 : (Poly.pass a).part (J).quiet = 1 := Poly.pass_part a a0
  have eqn : connected (Poly.pass a) = a :=
    pass_inj (connected_quiet a1) a0 (pass_connected a1)
  have y1 : (edit x q).part (J).quiet = 1 := by
    change x.part (J).quiet + a.part (J).quiet = 1
    rw [hx,a0,add_zero]
  constructor
  · rw [←log_to (edit x q) y1 3 room,factor,connected_mul hx a1,eqn,Poly.part_plus,
      log_to x hx 3 room]
    simp [a,Poly.part_send,z]
  · intro s
    simp only [edit,Poly.part_plus,Poly.part_send]

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
  {N per i : ℕ} (upper : i ≤ N) (o : Positions (Fin 3) (R.family.side N per))
local notation "C" => R.family
local notation "j" => fun h : Fin 3 => index A (grade h)
local notation "v" => vector A (Finset.univ : Finset (Fin 3))
local notation "refs" => ∀ h : Fin 3, R.family.ref ((j) h) ≤ N
local notation "W₀" => Config G (R.family.side i per)

def table (W : W₀) : Poly J :=
  (((R.family.path.rep N per i).eval W : ℂ)⁻¹) • incoming R A simple upper o W

theorem observed (ref : refs) (W : W₀) (s : (J).Mode) :
    (table R A simple upper o W).part s = actualTransport C (N:=N)
      (fun U => ∏ h ∈ s.val, R.family.O N per (A.station.wheel.atCut (N,per) ((j) h) ((v) h))
        (o.origin h) U) upper W := by
  have read := WilsonPositionThermometerDepositedFaces.deposited R simple N per A.station (j) (v)
    o ref upper s W
  change (((R.family.path.rep N per i).eval W : ℂ)⁻¹) *
    (incoming R A simple upper o W).part s = _
  rw [show (incoming R A simple upper o W).part s = _ from read,Complex.real_smul]
  have pos : (R.family.path.rep N per i).eval W ≠ 0 :=
    (Multi.AxisShift.chosen_positive R.makes.wilson upper W).ne'
  have nz : ((R.family.path.rep N per i).eval W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pos
  rw [←mul_assoc,inv_mul_cancel₀ nz,one_mul]

/-- Replace just the paid connected triple on its domain. Every proper face,
including the older singleton and pair means, is still transported on the
original full interacting posterior. -/
theorem original (ref : refs) (E : Set W₀) (q : W₀ → ℂ) {g ε : ℝ}
    (gg : 0 ≤ g) (ee : 0 ≤ ε)
    (pay : ∀ W ∈ E, g^7 * ‖(logTo 3 (table R A simple upper o W)).part whole - q W‖
        ≤ 8*ε*g^9) {u : ℕ} (old : u ≤ i) :
    let T := table R A simple upper o
    let Q := fun W => if W ∈ E then edit (T W) (q W) else T W
    (∀ W ∈ E, (logTo 3 (Q W)).part whole = q W) ∧
    (∀ W (s : (J).Mode), s ≠ whole → (Q W).part s = (T W).part s) ∧
    ∀ s : (J).Mode,
      let err := fun W => (g^7 : ℝ) • ((T W).part s - (Q W).part s)
      (∀ W, ‖actualTransport C (N:=N) err old W‖ ≤ 8*ε*g^9) ∧
      ‖∫ W,actualTransport C (N:=N) err old W ∂scene R.family.path N per u‖ ≤ 8*ε*g^9 := by
  intro T Q
  have normalized (W : W₀) : (T W).part (J).quiet = 1 := by
    rw [show (T W).part (J).quiet = _ from observed R A simple upper o ref W (J).quiet]
    simp only [show ((J).quiet.val : Finset (Fin 3)) = ∅ from rfl,Finset.prod_empty]
    exact actualTransport_const C R.makes le_rfl 1 upper W
  have proper (W : W₀) (s : (J).Mode) (ne : s ≠ whole) :
      (Q W).part s = (T W).part s := by
    by_cases h : W ∈ E
    · simp only [Q,if_pos h,(amended (T W) (normalized W) (q W)).2,if_neg ne,add_zero]
    · simp [Q,h]
  refine ⟨fun W h => by simp only [Q,if_pos h];exact (amended _ (normalized W) (q W)).1,proper,?_⟩
  intro s err
  have paid (W : W₀) : ‖err W‖ ≤ 8*ε*g^9 := by
    dsimp only [err]
    by_cases he : W ∈ E
    · by_cases eqn : s = whole
      · subst s
        rw [norm_smul,Real.norm_of_nonneg (pow_nonneg gg _)]
        rw [show (Q W).part whole = (T W).part whole + (q W - (logTo 3 (T W)).part whole)
          from by simp [Q,he,(amended (T W) (normalized W) (q W)).2]]
        rw [sub_add_cancel_left,neg_sub]
        exact pay W he
      · rw [proper W s eqn,sub_self,smul_zero,norm_zero]; positivity
    · simp only [Q,if_neg he,sub_self,smul_zero,norm_zero]
      positivity
  have every := actualTransport_norm_le C R.makes upper paid old
  letI : IsProbabilityMeasure (scene R.family.path N per u) := probability R.makes.wilson (old.trans upper)
  refine ⟨every,?_⟩
  simpa using norm_integral_le_of_norm_le_const (μ:=scene R.family.path N per u) (ae_of_all _ every)

end YM.Integration.WilsonThermometerCourseResidual
end
