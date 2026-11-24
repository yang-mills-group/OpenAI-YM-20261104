import YM.WilsonMS.Scales.IcePack
/-!
# Normalize in position coupling and reach the actual position scheme

The array `proposed` is prescribed internally (Wick/Wilson input). Here
g is literal MS parameter. Its inverse object reads at a once-fixed X-scale.
This is an end-to-end use of the quantitative remainder after exact field
normalization. The statement of this module could still be viewed as in
the filtered position scheme (frame may add lower engineering). Mass
independence will be a separate engineering argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.FrameX
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1 Lattice
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open PowerSeries (coeff mk X constantCoeff)
open Fiscal BMenu Rider Reservoir VisitH Sea Fray FrameConj FrameConj.Gates Ice
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d j n : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable {Q : Store G} (P : Rose.Pick Q) (W : XSpace.Initialize G) (A : Prescription (Ensure.deck G))
  {M : Booked (Ensure.deck G)} (F : MS_Data G M) (μ : ℝ)

def softX (d : ℕ) :=
  substitute (Counter (χMS μ P F)) (thawed Q F μ d)

def softK (d : ℕ) (x : Points n) :=
  substitute (Counter (χMS μ P F)) (Thaw Q F μ d x)

def Vine (p : XSpace.Mesh) :=
  (Rose.chosen W P p).subst (pι A μ p)

lemma vine_roots (p : 𝕄) : Rooted (Vine P W A μ p) :=
  (root_sub (Rose.chosen W P p) (pι A μ p) (share ..)).trans
    ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (Rose.zero_choice ..))

lemma vine_budget (m : 𝕄) (h : Rose.Use W P m) :
    (pι A μ m).subst (Counter (Vine P W A μ m)) = Rose.χ W P m := by
  have hv : coeff 1 (Vine P W A μ m) ≠ 0 := by
    unfold Vine
    rw [tangential (pι A μ m) (share A.team _) (Program.ann A.team _)]
    exact h
  have hp : Rooted (Rose.χ W P m) :=
    (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (Rose.χzero ..)
  apply
    Ice.separate (F := Rose.chosen W P m)
      ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (Rose.zero_choice ..)) h
      ((root_sub _ _ (born ..)).trans (share ..)) hp
  rw [← Ice.assoc (share A.team _) (Ice.born ..), Rose.invertsX W P m h]
  exact counter_l (vine_roots P W A μ m) hv

lemma top_P (m : 𝕄) (d : ℕ) : Rose.proposed W P m d = substitute (Rose.χ W P m) (Q.opens W m d) := by
  ext1 i
  ext1 n
  ext1 t
  ext1 p
  rw [Rose.sent, Rose.turn_coins]
  obtain h :=
    cite_r (c := Rose.χ W P m)
      ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (Rose.χzero ..)) t p (Q.opens W m d)
  exact (congr_arg (coeff i) (h.trans (pcomp ..))).symm.trans (PowerSeries.coeff_mk ..)

lemma top_X (d : ℕ) (x : Sample n) :
    Rose.measureₓ W P d x = substitute (Rose.χ W P x.F) (Rose.cooked W Q d x) := by
  ext1 i
  ext1 p
  rw [Rose.measure_paid, Rose.turn_coins]
  obtain h :=
    readMove (c := Rose.χ W P x.F)
      ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (Rose.χzero ..)) (Rose.cooked W Q d x)
      p
  exact (congr_arg (coeff i) (h.trans (pcomp ..))).symm.trans (PowerSeries.coeff_mk ..)

lemma SoftK_funds (n d : ℕ) : FundsK (fun x : Points n => softK P F μ d x) (softX P F μ d) :=
  FundSwim (theorem_F Q μ F d n) _

lemma prep_shape {p : 𝕄 → Cn} {T : Cn} {F : 𝕄 → Reports G d} {Y : Reports G d} (v : Tracks p T)
    (h : ∀ i ≤ j, NShape (fun p => F p i) (Y i)) :
    NShape (fun i => substitute (p i) (F i) j) (substitute T Y j) := by
  intro n w K hp hx
  simp_rw [← enlist, rules]
  refine HoldT.sum _ fun i hi => ?_
  exact HoldT.both (Coast v i j) (h i (Finset.mem_Iic.mp hi) n w K hp hx)

lemma sail_shape (p : 𝕄 → Cn) (T : Cn) (v : Tracks p T) (U : Cirrus.Sample n → Octave G d n)
    {K : Set (Points n)} (P : Points n → Octave G d n) (q : Fin n → Sec G d)
    (h : ∀ i ≤ j, Vitals (fun x => U x i q) (fun x => P x i q) K) :
    Vitals (fun x => substitute (p x.F) (U x) j q) (fun x => substitute T (P x) j q) K := by
  simp_rw [bookCost, rules]
  refine Vitals.sum _ fun i hi => ?_
  exact Vitals.team (Vitals.confirm (Coast v i j)) (h i (Finset.mem_Iic.mp hi))
variable (hG : G.Simple) (hA : Installed W F A) (h : Commuting A)
include hG hA h

lemma back_marks : Tracks (fun i => Counter (Vine P W A μ i)) (Counter (χMS μ P F)) := by
  apply Counter_steady (vine_roots P W A μ) (built0 ..) (tracked μ P W A F hG hA h)
  exact (trueFirst μ P W A F hG hA h) ▸ one_ne_zero

/-- Smeared finite-regulator predictions, X-space, with a positive power
rate on every stipulated shape K. Absence of coherent changes would be
observable (the calibration functional and invariant frame solves).
 -/
lemma removing (j d : ℕ) : NShape (fun p => Rose.proposed W P p d j) (softX P F μ d j) := by
  refine
    NShape.changed
      (prep_shape (F := fun i => substitute (pι A μ i) (Q.opens W i d)) (Y := thawed Q F μ d) (j := j)
        (back_marks P W A F μ hG hA h) (fun i _ => unbilled μ Q hG hA h i d))
      ?_
  filter_upwards [Rose.usable W P hG] with i hi
  exact
    congr_fun
      (show
        substitute (Counter (Vine P W A μ i)) (substitute (pι A μ i) (Q.opens W i d)) =
          Rose.proposed W P i d
        from (earns _ (share ..) (Ice.born ..)).trans (by rw [vine_budget P W A μ i hi, top_P]))
      j

lemma on_position (K : Set (Points n)) (ht : IsCompact K) (he : K ⊆ conf n) (j d : ℕ)
    (X' : Fin n → Sec G d) :
    Vitals (fun x => Rose.measureₓ W P d x j X') (fun x => softK P F μ d x j X') K := by
  apply
    Vitals.exact_s
      (sail_shape _ _ (back_marks P W A F μ hG hA h) (fun x => Swift W Q A μ d x) (j := j) (K := K)
        (Thaw Q F μ d) X' (fun i _ => picture_cost W Q A μ F hG hA h ht he d i X'))
  filter_upwards [Rose.usable W P hG] with p hp x he
  subst p
  obtain hx := vine_budget P W A μ x.F hp
  unfold Swift
  rw [ups (Rose.cooked _ _ _ _) (share ..) (Ice.born ..), hx, top_X]

lemma Gm_compatible (d : ℕ) :
    substitute (χMS μ P F) (softX P F μ d) = realm (deck (Lμ Q F μ d)) (fun i => Continuum F μ i d) := by
  have hx : coeff 1 (χMS μ P F) ≠ 0 := by
    rw [trueFirst μ P W A F hG hA h]
    norm_num
  rw [softX, earns _ (Ice.born _) (built0 ..), counter_r (built0 ..) hx]
  exact Ice.retract _

/-- X array obtained from literal MS. Independent of its subtraction-scale
when defining the Wilson testing coupling and frame at one physical length.
 -/
lemma x_clock (r : ℝ) (d : ℕ) : softX P F μ d = softX P F r d := by
  ext1 n
  ext1 k
  ext1 p
  ext1 x
  exact
    tendsto_nhds_unique ((removing P W A F μ hG hA h n d).eval x p |>.limit)
      ((removing P W A F r hG hA h n d).eval x p |>.limit)

lemma k_clock (r : ℝ) (d : ℕ) (x : Points n) (hx : x ∈ conf n) (j : ℕ) :
    softK P F μ d x j = softK P F r d x j := by
  ext1 i
  obtain ⟨he, hI⟩ := SoftK_funds P F μ n d j i
  obtain ⟨hp, hV⟩ := SoftK_funds P F r n d j i
  exact
    (Test.unique_kernel he hp).mp
      (fun p => Eq.trans (hI p |>.symm) (by rw [x_clock P W A F μ hG hA h r, hV p])) hx
end YM.WilsonMS.FrameX
