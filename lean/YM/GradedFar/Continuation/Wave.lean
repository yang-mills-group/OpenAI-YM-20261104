import YM.GradedFar.Continuation.Extract

/-!
# The MS RHS

Exactly the MS *within this corpus's formalization* of the perturbative theory.
Transforms its `Equator.wave` and OPE vector by the given f,Z. No assertion about
anything other than the specified MS here (in particular no claim re-identifying
it with another scheme/microscopic prescription, or with any other integral prescription).
-/
namespace YM.FVA2.GradedFar.Continuation.Wave
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Window
open Stretch (till Deep Stiff)
open Margin (probe)
open scoped Topology BigOperators Classical Matrix
variable {G : Gauge} {n h m : ℕ} (N : WilsonPrescription G) {d : Fin n → ℕ} {e : Fin m → ℕ}
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {A : Prescription (Press.portDeck G)}
local notation "ν" => Teller.logNu 1
local notation "ℓf" => Measure.f N.criterion ν M
local notation "Z" => Measure.Z N.scheme N.criterion ν M
def transformed : Arenas G := fun d => Facets.actMark (Z d) (Facets.couple ℓf (Equator.wave ν M d))

def value (x : Points n) (u : Inputs G d) : PowerSeries ℂ := ∑ a : Choices G d, C (combo u a) *
  install (transformed N M) _ x (roll a)

def refund (x : Points n) (u : Inputs G d) (q : Q G) : PowerSeries ℂ :=
  ∑ a : Choices G d, C (combo u a) * O.Project.refund (seats Z) (seats (replay Z)) ℓf
    (fun v => OPECoefficients (Equator.wave ν M) v 0 x) (roll a) q

def cropped (x : Points n) (u : Inputs G d) (h p : ℕ) (t : ℝ) : Sec G h :=
  ∑ a : Toon G h, crop p t (refund N M x u (flash a)) • theory a

variable (H : Main.Match N simple M A true) {x : Points n}
include H
lemma on_book : transformed N M = book N := funext (H.eqconv ν)

lemma tall {w : Scan G n} (x : Points n) : FarCoefficients (book N) w x = O.Project.refund (seats Z) (seats (replay Z)) ℓf
      (fun v => OPECoefficients (Equator.wave ν M) v 0 x) w := by
  have h := (H.separatedOPE ν).gifts w 0 x
  have hv : Civil Z := O.Canon.office H.details.toServed.toPosted.toQuoted.toContract
  unfold O.Project.Gift at h; unfold O.Project.refund
  rw [h, O.Project.timely,spin_v hv,O.Project.receipt_K,(H.separatedOPE ν).wilson.start_u]; -- energy orientation

theorem fee (x : Points n) (u : Inputs G d) (p h : ℕ) (t : ℝ) : cropped N M x u h p t = cActual N x u h p t := by
  unfold cropped
  nth_rw 1 [← reconstructed (cActual N x u h p t)]; simp_rw [coord_actual,seriesComponent, tall N M H]; rfl

omit H in
lemma forest_empty {x : Points n} (y : Points 0) : forest x y = x := by
  ext1 i
  exact forest_left (m:=0) i

abbrev vacant : Inputs G (fun _ : Fin 0 => 0) := fun i => i.elim0

lemma only_value (x : Points n) (u : Inputs G d) (s : ℝ) (y : Points 0) :
    row N x u y vacant s = value N M x u := by
  rw [value,on_book N M H]
  unfold row
  let L : Choices G (fun _ : Fin 0 => 0) := fun i => i.elim0
  rw [Finset.sum_eq_single L]; swap
  · intro i _ he; exact False.elim (he (Subsingleton.elim ..))
  swap; · exact fun notMem => False.elim (notMem (Finset.mem_univ _))
  rw [combo,Fin.prod_univ_zero,map_one,one_mul]; unfold Subarray.bare
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold party; rw [forest_empty, show Fin.append (roll a) (roll L)=roll a from (funext fun i => Fin.append_left ..)]
  rfl

end
end YM.FVA2.GradedFar.Continuation.Wave

