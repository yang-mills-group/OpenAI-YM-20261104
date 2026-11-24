import YM.GradedFar.Continuation.Insert
import YM.GradedFar.Physical.Output

namespace YM.FVA2.GradedFar.AppointedFiledMeter
noncomputable section
open Function Filter Set MeasureTheory
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe PowerSeries
open Continuation Continuation.Window OPE Orbits Physical
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {n m : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}

structure Layout (G : Gauge) {n m : ℕ} (d : Fin n → ℕ) (e : Fin m → ℕ)
    (I : Type*) (K : Set (Points n)) (S : Set (Points m)) (L R : ℝ) where
  w : Window
  viewer : I
  x : Points n
  hx : x ∈ K
  y : Points m
  hy : y ∈ S
  u : Inputs G d
  hu : Within L u
  v : Inputs G e
  hv : Within R v

variable (N : WilsonPrescription G)
variable {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {prescription : MS.Land.Prescription (Press.portDeck G)}
  (agreement : Main.Match N simple M prescription true)

theorem throughCrop (p : ℕ) (heater : ℝ) (first second : PowerSeries ℂ)
    (same : ∀ j ≤ p, coeff j first = coeff j second) :
    crop p heater first = crop p heater second := by
  simp only [YM.FVA2.GradedFar.crop_eq]
  apply Finset.sum_congr rfl
  intro j hj
  rw [same j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)]

include agreement

theorem originalStamp {I : Type*} {K : Set (Points n)} {S : Set (Points m)}
    {L R : ℝ} (l : Layout G d e I K S L R) (cap : ℕ)
    (hd : ∀ i, d i ≤ cap) (he : ∀ i, e i ≤ cap)
    (confined : forest l.x (squeeze (-l.w.sep) l.y) ∈ conf (n+m))
    (j : ℕ) :
    coeff j (row N l.x l.u l.y l.v l.w.sep) =
      Measure.outlook N.scheme N.criterion cap _ ⟨forest l.x (squeeze (-l.w.sep) l.y),confined⟩ j
        (Fin.append (installedInputs hd l.u) (installedInputs he l.v)) :=
  Continuation.coeff_row agreement l.x l.u l.y l.v l.w.sep hd he confined j

variable {A : Family G} {o : Extraction.Order} {P : Table A.book}
variable (U : Spec.Final A o P) (H : FramesH P)

set_option maxHeartbeats 1200000 in
theorem roundedOnFiled (K : Set (Points n)) (S : Set (Points m)) (windowsPaid : Set Window)
    (p cap : ℕ) (hd : ∀ i, d i ≤ cap) (he : ∀ i, e i ≤ cap) (t sourceMeter : ℝ → ℝ)
    (transfer : ∃ M : ℝ, 0 < M ∧ ∀ᶠ w in windows windowsPaid, 0 ≤ 1+(Window.sep w) ∧
      sourceMeter (Window.len w)^(p+1) ≤ M*(gYM G (Window.len w))^(p+1))
    (filed : ∀ L R : ℝ, ∃ rowRead : Layout G d e (View U) K S L R → ℂ,
      ∃ stamps : Layout G d e (View U) K S L R → PowerSeries ℂ,
      ∃ fileClock : Layout G d e (View U) K S L R → ℝ,
      ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ l in Filter.comap Layout.w (windows windowsPaid),
        rowRead l = Physical.Y0 U H d e l.w l.viewer l.x l.y l.u l.v ∧
        fileClock l = t l.w.len ∧
        (∃ hc : forest l.x (squeeze (-l.w.sep) l.y) ∈ conf (n+m),
          ∀ j ≤ p, coeff j (stamps l) =
            Measure.outlook N.scheme N.criterion cap _ ⟨forest l.x (squeeze (-l.w.sep) l.y),hc⟩ j
              (Fin.append (installedInputs hd l.u) (installedInputs he l.v))) ∧
        ‖rowRead l-crop p (fileClock l) (stamps l)‖ ≤ C*sourceMeter l.w.len^(p+1)*(1+l.w.sep)^a) :
    RoundedAt N (Physical.Y0 U H d e) windowsPaid K S t p := by
  intro L R
  obtain ⟨rowRead, stamps, fileClock, C, hC, a, paid⟩ := filed L R
  obtain ⟨M, hM, wallet⟩ := transfer
  refine ⟨C*M, mul_pos hC hM, a, ?_⟩
  obtain ⟨W, hW, subset⟩ := Filter.mem_comap.mp paid
  filter_upwards [hW, wallet] with w hw hcash
  intro viewer x hx y hy u hu v hv
  let l : Layout G d e (View U) K S L R := ⟨w,viewer,x,hx,y,hy,u,hu,v,hv⟩
  have event := subset (show l ∈ Layout.w ⁻¹' W from hw)
  obtain ⟨hrow, hclock, ⟨hc, hm⟩, debt⟩ := event
  have hseries : crop p (t (Window.len w)) (stamps l) = crop p (t (Window.len w)) (row N x u y v (Window.sep w)) := by
    apply throughCrop
    intro j hj
    exact (hm j hj).trans (originalStamp N agreement l cap hd he hc j).symm
  rw [hrow, hclock] at debt
  change ‖Physical.Y0 U H d e w viewer x y u v-crop p (t (Window.len w)) (stamps l)‖ ≤
    C*sourceMeter (Window.len w)^(p+1)*(1+(Window.sep w))^a at debt
  rw [hseries] at debt
  calc
    _ ≤ C*sourceMeter (Window.len w)^(p+1)*(1+(Window.sep w))^a := debt
    _ ≤ C*(M*(gYM G (Window.len w))^(p+1))*(1+(Window.sep w))^a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcash.2 hC.le) (pow_nonneg hcash.1 _)
    _ = _ := by ring

end
end YM.FVA2.GradedFar.AppointedFiledMeter

