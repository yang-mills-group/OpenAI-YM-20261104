import YM.WilsonMS.Scales.PointMove
/-!
# Stance triangle and the formal coupling read

`Rose.Detector` reads `together` on connected three-mark *point* observables
and then smears; not defined by products of averaged arrays. Keep the stance
normalization and read the same vertex
after the cutoff parameter relation. Consequence: converges jointly, is
real nonsingular. Reference scale fixed but no position choices in the
resulting series. We have not taken continuum limit inside the divergent
B frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.FrameConj
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1 Lattice
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open Fiscal BMenu Rider Reservoir VisitH Sea Fray
open Gates Rose
open PowerSeries (constantCoeff coeff mk)
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable {n d : ℕ} {i : ℝ} {c : Cn}

lemma pcomp (c T : PowerSeries ℂ) : Coupling.composeS c T = T.subst c := by
  unfold Coupling.composeS
  rw [show PowerSeries.map (algebraMap ℂ ℂ) c = c from
      PowerSeries.ext fun n => PowerSeries.coeff_map ..]

lemma usePool (h : Rooted c) {F : PowerSeries ℂ} (n : ℕ) :
    coeff n (F.subst c) = ∑ i ∈ Finset.Iic n, cut c i n * coeff i F := by
  rw [← pcomp]
  exact Eq.symm (congr_fun (Coupling.explicit h F) n)

lemma Worried (h : Rooted c) : PowerSeries.HasSubst (S := ℂ) c :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm.trans h)

lemma transept (h : Rooted c) (P : Octave G 6 3) :
    Rose.b3 (Rose.batchT (substitute c P)) = (Rose.b3 (Rose.batchT P)).subst c := by
  have he (p : Rose.Badge) : Rose.batchT (substitute c P) p = (Rose.batchT P p).subst c :=
    ((readMove h P (missing (Rose.tag G) p))).trans (pcomp ..)
  rw [b3]
  simp_rw [he]
  unfold b3
  simp only [two_smul, PowerSeries.subst_add (Worried h), PowerSeries.subst_mul (Worried h),
    PowerSeries.subst_sub (Worried h)]
variable (μ : ℝ) {Q : Store G} (P : Rose.Pick Q) (W : XSpace.Initialize G)
  (A : Prescription (Ensure.deck G)) {M : Booked (Ensure.deck G)} (F : MS_Data G M)
local notation "ƒ" => pι A μ

def Swift (Q : Store G) (A : Prescription (Ensure.deck G)) (μ : ℝ) (d : ℕ) (x : Cirrus.Sample n) :
    Octave G d n :=
  substitute (pι A μ x.F) (Rose.cooked W Q d x)

lemma detection (p : 𝕄) (j : ℕ) :
    coeff j ((Rose.Detector W P p).subst (ƒ p)) =
      Deposit p (fun x => coeff j (Rose.b3 (Rose.batchT (Swift W Q A μ 6 x)))) (test P) := by
  let c := ƒ p
  have he : Rooted c := share ..
  let g (x : Cirrus.Sample 3) := Rose.together W Q x
  rw [usePool (c := c) he]
  unfold Deposit Swift
  simp_rw [transept (c := pι A μ _) (share A.team _), Rose.detector]
  unfold Deposit
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [usePool (c := ƒ p) he, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold Rose.together c
  ring

abbrev plays (P : Points 3 → Octave G 6 3) (x : Points 3) : Cn :=
  Rose.b3 (Rose.batchT (P x))

abbrev observe (P' : Points 3 → Octave G 6 3) : Cn :=
  PowerSeries.mk (fun j => (test P).applyTo (fun x => coeff j (plays P' x)))

def observed (P' : Points 3 → Octave G 6 3) : Cn :=
  let T := observe P P';
  (↑(Rose.c_T P) : ℂ)⁻¹ • (T - PowerSeries.C (coeff 0 T))

abbrev χMS :=
  observed P (Thaw Q F μ 6)

lemma built0 (P' : Points 3 → Octave G 6 3) : Rooted (observed P P') := by
  unfold observed Rooted
  simp

lemma takes (P' : Points 3 → Octave G 6 3) (n : ℕ) (hn : n ≠ 0) :
    coeff n (observed P P') =
      (↑(Rose.c_T P) : ℂ)⁻¹ * ((test P).applyTo fun x => coeff n (plays P' x)) := by
  unfold observed
  simp only [map_smul, map_sub, PowerSeries.coeff_C, if_neg hn, sub_zero, observe,
    PowerSeries.coeff_mk]
  rfl

private lemma prodC {f g : Points n → Cn} {K : Set (Points n)}
    (h : ∀ i : ℕ, ContinuousOn (fun x => coeff i (f x)) K)
    (ht : ∀ i : ℕ, ContinuousOn (fun x => coeff i (g x)) K) (i : ℕ) :
    ContinuousOn (fun x => coeff i (f x * g x)) K := by
  simp_rw [PowerSeries.coeff_mul]
  exact continuousOn_finsetSum _ (fun i _ => (h i.1).mul (ht i.2))

lemma tender {Q} {P : Points 3 → Octave G 6 3} (h : FundsK P Q) (j : ℕ) :
    ContinuousOn (fun x => coeff j (plays P x)) (conf 3) := by
  have he p (i : ℕ) : ContinuousOn (fun x => coeff i (Rose.batchT (P x) p)) (conf 3) := by
    unfold Rose.batchT
    simp_rw [PowerSeries.coeff_mk]
    exact h i _ |>.1
  unfold plays b3
  simp_rw [map_add, map_smul, map_sub]
  exact
    ((he _ _).sub
          (((prodC (he _) (he _) _).add (prodC (he _) (he _) _)).add (prodC (he _) (he _) _))).add
      ((continuousOn_const (c := (2 : ℂ))).smul (prodC (prodC (he {0}) (he { 1 })) (he { 2 }) j))

lemma ScoreP {f g : Points n → Cn} {F H : Sample n → Cn} {K : Set (Points n)}
    (h : ∀ i, Vitals (fun x => coeff i (F x)) (fun x => coeff i (f x)) K)
    (hu : ∀ i, Vitals (fun x => coeff i (H x)) (fun x => coeff i (g x)) K) (j : ℕ) :
    Vitals (fun x => coeff j (F x * H x)) (fun x => coeff j (f x * g x)) K := by
  simp_rw [PowerSeries.coeff_mul]
  exact Vitals.sum _ (fun i _ => (h i.1).team (hu i.2))
variable (h : G.Simple) (hx : Installed W F A) (hu : Commuting A)
include h hx hu

lemma reportedC (j : ℕ) :
    Fast (fun p => coeff j ((Rose.Detector W P p).subst (ƒ p)))
      (coeff j (observe P (Thaw Q F μ 6))) := by
  let t := test P
  let s := tsupport t
  let g (x : Sample 3) := Swift W Q A μ 6 x
  let p (x : Points 3) := Thaw Q F μ 6 x
  let Y (x : Sample 3) := Rose.b3 (Rose.batchT (g x))
  let f' x := plays p x
  have he : Vitals (fun x => coeff j (Y x)) (fun x => coeff j (f' x)) s := by
    have hh i (n : ℕ) :
      Vitals (fun x => coeff n (Rose.batchT (g x) i)) (fun x => coeff n (Rose.batchT (p x) i)) s := by
      unfold Rose.batchT
      simp_rw [PowerSeries.coeff_mk]
      exact picture_cost W Q A μ F h hx hu t.hasCompactSupport t.tsupport_subset 6 n _
    unfold Y f' plays b3
    simp_rw [map_add, map_smul, map_sub]
    exact
      (((hh _ _).sub
            (((ScoreP (hh _) (hh _) _).knits (ScoreP (hh _) (hh _) _)).knits
              (ScoreP (hh _) (hh _) _))).knits
        ((Vitals.const 2).team (ScoreP (ScoreP (hh _) (hh _)) (hh _) _)))
  simp_rw [detection μ P W A]
  unfold observe
  rw [PowerSeries.coeff_mk]
  obtain ⟨a, ha, C, hC, hK⟩ :=
    he.layPoint t.hasCompactSupport (tender (Gates.theorem_F Q μ F 6 3) j) (fun _ _ _ => rfl)
  obtain ⟨b, hb, hT⟩ := bound_fin t
  exact Fast.fed ha (hK.mono fun i hi => hi t (Set.Subset.refl _) b hT)

lemma tracked (j : ℕ) :
    Fast (fun i => coeff j ((Rose.chosen W P i).subst (ƒ i))) (coeff j (χMS μ P F)) := by
  by_cases hi : j = 0
  · subst j
    simp_rw [usePool (c := ƒ _) (share A.team _),
      show Finset.Iic (0 : ℕ) = {0} from Finset.ext (by simp), Finset.sum_singleton,
      show ∀ p : 𝕄, coeff 0 (chosen W P p) = 0 from fun _ =>
        (PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (zero_choice ..),
      mul_zero, show coeff 0 (χMS μ P F) = 0 from built0 ..]
    exact Fast.const _
  rw [← show observed P (fun x => Thaw Q F μ 6 x) = χMS μ P F from rfl]
  unfold chosen
  have he (p : 𝕄) := Worried (c := ƒ p) (share A.team _)
  simp_rw [PowerSeries.subst_smul (he _), PowerSeries.subst_sub (he _),
    show ∀ (i : 𝕄) (t : ℂ), (PowerSeries.C t).subst (ƒ i) = PowerSeries.C t from fun i t =>
      PowerSeries.subst_C t,
    map_smul, map_sub, PowerSeries.coeff_C, if_neg hi, sub_zero, smul_eq_mul]
  unfold observed
  simp only [map_smul, map_sub, PowerSeries.coeff_C, if_neg hi, sub_zero]
  exact (Fast.const _).mul (reportedC μ P W A F h hx hu j)
omit hu h hx

lemma tangential (S : Cn) (hx : Rooted S) (hh : coeff 1 S = 1) (P : Cn) :
    coeff 1 (P.subst S) = coeff 1 P := by
  rw [usePool hx]
  have hp : Finset.Iic (1 : ℕ) = {0, 1} :=
    Finset.ext fun i => by
      simp
      omega
  rw [hp, Finset.sum_insert (by simp), Finset.sum_singleton, cut, cut, pow_zero, pow_one,
    PowerSeries.coeff_one]
  simp [hh]
include h hx hu

lemma trueFirst : coeff 1 (χMS μ P F) = 1 := by
  have he := (tracked μ P W A F h hx hu 1).limit
  simp_rw [tangential (ƒ _) (share A.team _) (Program.ann A.team _)] at he
  exact tendsto_nhds_unique he (Rose.xc W P h)

omit h hx hu in
lemma lucid (I : 𝕄) : Clean ((chosen W P I).subst (ƒ I)) := by
  intro j
  rw [usePool (c := ƒ I) (share A.team _)]
  simp_rw [star_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [star_mul', (copy_clean A.team _ |>.powers i j), real_c]

lemma cleanχ : Clean (χMS μ P F) := by
  intro j
  obtain hh := (tracked μ P W A F h hx hu j).limit
  exact
    tendsto_nhds_unique (f := fun i => coeff j ((Rose.chosen W P i).subst (ƒ i)))
      (Tendsto.congr (fun i => lucid ..) hh.star) hh
end YM.WilsonMS.FrameConj
