import YM.UVExt.PathJet
import YM.Integration.WilsonSlotContactTruncation
import YM.Integration.LocalComparisonPackets
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Flat
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Taylor coefficients along the true exponential links of an arbitrary torus.  Each
oriented visit charges its own direction, including successive visits to the same bond. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPathTaylor
open Lattice Wilson RG Exterior Comparison.Stencils WilsonWalkMatrixSecant
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side}

def field (a : Directions G c) (t : ℝ) : Config G c := fun e => G.lieExp (t • a e)

def speed (a : Directions G c) (e : Edge (Site c)) : ℝ := ‖G.colorMat (a e)‖

def fare (a : Directions G c) (x : Site c) (w : Walk) : ℝ :=
  ((occurrences x w).map (speed a)).sum

private theorem fare_nonneg (a : Directions G c) (x : Site c) (w : Walk) : 0 ≤ fare a x w := by
  induction w generalizing x with
  | nil => exact le_rfl
  | cons d w ih => exact add_nonneg (norm_nonneg _) (ih _)

def curve (a : Directions G c) (x : Site c) (w : Walk) (t : ℝ) : G.Mat :=
  G.mat (travel (field a t) x w)

private def single (a : Directions G c) (d : Step) (x : Site c) (t : ℝ) : G.Mat :=
  G.mat (d.read (field a t) x)

private def signedColor (a : Directions G c) (d : Step) (x : Site c) : G.Color :=
  if d.neg then -a (d.used x) else a (d.used x)

private theorem reveal (a : Directions G c) (d : Step) (x : Site c) :
    single a d x = fun t => G.mat (G.lieExp (t • signedColor a d x)) := by
  funext t
  unfold single Step.read field signedColor
  split
  · rw [smul_neg,Work.F03.exp_neg_color]
  · rfl

private theorem single_smooth (a : Directions G c) (d : Step) (x : Site c) :
    ContDiff ℝ ω (single a d x) := by
  rw [reveal]
  exact G.exp_jet.comp (contDiff_id.smul contDiff_const)

private theorem cons_curve (a : Directions G c) (d : Step) (x : Site c) (w : Walk) :
    curve a x (d::w) = single a d x * curve a (x+d.vec) w :=
  funext fun _ => G.mat_mul _ _

theorem smooth (a : Directions G c) (x : Site c) (w : Walk) : ContDiff ℝ ω (curve a x w) := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons d w ih => rw [cons_curve]; exact (single_smooth ..).mul (ih _)

private theorem letter (a : Directions G c) (d : Step) (x : Site c) (t : ℝ) (k : ℕ) (X : G.Mat) :
    ‖iteratedDeriv k (single a d x) t * X‖ ≤ speed a (d.used x)^k * ‖X‖ := by
  rw [reveal,UVExt.Paths.ray_deriv,mul_assoc,Gauge.mul_frob_eq _ _ (G.mat_star_mul _)]
  have hs : ‖G.colorMat (signedColor a d x)‖ = speed a (d.used x) := by
    unfold signedColor speed
    split <;> simp only [map_neg,norm_neg]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',mul_assoc]
    exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left ih (norm_nonneg _)).trans_eq
      (by rw [hs,pow_succ',mul_assoc]))

/-- The native all-real ordered matrix derivative, priced at every actual lift of a visit. -/
theorem ordered (a : Directions G c) (x : Site c) (w : Walk) (t : ℝ) (k : ℕ) :
    ‖iteratedDeriv k (curve a x w) t‖ ≤ fare a x w ^ k * ‖(1:G.Mat)‖ := by
  induction w generalizing x t k with
  | nil =>
    change ‖iteratedDeriv k (fun _ : ℝ => (1:G.Mat)) t‖ ≤ (0:ℝ)^k * _
    cases k <;> simp [iteratedDeriv_succ']
  | cons d w ih =>
    rw [cons_curve,iteratedDeriv_mul ((single_smooth a ..).of_le (by simp)).contDiffAt
      ((smooth a ..).of_le (by simp)).contDiffAt]
    let X := single a d x
    let Y := curve a (x+d.vec) w
    calc
      _ ≤ ∑ i ∈ Finset.range (k+1),
          (speed a (d.used x)^i * fare a (x+d.vec) w^(k-i) * (k.choose i:ℝ)) * ‖(1:G.Mat)‖ :=
        (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
      _ = _ := (Finset.sum_mul ..).symm.trans (by rw [← add_pow]; rfl)
    change ‖(k.choose i:G.Mat) * iteratedDeriv i X t * iteratedDeriv (k-i) Y t‖ ≤ _
    rw [mul_assoc,← nsmul_eq_mul]
    apply norm_nsmul_le.trans ((mul_le_mul_of_nonneg_left (letter a _ _ _ _ _) (by positivity)).trans _)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih ..)
      (pow_nonneg (norm_nonneg _) _)) (by positivity)).trans_eq (by unfold speed; ring)

def jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (n : ℕ) (t : ℝ) : E :=
  ∑ k ∈ Finset.range (n+1), ((k.factorial:ℝ)⁻¹*t^k) • iteratedDeriv k f 0

private theorem linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] F) {f : ℝ → E}
    (hf : ContDiff ℝ ω f) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (B ∘ f) t = B (iteratedDeriv k f t) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, B.iteratedFDeriv_comp_left hf.contDiffAt (by simp),
    iteratedDeriv_eq_iteratedFDeriv]
  rfl

/-- The Taylor remainder has its full factorial also for vector and matrix observations. -/
theorem remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ ω f) (n : ℕ) (t C : ℝ)
    (hC : ∀ s, ‖iteratedDeriv (n+1) f s‖ ≤ C) :
    ‖f t - jet f n t‖ ≤ C * |t|^(n+1) / (n+1).factorial := by
  by_cases ht : t=0
  · subst t
    have h0 : jet f n 0 = f 0 := by rw [jet,Finset.sum_range_succ']; simp
    simp [h0]
  obtain ⟨B,hB,hE⟩ := exists_dual_vector'' ℝ (f t - jet f n t)
  let p := B ∘ f
  have hp : ContDiff ℝ ω p := B.contDiff.comp hf
  obtain ⟨s,_,hs⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n:=n) (Ne.symm ht)
    (hp.of_le (by simp)).contDiffOn
  have hpoly : taylorWithinEval p n (Set.uIcc 0 t) 0 t = B (jet f n t) := by
    rw [taylor_within_apply,jet,map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (Ne.symm ht))
      (hp.of_le (by simp)).contDiffAt Set.left_mem_uIcc, map_smul,sub_zero]
    exact congrArg _ (linear B hf k 0)
  have hh : |B (iteratedDeriv (n+1) f s)| ≤ C := by
    change ‖B (iteratedDeriv (n+1) f s)‖ ≤ C
    exact (B.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans
      ((one_mul _).le.trans (hC s)))
  calc
    ‖f t - jet f n t‖ = |B (f t - jet f n t)| := by
      rw [hE]
      change ‖f t - jet f n t‖ = |‖f t - jet f n t‖|
      exact (abs_of_nonneg (norm_nonneg _)).symm
    _ = |B (iteratedDeriv (n+1) f s)| * |t|^(n+1) / (n+1).factorial := by
      rw [map_sub,← hpoly,show B (f t) = p t from rfl,hs,linear B hf,sub_zero,abs_div,abs_mul,
        abs_pow,abs_of_nonneg (by positivity : 0 ≤ ((n+1).factorial:ℝ))]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)

theorem matrix (a : Directions G c) (x : Site c) (w : Walk) (n : ℕ) (t : ℝ) :
    ‖curve a x w t - jet (curve a x w) n t‖ ≤
      (fare a x w^(n+1) * ‖(1:G.Mat)‖) * |t|^(n+1) / (n+1).factorial :=
  remainder (smooth ..) n t _ (fun s => ordered a x w s (n+1))

abbrev Letter (G : Gauge) := WilsonSlotContactTruncation.Letter G

def score (a : Directions G c) (x : Site c) (l : List (Letter G)) : ℝ :=
  ((WilsonSlotContactTruncation.contacts x l).map (speed a)).sum

private theorem cons_score (a : Directions G c) (x : Site c) (s : Letter G) (l : List (Letter G)) :
    score a x (s::l) = fare a x (closes s.1) + score a x l := by
  simp [score,fare,WilsonSlotContactTruncation.contacts]

private theorem score_nonneg (a : Directions G c) (x : Site c) (l : List (Letter G)) :
    0 ≤ score a x l := by
  induction l with
  | nil => exact le_rfl
  | cons s l ih => rw [cons_score]; exact add_nonneg (fare_nonneg ..) ih

private def oneSlot (a : Directions G c) (x : Site c) (s : Letter G) (t : ℝ) : ℂ :=
  WilsonSlotContactTruncation.coord (field a t) x s

private theorem slot_eq (a : Directions G c) (x : Site c) (s : Letter G) :
    oneSlot a x s = decode s.2 ∘ curve a x (closes s.1) := by
  funext t
  unfold oneSlot WilsonSlotContactTruncation.coord
  rw [WilsonWalkEndpointBias.atSite_reads]
  rfl

private theorem slot_smooth (a : Directions G c) (x : Site c) (s : Letter G) :
    ContDiff ℝ ω (oneSlot a x s) := by rw [slot_eq]; exact (decode s.2).contDiff.comp (smooth ..)

private theorem decode_bound (j : G.ColorIndex) (U : G.Mat) :
    ‖decode j U‖ ≤ (1/G.colorScale)*‖U‖ := by
  let Y := Pert.First.recoverL G U
  change ‖((Y j : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real,Real.norm_eq_abs]
  calc |Y j| = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j) Y| := by
         simp only [EuclideanSpace.basisFun_inner]
       _ ≤ ‖Y‖ := (abs_real_inner_le_norm _ _).trans_eq (by rw [OrthonormalBasis.norm_eq_one,one_mul])
       _ ≤ _ := WilsonWalkEndpointBias.recover_bound U

private theorem one_rate (a : Directions G c) (x : Site c) (s : Letter G) (t : ℝ) (k : ℕ) :
    ‖iteratedDeriv k (oneSlot a x s) t‖ ≤ fare a x (closes s.1)^k := by
  have step : iteratedDeriv k (oneSlot a x s) t =
      decode s.2 (iteratedDeriv k (curve a x (closes s.1)) t) := by
    rw [slot_eq]
    exact linear (decode (G:=G) s.2) (smooth a x (closes s.1)) k t
  rw [step]
  have h1 : ‖(1:G.Mat)‖ = G.colorScale := Gauge.unitary_frob (A:=1) (by simp)
  exact (decode_bound _ _).trans ((mul_le_mul_of_nonneg_left (ordered a x _ t k)
    (by positivity [G.colorScale_pos])).trans_eq (by
      rw [h1,one_div]
      calc _ = (G.colorScale⁻¹*G.colorScale)*fare a x (closes s.1)^k := by ring
           _ = _ := by rw [inv_mul_cancel₀ G.colorScale_pos.ne',one_mul]))

def read (a : Directions G c) (x : Site c) (l : List (Letter G)) (t : ℝ) : ℂ :=
  WilsonSlotContactTruncation.word (field a t) x l

private theorem split_read (a : Directions G c) (x : Site c) (s : Letter G) (l : List (Letter G)) :
    read a x (s::l) = oneSlot a x s * read a x l := rfl

theorem read_smooth (a : Directions G c) (x : Site c) (l : List (Letter G)) :
    ContDiff ℝ ω (read a x l) := by
  induction l with
  | nil => exact contDiff_const
  | cons s l ih => rw [split_read]; exact (slot_smooth ..).mul ih

/-- All independently charged original slot coordinates are differentiated together. -/
theorem product (a : Directions G c) (x : Site c) (l : List (Letter G)) (t : ℝ) (k : ℕ) :
    ‖iteratedDeriv k (read a x l) t‖ ≤ score a x l^k := by
  induction l generalizing k t with
  | nil =>
    change ‖iteratedDeriv k (fun _ : ℝ => (1:ℂ)) t‖ ≤ (0:ℝ)^k
    cases k <;> simp [iteratedDeriv_succ']
  | cons s l ih =>
    rw [split_read,iteratedDeriv_mul ((slot_smooth a ..).of_le (by simp)).contDiffAt
      ((read_smooth a ..).of_le (by simp)).contDiffAt,cons_score,add_pow]
    apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
    simp only [norm_mul,Complex.norm_natCast]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (one_rate a x s t i) (by positivity))
      (ih t (k-i)) (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg (fare_nonneg ..) _))).trans_eq
        (by ring)

theorem slots (a : Directions G c) (x : Site c) (l : List (Letter G)) (n : ℕ) (t : ℝ) :
    ‖read a x l t - jet (read a x l) n t‖ ≤ score a x l^(n+1) * |t|^(n+1) / (n+1).factorial :=
  remainder (read_smooth ..) n t _ (fun s => product a x l s (n+1))

/-- Application to a measured configuration whose true bond is the exponential of its sampled direction. -/
theorem material (U : ℝ → Config G c) (a : Directions G c)
    (h : ∀ t e, U t e = G.lieExp (t • a e)) (x : Site c) (l : List (Letter G)) (n : ℕ) (t : ℝ) :
    ‖WilsonSlotContactTruncation.word (U t) x l -
       jet (fun u => WilsonSlotContactTruncation.word (U u) x l) n t‖ ≤
      score a x l^(n+1) * |t|^(n+1) / (n+1).factorial := by
  have hU : U = field a := funext fun s => funext fun e => h s e
  subst U
  exact slots a x l n t

section Prescribed
open Tree Precision Marker LocalComparison Comparison.RG02 Comparison.Density.RenderM
open Next.SectorChange.Flat

theorem represent_field (a : Directions G c) (t : ℝ) : represent (t • labels a) = field a t := by
  funext e
  change G.lieExp ((t:ℝ) • collect G (labels a) e) * (1:G.El) = G.lieExp (t • a e)
  rw [collected,mul_one]

def freeDirection {b : Side} {ρ : Ratio b c} (H : Forest ρ) (a : AxisChart G H) : Directions G c :=
  fun e => if h : e ∈ H.trunks then 0 else a ⟨e,h⟩

/-- Evaluate the original no-hole forest chart at any of its free directions. -/
theorem live_field {b : Side} {ρ : Ratio b c} (H : Forest ρ) (a : AxisChart G H) (t : ℝ) :
    Work.F03.live H (0,t • a) = field (freeDirection H a) t := by
  funext e
  change H.drape (fun i => G.lieExp ((t • a) i) * replica ρ (represent 0) i) e =
    G.lieExp (t • freeDirection H a e)
  by_cases ht : e ∈ H.trunks
  · rw [freeDirection,dif_pos ht,smul_zero,G.mat_lieExp_zero]
    exact H.on_tree _ ⟨e,ht⟩
  · change H.drape _ (⟨e,ht⟩:H.Free) = _
    rw [H.off_tree,link_one,replica_one,Pi.one_apply,mul_one,freeDirection,dif_neg ht]
    rfl

variable {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {C : Family G}
    {D : V → ComparisonDensity.Address.Orbit} {datum : LocalFormal.Datum C B}
    {Y : Bulk.Chain C.path} {inputColors : TestSpace D → Bulk.Colors B G (C.side (datum.level+1) datum.period)}
    {P : MarkedPackets D G (C.side datum.level datum.period) B} {order : ℕ}

/-- The original finite packet on the genuine free chart, with independently specified
coupling and field parameter, before prescribing any coefficients. -/
theorem packet_material {b : Side} {ρ : Ratio b c} (P : MarkedPackets D G c B) (x : TestSpace D)
    (H : Forest ρ) (a : AxisChart G H) (g t : ℝ) :
    P.read x g (Work.F03.live H (0,t • a)) = P.read x g (field (freeDirection H a) t) :=
  congrArg (P.read x g) (live_field H a t)

/-- Any supplied original finite marked prescription reads its full extension along the
same physical angular field, for every signed test and nonzero coupling. -/
theorem prescribed (F : PrescribedPackets Y datum inputColors P order) (x : TestSpace D)
    (a : Directions G (C.side datum.level datum.period)) (g : ℝ) (hg : g ≠ 0) :
    P.read x g (field a g) = F.extension x g (labels a) := by
  rw [←represent_field]
  exact (F.value x g hg (labels a)).symm

def coefficient (F : PrescribedPackets Y datum inputColors P order) (x : TestSpace D)
    (a : Directions G (C.side datum.level datum.period)) (k : ℕ) : Poly B :=
  ((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun g : ℝ => F.extension x g (labels a)) 0 (fun _ => 1)

/-- At every true no-hole free key the complete packet has the prescribed punctured value.
Its purchased extension at zero carries the actual connected formal coefficients at that
same direction through the declared finite order. -/
theorem prescribed_material (F : PrescribedPackets Y datum inputColors P order) {b : Side}
    {ρ : Ratio b (C.side datum.level datum.period)} (H : Forest ρ) (a : AxisChart G H)
    (x : TestSpace D) :
    let A₀ := labels (freeDirection H a)
    (∀ g : ℝ, g ≠ 0 → P.read x g (Work.F03.live H (0,g • a)) = F.extension x g A₀) ∧
    ∀ k : ℕ, k ≤ order → coefficient F x (freeDirection H a) k =
      Order.observe B order (({ datum with colors := inputColors x, field := A₀ } :
        LocalFormal.Datum C B).markedLog Y order) k := by
  dsimp only
  refine ⟨fun g hg => ?_,fun k hk => F.coefficients x _ k hk⟩
  rw [live_field]
  exact prescribed F x (freeDirection H a) g hg

/-- A separately supplied finite-to-cover estimate on an original mode carries its exact
cost across the chart, including a residual from winding and the window boundary. -/
theorem prescribed_price (F : PrescribedPackets Y datum inputColors P order) {b : Side}
    {ρ : Ratio b (C.side datum.level datum.period)} (H : Forest ρ) (a : AxisChart G H)
    (x : TestSpace D) (k : ℕ) (hk : k ≤ order) (s : B.Mode) (cover : Poly B) (E : ℝ)
    (invoice : ‖(Order.observe B order (({ datum with colors := inputColors x, field := labels (freeDirection H a) } :
        LocalFormal.Datum C B).markedLog Y order) k).part s -
        cover.part s‖ ≤ E) : ‖(coefficient F x (freeDirection H a) k).part s - cover.part s‖ ≤ E := by
  rw [(prescribed_material F H a x).2 k hk]
  exact invoice

end Prescribed

end YM.Integration.WilsonMeasuredPathTaylor
