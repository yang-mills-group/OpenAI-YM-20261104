import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Reports
import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Overtime
/-! # Connected-log recrop price on compacts & absolute cost at receipt
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Pose
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open FVA2.Scale O.Score Dframe Comparing Rose
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {n : ℕ} {I J : Type*} {E : Type*} [Norm E] {F : Filter I}

-- Use earlier log-accounting also here, with T=1.
def home (_ : I) : ℝ := 1
private lemma h1 : ∀ᶠ i in F, 1 ≤ home i := Eventually.of_forall fun _=> le_rfl
lemma homebound {w:I→ℝ} {z:I→E} (h:Fare home F w z) : z=O[F] w := by
  obtain ⟨p,h⟩:= h; simpa only [home,logs,Real.log_one,add_zero,one_pow,mul_one] using h

variable {w t : I→ℝ} {X A B Y : I→ℂ}
lemma crossed (ht:(fun i=> A i-X i)=O[F] w) (hq:(fun i=>B i-Y i)=O[F] w)
    (a : A=O[F] home) (y:Y=O[F] home) :
    (fun i=> A i * B i-X i * Y i)=O[F] w := by
  refine ((a.mul hq |>.congr_right (fun i=>one_mul _)).add (ht.mul y|>.congr_right (fun i=>mul_one _))).congr_left ?_
  intro i; ring
lemma mix_home (a:X=O[F] home) (b:Y=O[F] home) : (fun i=>X i*Y i)=O[F] home:= (a.mul b).congr_right (fun i=>one_mul _)
lemma use_log (X Y: I→ Badge→ℂ) (a : ∀ j,(fun i=>X i j - Y i j)=O[F] w)
    (b : ∀ j,(fun i=>X i j)=O[F] home) (c : ∀ j,(fun i=>Y i j)=O[F] home) :
    (fun i=> log3 (X i)-log3 (Y i))=O[F] w := by
  let U:= (Finset.univ : Badge)
  have each (p q:Badge) := crossed (a p) (a q) (b p) (c q)
  have hp:= crossed (each {0} {1}) (a {2}) (mix_home (b {0}) (b {1})) (c {2})
  refine (((a U).sub (((each {0,1} {2}).add (each {0,2} {1})).add (each {1,2} {0}))).add (hp.const_mul_left 2)).congr_left ?_
  intro i; unfold U log3; ring

section
variable {g : I→ℝ} (p : ℕ) (ht : t=O[F] g) (hh : ∀ᶠ i in F,|t i|≤1)
    (D : Badge → I → PowerSeries ℂ) (hD : ∀ b, Tunes home F home (D b))
include ht hh hD
lemma logcrop :
    (fun i=> log3 (fun b=> crop p (t i) (D b i)) - crop p (t i) (Rose.b3 (fun b=>D b i))) =O[F] fun i=>g i^(p+1) := by
  have c (b q:Badge) : (fun i=>crop p (t i) (D b i)*crop p (t i) (D q i)-crop p (t i) (D b i * D q i)) =O[F] (fun i=>g i^(p+1)) := (homebound (Tunes.overflow h1 hh ht p (hD b) (hD q))).congr_right (fun i=> by unfold home; ring)
  let a:Badge:={0}; let b:Badge:={1}; let d:Badge:={2}
  have L := c {0,1} d
  have C := c {0,2} b
  have Q := c {1,2} a
  have Z := (homebound (Tunes.overflow h1 hh ht p (Tunes.mix h1 (hD a) (hD b)) (hD d))).congr_right (g₂:=fun i=>g i^(p+1)) (fun i=>by unfold home; ring)
  have H := ((c a b).mul (homebound (Tunes.cuts h1 hh p (hD d)))).congr_right (g₂:=fun i=>g i^(p+1)) fun i=> mul_one _
  refine (((Z.add H).const_mul_left (2:ℂ)).sub ((L.add C).add Q)).congr_left fun i=>?_ ; unfold log3 b3 a b d; rw [ map_add, map_sub, _root_.map_smul, map_add,map_add ]; simp only [smul_eq_mul]; ring
end

variable {d : ℕ} (A : Way G d) (H : Jury.Thin A) {x : I → Points n}
    {K : Set (Points n)} (hK : IsCompact K) (hc : K ⊆ conf n) (hx : ∀ᶠ i in F,x i∈K)
    (u : Tags G d n)
include hK hc H hx
lemma on_compact (p : ℕ) : (fun i=> Jury.fxt A (x i) p u)=O[F] home := by
  obtain ⟨C,h⟩ := hK.exists_bound_of_continuousOn ((H n p u).mono hc)
  exact IsBigO.of_bound C (hx.mono fun i hi=> (h (x i) hi).trans_eq (by simp [home]))
lemma compact_tunes : Tunes home F home (fun i=> mk fun k=> Jury.fxt A (x i) k u) := fun j=> by
  simp_rw [coeff_mk]; exact Fare.bare (on_compact A H hK hc hx u j)
lemma bounded_array (p : ℕ) (ht : ∀ᶠ i in F,|t i|≤1) : (fun i=> array A (x i) p (t i) u)=O[F] home := by
  simp_rw [array_eq]; exact homebound (Tunes.cuts h1 ht p (compact_tunes A H hK hc hx u))
lemma truncate_array {g:I→ℝ} (hg : t=O[F] g) (q p : ℕ) (ht : ∀ᶠ i in F,|t i|≤1) (hp : p ≤ q) : (fun i=> array A (x i) q (t i) u-array A (x i) p (t i) u)=O[F] fun i=>g i^(p+1) := by
  simp_rw [array_eq]; exact (homebound (Tunes.excess h1 ht hg q p hp (compact_tunes A H hK hc hx u))).congr_right fun i=> mul_one _
omit hK hc H hx

/-- BB layout after paying analysis of (C.5) on the unselected state. -/
def booth (K : Set (Points n)) (F : Filter I) := F ×ˢ (𝓟 K)
lemma advertise (A : I → Points n→E) :
    (fun i:I × Points n=>A i.1 i.2)=O[booth K F] (w ∘ Prod.fst) ↔
    ∃ C:ℝ, ∀ᶠ i in F,∀ x∈K, ‖A i x‖ ≤ C*‖w i‖ := by
  simp only [isBigO_iff,booth,eventually_prod_principal_iff]; rfl
lemma placed : ∀ᶠ i in booth K F, i.2 ∈ K := eventually_prod_principal_iff.mpr (Eventually.of_forall fun _ x hx=>hx)

variable {D E' : I → Points n→ℂ} {a : Test n}
lemma opening (hv : ∀ᶠ i in F, ContinuousOn (D i) (conf n) ∧ ContinuousOn (E' i) (conf n))
    (h : (fun i:I × Points n=> D i.1 i.2 - E' i.1 i.2)=O[booth K F] (w ∘ Prod.fst))
    (ha : tsupport a⊆ K) : (fun i=>a.applyTo (D i)-a.applyTo (E' i))=O[F] w := by
  obtain ⟨C,hC⟩:= (advertise (fun i x=>D i x-E' i x)).mp h
  refine IsBigO.of_bound ((∫ x:Points n,‖a x‖)*C) ?_; filter_upwards [hC,hv] with i hi ⟨hD,hE⟩
  unfold Test.applyTo; rw [← integral_sub (a.smearing hD) (a.smearing hE)]
  have H : Integrable (fun x=>a x) := a.continuous.integrable_of_hasCompactSupport a.hasCompactSupport
  refine (norm_integral_le_of_norm_le (H.norm.mul_const (C*‖w i‖)) (Eventually.of_forall fun x=>?_)).trans_eq ((integral_mul_const _ _).trans (mul_assoc ..).symm)
  rw [ ← mul_sub, norm_mul ]; by_cases hx:x∈tsupport a; exact mul_le_mul_of_nonneg_left (hi x (ha hx)) (norm_nonneg _)
  rw [image_eq_zero_of_notMem_tsupport hx, norm_zero,zero_mul,zero_mul]

end YM.FVA2.GradedFar259.Pose
