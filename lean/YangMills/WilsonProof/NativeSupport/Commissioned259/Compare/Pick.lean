import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Invert
import YangMills.WilsonProof.NativeSupport.Commissioned259.Consistent

/-! # Detector measurements: ancillary costs -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set MeasureTheory PowerSeries Asymptotics
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 Matrix
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale O.Score O.Enh O.Canon Dframe O.Read MS.Theater
variable {G : Gauge} {I : Type*} {n h : ℕ} {V : Arenas G} {B : ℝ → Frames G} {R : ℝ→PowerSeries ℂ}
    {X : Filter I}

-- reach mismatch estimate from the *same* p, on the prepositioned compact
lemma coin {d : Fin n→ℕ} (x : Points n) (u : Slots G d) (b : Toon G h) (p : ℕ) (t : ℝ) :
    coord b (purchased V u x h p t) = crop p t (farCf V u x (flash b)) := by
  simp_rw [purchased,map_sum,_root_.map_smul,pivotδ,smul_eq_mul,mul_ite,mul_one,mul_zero]; simp
lemma hull (h : G.Simple) {T r : I→ℝ} {b a : ℝ} (ht : ∀ᶠ i in X, 0 < T i) (hr : Tendsto r X (𝓝[>] 0))
    (ha : ∀ᶠ i in X, T i ≤ a * (g0 G (r i)) ^ (-b)) : Tendsto (fun i=> r i*T i) X (𝓝[>] 0) := by
  let g:=g0 G ∘ r; have hp : Tendsto g X (𝓝[>]0) := (pace h).comp hr; have hh := now hp
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
  · have hT : T =O[X] fun i=>g i^(-b) := by
      refine IsBigO.of_bound a ?_
      filter_upwards [ht,ha,hh] with i h ha hv; rwa [Real.norm_of_nonneg h.le,Real.norm_of_nonneg (Real.rpow_nonneg hv.le _)]
    refine IsBigO.trans_tendsto (g'':=g) ?_ (tendsto_nhdsWithin_iff.mp hp).1
    apply ((length h (b+1)).comp_tendsto hr |>.mul hT).congr' (EventuallyEq.refl ..)
    refine hh.mono fun i hi=>?_ ; change g i ^ (b+1) * g i ^ (-b) = g i; rw [ ← Real.rpow_add hi, show b+1+-b=1 by ring,Real.rpow_one]
  exact (ht.and (hr.eventually self_mem_nhdsWithin)).mono fun i h=>mul_pos h.2 h.1

lemma front_cost (P : O.Canon.Physical V R B) {d : Fin n→ℕ} {K : Set (Points n)} (hK : IsCompact K) (hk : K⊆conf n)
    {x : I→Points n} {u : I→Slots G d} {L : ℝ} (hL : 0 ≤ L) (hx : ∀ᶠ i in X, x i∈K) (hu : ∀ᶠ i in X,u i∈Balls L G d)
    (b : Toon G h) (p q : ℕ) (hp : q≤p) {t : I→ℝ} (ht : Tendsto t X (𝓝 0)) :
    (fun i=> coord b (purchased V (u i) (x i) h p (t i)-purchased V (u i) (x i) h q (t i))) =O[X] (fun i=>t i^(q+1)) := by
  simp_rw [map_sub, coin]
  -- difference of p and q comes also from Tunes.excess, can take logarithmic parameter 1
  have hz : Tunes (fun (_:I)=> (1:ℝ)) X (fun (_:I)=>(1:ℝ)) (fun i=>farCf V (u i) (x i) (flash b)) := by
    intro n; have he : ∃ C:ℝ, ∀ u∈Balls L G d, ∀ x∈K, ‖coeff n (farCf V u x (flash b))‖ ≤ C := by
      obtain ⟨C,hC⟩ := through_horizon hL P hK hk (fun i : (↥(Balls L G d) × ↥K) => i.1.property)
        (fun i=> i.2.property) (flash b) n
      exact ⟨C,fun u hu x hx=> hC ((⟨u,hu⟩,⟨x,hx⟩) : (↥(Balls L G d) × ↥K))⟩
    obtain ⟨C,hC⟩ := he
    exact Fare.cent ((hx.and hu).mono fun i hi=>hC _ hi.2 _ hi.1)
  obtain ⟨j,H⟩:= Tunes.excess (Eventually.of_forall fun (_:I)=> show (1:ℝ)≤1 from le_rfl)
    (ht.abs.eventually (ge_mem_nhds (by simp : (|(0:ℝ)|)<1))) (isBigO_refl t X) p q hp hz
  exact H.congr_right (fun i=>by simp [logs])

lemma finish (P : O.Canon.Physical V R B) {d : Fin n→ℕ} {K : Set (Points n)} (hK : IsCompact K) (hk : K⊆conf n)
    {x : I→Points n} {u : I→Slots G d} {L : ℝ} (hL : 0 ≤ L) (hx : ∀ᶠ i in X, x i∈K) (hu : ∀ᶠ i in X,u i∈Balls L G d)
    (b : Toon G h) (p q n : ℕ) (hp : q≤p) (hq : q+1≤n) {t g T : I→ℝ} {a : ℝ} (ha : 0<a)
    (hg : Tendsto g X (𝓝 0)) (ht : t=O[X] g) (hT : ∀ᶠ i in X, 1 ≤ T i) {W : I→Sec G h}
    (H : (fun i=> coord b (W i - purchased V (u i) (x i) h p (t i)))=O[X] fun i=> T i ^ (-a) * (g i)^n) :
    (fun i=> coord b (W i - purchased V (u i) (x i) h q (t i)))=O[X] fun i=> (g i)^(q+1) := by
  have h : (fun i=> coord b (W i - purchased V (u i) (x i) _ p (t i)))=O[X] fun i=> (g i)^(q+1) := by
    refine (H.trans ?_).trans (Fare.over_pow (q+1) n hq X g (hg.abs.eventually (ge_mem_nhds (by simp : (|(0:ℝ)|)<1))))
    apply IsBigO.of_bound'
    refine hT.mono fun i h'=>?_ ; rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ((Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans h') _)).trans_le (Real.rpow_le_one_of_one_le_of_nonpos h' (neg_nonpos.mpr ha.le)))
  refine (h.add ((front_cost P hK hk hL hx hu b p q hp (ht.trans_tendsto hg)).trans (ht.pow _))).congr_left ?_
  intro i; rw [←map_add, sub_add_sub_cancel ]
end YM.FVA2.GradedFar259.Comparing
