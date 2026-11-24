import YangMills.WilsonProof.NativeSupport.Commissioned259.Threshold
/-!
# Also finite-T price: may use any geometry threshold, *then* pay with the constant
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {I : Type} [TopologicalSpace I]

private abbrev PC (A : I → PowerSeries ℂ) : Prop := ∀ k : ℕ, Continuous (fun i=> coeff k (A i))
private lemma pc_times (A B : I → PowerSeries ℂ) (hf : PC A) (hg : PC B) : PC (fun i=> A i * B i) := by
  intro k; simp_rw [coeff_mul]
  exact continuous_finsetSum _ fun i _=> (hf _).mul (hg _)
private lemma pc_sum {J : Type} (A : J → I → PowerSeries ℂ) (l : Finset J) (ha : ∀ j ∈ l, PC (A j)) :
    PC (fun i => ∑ j ∈ l, A j i) := by
  intro k; simp_rw [map_sum]
  exact continuous_finsetSum _ fun i hi=> ha i hi k
private lemma pc_prod {J : Type} (A : J → I → PowerSeries ℂ) (l : Finset J) (ha : ∀ j ∈ l, PC (A j)) :
    PC (fun i => ∏ j ∈ l, A j i) := by
  induction l using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact fun _=> continuous_const
  | insert i l hi ih =>
    simp_rw [Finset.prod_insert hi]; exact pc_times _ _ (ha i (Finset.mem_insert_self ..))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))
private lemma pc_letter (A : I → ℂ) (ha : Continuous A) : PC (fun i=> C (A i)) := by
  intro k; simp_rw [coeff_C]; split
  · exact ha
  exact continuous_const

private lemma continuity_crop (A : I → PowerSeries ℂ) (ha : PC A) (p : ℕ) (t : I → ℝ) (ht : Continuous t) :
    Continuous (fun i=> crop p (t i) (A i)) := by
  simp_rw [crop_apply]; exact continuous_finsetSum _ fun i _=> ((Complex.continuous_ofReal.comp ht).pow _).mul (ha _)

variable {G : Gauge} {V : Arenas G} {R : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    {n m H h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H)
    (he : ∀ i, e i ≤ H) (hh : h ≤ H)
    (L : Law V R B) (P : O.Canon.Physical V R B)
section
variable {T : I → ℝ} {x : I → Points n} {y : I → Points m}
    (ht : Continuous T) (hx : Continuous x) (hy : Continuous y) (hp : ∀ i, 0 < T i)
    {u : I → Slots G d} {v : I → Slots G e}
    (cu : ∀ i j, Continuous (fun a : I => coord j (u a i)))
    (cv : ∀ i j, Continuous (fun a : I => coord j (v a i)))
    (hc : ∀ i, forest (x i) ((T i) • (y i)) ∈ conf (n+m))
    (hz : ∀ i, y i ∈ Outside m) (hk : ∀ i, x i ∈ conf n) (p : ℕ) (t : I → ℝ) (hr : Continuous t)

include cu in
private lemma continuity_coordinates (b : BasisSlots G d) : Continuous (fun i => coordinates b (u i)) :=
  continuous_finsetProd _ (fun i _ => cu i _)

include P hk hx cu in
lemma coeff_continuous (q : Q G) (j : ℕ) : Continuous (fun i => coeff j (farCf V (u i) (x i) q)) := by
  refine pc_sum (fun (b : BasisSlots G d) i => C (coordinates b (u i)) * FarCoefficients V (names b) (x i) q) _ (fun b _=>?_) j
  exact pc_times _ _ (pc_letter _ (continuity_coordinates cu b)) (fun j =>
    ContinuousOn.comp_continuous (f:=fun p : I=> x p) ((P.far (names b)).2.1 q j) hx hk)

include ht hx hy hp hc L P in
private lemma basis_cont (b : BasisSlots G d) (a : BasisSlots G e) :
    PC (fun i => measurement V B hd he (x i) (T i • y i) (-Real.log (T i)) (word b) (word a)) := by
  simp_rw [←inputs_names, measured_basis L P.dimensions]; refine pc_sum _ _ (fun j _=>?_) ; refine pc_times _ _ ?_ ?_
  · refine pc_prod _ _ (fun r _ k=>?_); simp_rw [power_T _ _ _ (hp _)]
    obtain ⟨p,hpoly⟩ := Rhythm.from_poly.mp (polynomial_T L (names a r) (j r) k); simp_rw [congr_fun hpoly]
    exact Continuous.mul (by fun_prop)
      (p.continuous.comp (Complex.continuous_ofReal.comp (ht.log (fun i=>(hp i).ne'))))
  intro k
  exact (P.awake _ _ _).comp_continuous (O.Enh.continual hx (Continuous.smul ht hy)) hc

include ht hx hy hp L P
include cu cv hc in
private lemma full_cont (j : ℕ) :
    Continuous (fun i => coeff j (measurement V B hd he (x i) (T i • y i) (-Real.log (T i)) (u i) (v i))) := by
  -- successive multilinearity before continuity
  simp_rw [near_extension hd he _ _ _ (u _), far_extension hd he _ _ _ (word _) (v _)]
  exact pc_sum _ _ (fun b _=> pc_times _ _ (pc_letter _ (continuity_coordinates cu b))
    (pc_sum _ _ fun r _=> pc_times _ _ (pc_letter _ (continuity_coordinates cv r)) (basis_cont hd he L P ht hx hy hp hc b r))) j

include cu cv hk hc hz hr in
lemma rows_cont :
    Continuous (fun i => crop p (t i) (measurement V B hd he (x i) (T i • y i) (-Real.log (T i)) (u i) (v i))) ∧
    Continuous (fun i => crop p (t i) (center V B he (T i • y i) hh (-Real.log (T i))
      (purchased V (u i) (x i) h p (t i)) (v i))) := by
  refine ⟨continuity_crop _ (full_cont hd he L P ht hx hy hp cu cv hc) p t hr,?_⟩
  have rate i : forest (0 : Points 1) (T i • y i)∈ conf (1+m) := by
    rw [← squeeze_T _ (hp i)]; exact lives _ (hz i)
  simp_rw [purchased, reading_linear]
  exact continuous_finsetSum _ fun j _=>
    (continuity_crop _ (coeff_continuous P hx cu hk (flash j)) p t hr).mul
      (continuity_crop _ (full_cont (d:=fun _ => h) (fun (_ : Fin 1)=> hh) he L P ht
        continuous_const hy hp (u:=fun i _=>theory j) (fun _ _=> continuous_const) cv rate) p t hr)
end
-- Need pass geometry-only lower threshold into upper bounds by using compact on boxes of coords.
section
abbrev Panel (L : ℝ) (G : Gauge) (d : Fin n → ℕ) := (i : Fin n) → Toon G (d i) →
    (Metric.closedBall (0:ℂ) L : Set ℂ)
private def Aboard {L : ℝ} (X : Panel L G d) : Slots G d := fun i =>
  (MS.Theater.Daylight (Press.portDeck G) (d i)).equivFun.symm (fun b=> (X i b).val)
private lemma recovery {L : ℝ} (u : Slots G d) (hu : u ∈ Balls L G d) : ∃ X : Panel L G d, u = Aboard X := by
  refine ⟨fun i b=>⟨_,(by rw [Metric.mem_closedBall, dist_zero_right]; exact hu i b)⟩,?_⟩
  funext i; apply Eq.symm ((MS.Theater.Daylight (Press.portDeck G) (d i)).equivFun.symm_apply_apply (u i))
private lemma aboard {L : ℝ} {f : I → Panel L G d} (hf : Continuous f) (i j) : Continuous (fun a => coord j (Aboard (f a) i)) := by
  simp_rw [Aboard, O.Score.coord, Module.Basis.coord_equivFun_symm]; fun_prop
private instance Cspace (L : ℝ) (G : Gauge) (d : Fin n → ℕ) : CompactSpace (Panel L G d) := by
  haveI := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:ℂ) L); infer_instance

variable {U : ℝ} {K : Set (Points n)} {S : Set (Points m)}
    (hU : 0 ≤ U) (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    {W : ℝ} (hW : 1 ≤ W)

/-- Fix any sufficiently large lower endpoint, geometrically admissible. -/
def clears (W : ℝ) (K : Set (Points n)) (S : Set (Points m)) : Prop :=
  ∀ T ≥ W, ∀ x ∈ K, ∀ y ∈ S, forest x (T • y) ∈ conf (n+m)

include hK hc hS hy in
lemma always_clear : ∀ᶠ W : ℝ in atTop, clears W K S := by
  have h := Real.tendsto_log_atTop.eventually (O.Read.for_far hK hc hS hy)
  have hw : ∀ᶠ T : ℝ in atTop, ∀ x ∈ K, ∀ y ∈ S, forest x (T • y) ∈ conf (n+m) := by
    filter_upwards [h,eventually_gt_atTop (0:ℝ)] with T h ht x hx y hy'
    rw [← squeeze_T _ ht]; exact h x hx y hy'
  obtain ⟨T0,h⟩ := eventually_atTop.1 hw
  exact (eventually_ge_atTop T0).mono fun i hi _ ht => h _ (hi.trans ht)

include L P hW hK hc hS hy
lemma bounded_window (ha : clears W K S) (Z : ℝ) (p : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ T ∈ Icc W Z, ∀ x ∈ K, ∀ y ∈ S, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      ∀ t : ℝ, |t| ≤ 1 → ‖crop p t (measurement V B hd he x (T • y) (-Real.log T) u v) -
        crop p t (center V B he (T • y) hh (-Real.log T) (purchased V u x h p t) v)‖ ≤ A := by
  let Q := Metric.closedBall (0:ℝ) 1
  let I := ↥(Icc W Z) × (↥K × ↥S) × ↥Q × (Panel U G d × Panel U G e)
  obtain ⟨H,J⟩ := rows_cont hd he hh L P (T:=fun i:I=> i.1.val) (x:=fun i=>i.2.1.1.val)
    (y:=fun i=>i.2.1.2.val) (u:=fun i=>Aboard i.2.2.2.1) (v:=fun i=>Aboard i.2.2.2.2)
    (by unfold I; fun_prop) (by unfold I; fun_prop) (by unfold I; fun_prop) (fun i=>zero_lt_one.trans_le (hW.trans i.1.property.1))
    (aboard (by unfold I; fun_prop)) (aboard (by unfold I; fun_prop))
    (fun i=>ha _ i.1.property.1 _ i.2.1.1.property _ i.2.1.2.property)
    (fun i=>hy i.2.1.2.property) (fun i=>hc i.2.1.1.property) p (fun i=> i.2.2.1.val) (by unfold I; fun_prop)
  haveI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  haveI := isCompact_iff_compactSpace.mp hK
  haveI := isCompact_iff_compactSpace.mp hS
  obtain ⟨C,h⟩ := isCompact_univ.exists_bound_of_continuousOn (H.sub J).continuousOn
  refine ⟨max 1 C, lt_max_of_lt_left zero_lt_one, fun T hT x hx y hy u hu v hv t ht =>?_⟩
  obtain ⟨X,rfl⟩ := recovery u hu; obtain ⟨Y,rfl⟩ := recovery v hv
  exact (h ((⟨T,hT⟩,(⟨x,hx⟩,⟨y,hy⟩),⟨t,(by change t∈Metric.closedBall (0:ℝ) 1; rwa [Metric.mem_closedBall,Real.dist_eq,sub_zero])⟩,X,Y) : I) (mem_univ _)).trans (le_max_right ..)
include hU
lemma all_T (ha : clears W K S) (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ T ≥ W, ∀ x ∈ K, ∀ y ∈ S, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      ∀ t g : ℝ, |t| ≤ 1 → |t| ≤ 2*g →
        ‖crop p t (measurement V B hd he x (T • y) (-Real.log T) u v) -
          crop p t (center V B he (T • y) hh (-Real.log T)
            (purchased V u x h p t) v)‖ ≤ C*((T⁻¹)^(h+1)+g^(p+1))*(1+Real.log T)^a := by
  obtain ⟨C,hC,a,H⟩ := M2_large hd he hh hU L P hK hc hS hy p
  obtain ⟨W',hAbove⟩ := eventually_atTop.mp H
  let Z := max W W'
  have hz : 0 < Z := zero_lt_one.trans_le (hW.trans (le_max_left ..))
  obtain ⟨A,hA,K⟩ := bounded_window hd he hh L P (U:=U) hK hc hS hy hW ha Z p
  refine ⟨max C (A*Z^(h+1)),lt_max_of_lt_left hC,a,?_⟩
  intro T hT x hx y hy u hu v hv t g ht hg
  have log := Real.log_nonneg (hW.trans hT)
  have tpos : 0 < T := zero_lt_one.trans_le (hW.trans hT)
  have gg : 0 ≤ g := by linarith [abs_nonneg t]
  rcases le_total T Z with htZ|htZ
  · apply (K _ ⟨hT,htZ⟩ x hx y hy u hu v hv t ht).trans
    calc
      A = A * Z ^ (h+1) * (Z⁻¹)^(h+1) * 1^a := by rw [one_pow,mul_one,mul_assoc, ← mul_pow, mul_inv_cancel₀ hz.ne',one_pow,mul_one]
      _ ≤ _ := by gcongr; apply le_max_right; apply le_trans ?_ (le_add_of_nonneg_right (by positivity)); gcongr; simpa using log
  apply (hAbove T ((le_max_right ..).trans htZ) x hx y hy u hu v hv t g ht hg).trans; gcongr; exact le_max_left ..
end
end YM.FVA2.GradedFar259
