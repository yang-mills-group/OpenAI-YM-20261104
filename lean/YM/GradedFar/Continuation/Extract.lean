import YM.GradedFar.Continuation.Decode

/-!
# Instantiate a band lease to derive the through-q OPE price for *all* small r
-/
namespace YM.FVA2.GradedFar.Continuation
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Window
open Stretch (till Deep Stiff)
open Margin (probe)
open scoped Topology BigOperators Classical Matrix
variable {G : Gauge} {n h m : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ} {e : Fin m → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "g" => gYM G
local notation "τ" => 𝓝[>] (0:ℝ)
variable {I : Type} (t : ℝ → ℝ) {c C η B : ℝ} (hb : 0<B) (hc : 0<c) (hC : c ≤ C)
  {p q P : ℕ} (ht : Tendsto (fun r => t r/gYM G r) τ (𝓝 1))
  {Z : ChangeAt G} {D0 : TagAt G (fun _ : Fin 1 => h) I h} {F0 : ReadAt G d (fun _ : Fin 1 => h) I}
  {packet : PacketAt G d I h}
  {K : Set (Points n)} (hK : IsCompact K) (hx : K ⊆ conf n)
  {R v L : ℝ}

lemma crop_cost {I : Type} {F : I → PowerSeries ℂ} (k j : ℕ) (C : I → ℝ)
    (hc : ∀ i, |C i| ≤ 1) (h : ∀ k, ∃ D : ℝ, ∀ i, ‖coeff k (F i)‖ ≤ D) (hj : k ≤ j) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ i, ‖crop j (C i) (F i)-crop k (C i) (F i)‖ ≤ D*|C i|^(k+1) := by
  induction j,hj using Nat.le_induction with
  | base => exact ⟨0,le_rfl,fun _ => by rw [sub_self,norm_zero,zero_mul]⟩
  | succ q hq ih =>
    obtain ⟨D,hD,hK⟩:= ih; obtain ⟨D',hz⟩:= h (q+1)
    refine ⟨D+max 1 D',add_nonneg hD (zero_le_one.trans (le_max_left ..)),fun i => ?_⟩
    let u := C i; let x:=crop q u (F i)-crop k u (F i); let w:= (u:ℂ)^(q+1)*coeff (q+1) (F i)
    rw [show crop (q+1) (C i) (F i)-crop k (C i) (F i)=x+w from (by
      unfold x w u; simp only [crop_eq]; conv_lhs => lhs; rw [Finset.sum_range_succ]
      abel)]
    apply le_trans (norm_add_le ..); rw [add_mul]; refine add_le_add (hK i) ?_
    unfold w u; rw [norm_mul, norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_comm]
    exact mul_le_mul ((hz i).trans (le_max_right ..)) (pow_le_pow_of_le_one (abs_nonneg (C i))
      (hc i) (by omega)) (pow_nonneg (abs_nonneg (C i)) (q+1)) (zero_le_one.trans (le_max_left ..))

include H hK hx
lemma previous_fee (q p : ℕ) (hq : q ≤ p) (h : ℕ) (L : ℝ) (d : Fin n → ℕ) : ∃ D : ℝ, 0≤D ∧
    ∀ t : ℝ, |t|≤1 → ∀ u : Inputs G d, Within L u → ∀ x ∈ K,
      Ball (D*|t|^(q+1)) (cActual N x u h p t - cActual N x u h q t) := by
  let I := ↥K × {v : Inputs G d // Within L v} × {i : ℝ // |i| ≤ 1}
  let x (i : I) := i.1; let v (i : I) := i.2.1.val; let t (i : I) := i.2.2.val
  let F b i := seriesComponent N (x i).val (v i) b
  choose D hD he using fun b : Toon G h => crop_cost (F:=F (flash b)) q p t (fun i => i.2.2.property)
    (fun k => price_components H hK hx v x k (L:=L) (fun i => i.2.1.property) (flash b)) hq
  obtain ⟨E,hE⟩ := Finite.bddAbove_range D
  refine ⟨max 0 E,le_max_left ..,?_⟩; intro T ht u hu X hx b
  let i : I := (⟨X,hx⟩,⟨u,hu⟩,⟨T,ht⟩)
  rw [map_sub,coord_actual,coord_actual]
  exact (he b i).trans (mul_le_mul_of_nonneg_right ((hE (mem_range_self b)).trans (le_max_right ..)) (pow_nonneg (abs_nonneg (t i)) _))

omit H hK hx in
include simple hc hC in
/-- Admissible pick of T depending on r. -/
lemma freeze : ∀ᶠ r in τ, let w : Window := (r,log (c * g r^(-B)))
    w ∈ band G c C B := by
  filter_upwards [positive_g simple] with r hr w
  have hx : 0 < g r^(-B) := by positivity
  have hf : w.Stretch=c*g r^(-B) := exp_log (mul_pos hc hx)
  refine ⟨show w.Stretch ≤ C*g r^(-B) from hf.le.trans (mul_le_mul_of_nonneg_right hC hx.le), hf.ge⟩

include ht hb hc hC
variable (hp : Stretch.Deep p P B h h η) (hη : 0<η) (hP : q+1 ≤ P) (hq : q ≤ p)
include hp hη hP hq
theorem deleted (hd : ∀ᶠ (w : Window) in windows (band G c C B),
      ∀ i (b : Toon G h), ∃ δ : Sec G h →ₗ[ℂ] ℂ, DCoat Z D0 w i RootG (probe b) = δ)
    (frame : ReplacementAt N M h Z (upper G C B) t p)
    (full : RoundedAt N F0 (upper G C B) K {RootG} t p)
    (hsingle : RoundedAt N D0 (upper G C B) {0} {RootG} t p)
    (spatial : Spatial Z F0 D0 packet (upper G C B) v L R K {RootG})
    (hs : ∀ b : Toon G h, Within R (probe b)) (hv : 0 ≤ v) (hbgt : Stretch.Stiff B P η v) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in τ, ∀ i x, x∈K →
      ∀ u : Inputs G d, Within L u →
        Ball (C*t r^(q+1)) (packet r i x u - cActual N x u h q (t r)) := by
  obtain ⟨D,hD,hd⟩ := Margin.behind H t hb hc hC ht hp hη hK hx hd frame full hsingle spatial hs hv hbgt
  obtain ⟨E,he,hf⟩ := previous_fee H hK hx q p hq h L d
  -- even bring to thermometer scale.
  refine ⟨D*2^(q+1)+E, add_pos_of_pos_of_nonneg (by positivity) he,?_⟩
  obtain ⟨s,hS⟩ := (windows_eventually _ _).mp hd
  have he : ∀ᶠ r in τ, 1/2 < t r / g r := ht.eventually (lt_mem_nhds (by norm_num))
  filter_upwards [has_room simple c B hc hb (exp (max s 0)),hS,he,
    freeze (simple:=simple) (B:=B) hc hC, paid_reading simple t ht,(shrink simple).eventually (gt_mem_nhds zero_lt_one)]
    with r hu hs hry hb hg ht
  let T := c*g r ^(-B)
  have hp : 0< T := mul_pos hc (Real.rpow_pos_of_pos hg.1 _)
  have hv : max s 0 ≤ Real.log T := exp_le_exp.mp (by rw [exp_log hp]; exact hu)
  have ht : g r < 1 := ht
  intro i x hx u hf' b
  let p1 := packet r i x u; let p2:= cActual N x u h p (t r); let p3 := cActual N x u h q (t r)
  have hr := hs (log T) ((le_max_left ..).trans hv) hb i x hx u hf' b
  change ‖coord b (p1-p2)‖ ≤ D*g r ^ P*(exp (log T))^(-η) at hr
  have hl := hf (t r) hg.2.2.1 u hf' x hx b
  rw [add_mul]
  change ‖coord b (p1-p3)‖ ≤ _
  rw [show p1-p3=p1-p2+(p2-p3) by abel,map_add]
  apply (norm_add_le ..).trans
  rw [abs_of_nonneg hg.2.1.le] at hl
  apply add_le_add (le_trans hr ?_) hl
  have Hs := hg.1
  calc
    _ ≤ D*g r^P*1 := mul_le_mul_of_nonneg_left (by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
        (Real.one_le_exp ((le_max_right ..).trans hv)) (show -η ≤ 0 by linarith)) (by positivity)
    _ = D*g r^P := mul_one _
    _ ≤ D*g r^(q+1) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one Hs.le ht.le hP) hD.le
    _ ≤ D*(2*t r)^(q+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg.1.le
      (show g r ≤ 2*t r from (by linarith only [(lt_div_iff₀ hg.1).mp hry])) _) hD.le
    _ = _ := by rw [mul_pow]; ring
end
end YM.FVA2.GradedFar.Continuation
