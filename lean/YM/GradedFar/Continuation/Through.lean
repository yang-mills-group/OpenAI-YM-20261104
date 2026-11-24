import YM.GradedFar.Continuation.First
import YM.GradedFar.Continuation.Meal

/-! At the M.3 precision. -/
namespace YM.FVA2.GradedFar.Continuation
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open Window (windows)
open Stretch (till Deep Stiff)
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ} {e : Fin m → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

local notation "g" => gYM G
local notation "τ" => 𝓝[>] (0:ℝ)
abbrev TagAt (G : Gauge) {m : ℕ} (e : Fin m → ℕ) (I : Type) (h : ℕ) := ReadAt G (fun _ : Fin 1 => h) e I
/-- Packet in r-coordinates. -/
abbrev PacketAt (G : Gauge) {n : ℕ} (d : Fin n → ℕ) (I : Type) (h : ℕ) := ℝ → I → Points n → Inputs G d → Sec G h

def YCoat {I : Type} (Z : ChangeAt G) (F0 : ReadAt G d e I) (w : Window) (i : I)
    (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) := F0 w i x y u (Coat Z w v)
def DCoat {I : Type} (Z : ChangeAt G) (D0 : TagAt G e I h) (w : Window) (i : I)
    (y : Points m) (v : Inputs G e) (a : Sec G h) := YCoat Z D0 w i (0:Points 1) y (fun _ => a) v
def deltaFull {I : Type} (Z : ChangeAt G) (F0 : ReadAt G d e I) (w : Window) (i : I)
    (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (t : ℝ) (p : ℕ) :=
  YCoat Z F0 w i x y u v - crop p t (Yx N M x y u v w.sep)
def deltaTag {I : Type} (Z : ChangeAt G) (D0 : TagAt G e I h) (w : Window) (i : I)
    (y : Points m) (v : Inputs G e) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (t : ℝ) (p : ℕ) (a : Sec G h) :=
  DCoat Z D0 w i y v a - crop p t (Dx N M y v w.sep a)
/-- ℓ¹ on these functionals in dual basis (pointwise estimate on the unit ball also below). -/
def weigh (h : ℕ) (F : Sec G h → ℂ) := ∑ c : Toon G h, ‖F (theory c)‖
lemma functional_so (L : ℝ) (F : Sec G h →ₗ[ℂ] ℂ) (x : Sec G h) (hx : Ball L x) :
    ‖F x‖ ≤ L * weigh h F := by
  rw [← reconstructed x,map_sum]; unfold weigh; simp_rw [_root_.map_smul, smul_eq_mul, Finset.mul_sum]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hx i) (norm_nonneg _)

/-- The part of (G.6) (for the particular calendar and world) that is needed.
D chosen before B. -/
def Spatial {I : Type} (Z : ChangeAt G) (F0 : ReadAt G d e I) (D0 : TagAt G e I h) (packet : PacketAt G d I h)
    (Q : Set Window) (D L R : ℝ) (K : Set (Points n)) (S : Set (Points m)) : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ᶠ (w : Window) in windows Q, ∀ i x, x∈K → ∀ y ∈ S,
    ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
    ‖YCoat Z F0 w i x y u v - DCoat Z D0 w i y v (packet w.len i x u)‖ ≤
      C*g w.len^(-D)*(w.Coarse+w.Stretch⁻¹^(h+1))

variable {I : Type} (t : ℝ → ℝ) {Z : ChangeAt G} {K : Set (Points n)} {S : Set (Points m)}
  (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
  {F0 : ReadAt G d e I}
  {D0 : TagAt G e I h} {packet : PacketAt G d I h}
  {L R : ℝ} {k B P' D : ℝ} {P p : ℕ}

include H hK hx
/-- c itself uniformly in a fixed ball on compact x. -/
lemma payout (p h : ℕ) (L : ℝ) (d : Fin n → ℕ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ K, ∀ u : Inputs G d, Within L u → ∀ t : ℝ, |t| ≤ 1 →
      Ball R (cActual N x u h p t) := by
  let I := ↥K × {v : Inputs G d // Within L v}
  choose C h using fun j (b : Toon G h) => price_components (I:=I) H hK hx (fun i => i.2.val) Prod.fst j
    (L:=L) (fun i => i.2.property) (flash b)
  let V b := ∑ j ∈ Finset.range (p+1), max 0 (C j b)
  obtain ⟨M0,hM⟩ := Finite.bddAbove_range V
  refine ⟨max 1 M0,le_max_left ..,?_⟩
  intro x hk u hu t ht b
  rw [coord_actual]; simp only [crop_eq]
  apply le_trans _ (show V b ≤ max 1 M0 from le_trans (hM (mem_range_self b)) (le_max_right ..))
  refine norm_sum_le_of_le _ fun j _ => ?_
  rw [norm_mul,norm_pow,Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) ht) (h j b ((⟨x,hk⟩,⟨u,hu⟩):I))
    (norm_nonneg _) zero_le_one).trans (by rw [one_mul]; exact le_max_right ..)

include hS hy
variable (ht : Tendsto (fun r => t r/gYM G r) τ (𝓝 1)) (hk : 0<k) (hc : k ≤ P') (hb : 0<B) {η : ℝ}
include ht hk hc hb
omit H hK hx hS hy ht in
include simple in
lemma compacted
    (hp : Deep p P B (∑ j, e j) h η)
    (hF : WithinError N M F0 Z (upper G P' B) K S t p L R) :
    ∀ᶠ (w : Window) in windows (band G k P' B), ∀ i x, x∈K → ∀ y ∈ S,
    ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
      ‖deltaFull Z F0 w i x y u v N M (t w.len) p‖ ≤ till G P h η w := by
  obtain ⟨C,hC,k₀,hf⟩ := hF
  filter_upwards [Stretch.first_cost simple hk (hk.trans_le hc) hb k₀ hp hC, hf.filter_mono (narrower ..)]
    with w hx hf i x hw y hy u hu v hv
  exact (hf i x hw y hy u hu v hv).trans hx

lemma formal_band (hp : Deep p P B (∑ j, e j) h η) (hs : Stiff B P η D) (hd : 0 ≤ D) :
    ∀ᶠ (w : Window) in windows (band G k P' B), ∀ x∈K, ∀ y∈S, ∀ u : Inputs G d, Within L u →
    ∀ v : Inputs G e, Within R v →
      ‖crop p (t w.len) (Yx N M x y u v w.sep) - crop p (t w.len) (Dx N M y v w.sep
        (cActual N x u h p (t w.len)))‖ ≤ 2*till G P h η w := by
  obtain ⟨C,hC,a,hx'⟩ := bound_log d e H hK hx hS hy L R p h
  filter_upwards [Stretch.residual_cost simple hk (hk.trans_le hc) hb hd hs hp a hC,
    (Window.windows_separation _).eventually hx', (Window.windows_short _).eventually (paid_reading simple t ht)]
    with w hx hw hp' x px y py u hu v hv
  exact (hw u hu v hv x px y py _ _ hp'.2.2.1 hp'.2.2.2).trans hx

/-- From all inputs of the two worlds, strong bounds below; even an evaluated
norm price on every energy in the unit ball (along with the ℓ¹ simple price on the
linear forms). `tcal` *already* set, T undeformed in every term. -/
theorem tolerance (hp : Deep p P B (∑ j, e j) h η) (hD : 0 ≤ D) (hs : Stiff B P η D)
    (frame : ∀ j, ReplacementAt N M (e j) Z (upper G P' B) t p)
    (full : RoundedAt N F0 (upper G P' B) K S t p) (singleton : RoundedAt N D0 (upper G P' B) {0} S t p)
    (s : Spatial Z F0 D0 packet (upper G P' B) D L R K S) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ (w : Window) in windows (band G k P' B), ∀ i x, x∈K → ∀ y ∈ S,
    ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
    let J := deltaFull Z F0 w i x y u v N M (t w.len) p
    let Q := deltaTag Z D0 w i y v N M (t w.len) p
    let Y := YCoat Z F0 w i x y u v; let H := DCoat Z D0 w i y v
    let cW := packet w.len i x u; let c := cActual N x u h p (t w.len)
    ∀ a, Ball 1 a →
      ‖J‖+‖Q a‖+weigh h Q+‖J-Q c‖+‖Y-H cW‖+‖Y-H c‖ ≤ C*till G P h η w := by
  obtain ⟨M',hM,hsp⟩ := s
  obtain ⟨D',hD',hf⟩ := payout H hK hx p h L d
  have ha : ∀ᶠ r in τ, |t r|≤2*g r := (paid_reading simple t ht).mono fun r h => h.2.2.2
  have hF := compacted (simple:=simple) t hk hc hb hp (paid_first H Z _ t _ F0 hK hx hS hy ha frame full L R)
  have hh : ({(0:Points 1)} : Set _) ⊆ conf 1 := singleton_subset_iff.mpr (fun _ _ _ => Subsingleton.elim ..)
  have hG := compacted (simple:=simple) t hk hc hb hp
    (paid_first H Z _ t _ D0 isCompact_singleton hh hS hy ha frame singleton D' R)
  refine ⟨10+Fintype.card (Toon G h),by positivity,?_⟩
  filter_upwards [hF,hG,formal_band (R:=R) (L:=L) H t hK hx hS hy ht hk hc hb hp hs hD,
    hsp.filter_mono (narrower ..), Stretch.spatial_cost simple hk (hk.trans_le hc) hb hs hM,
    (Window.windows_short _).eventually (paid_reading simple t ht)] with w F E form phys sale tally
  intro i x px y py u hu v hv J Q Y Rκ cW c a ha
  let z := till G P h η w
  have full : ‖J‖ ≤ z := F i x px y py u hu v hv
  have W : ‖Y-Rκ cW‖ ≤ 2*z := (phys i x px y py u hu v hv).trans sale
  have Htag (d₀ : Sec G h) (hd₀ : Ball D' d₀) : ‖Q d₀‖≤z := by
    obtain h := E i _ (mem_singleton (0:Points 1)) y py (fun _=>d₀) (fun _ => hd₀) v hv
    unfold Q deltaTag Dx; rw [responses_eq]; exact h
  have HE (d₀ : Sec G h) (hd₀ : Ball 1 d₀) := Htag d₀ (fun i => (hd₀ i).trans hD')
  have hφ : ‖J-Q c‖ ≤ 2*z := (norm_sub_le ..).trans ((add_le_add full (Htag c (hf _ px _ hu _ tally.2.2.1))).trans_eq (by ring))
  have hc := form x px y py u hu v hv
  have hh : ‖Y-Rκ c‖ ≤ 4*z := by
    let P':=crop p (t (Window.len w)) (Yx N M x y u v (Window.sep w))
    let Q':=crop p (t (Window.len w)) (Dx N M y v (Window.sep w) c)
    rw [show Y-Rκ c= J-Q c + (P'-Q') from (show _ = Y-P'-(Rκ c-Q')+(P'-Q') by abel)]
    exact (norm_add_le ..).trans ((add_le_add hφ hc).trans_eq (by dsimp only [z]; ring))
  let B' : ℕ := Fintype.card (Toon G h)
  have hm : weigh h Q ≤ B' * z := by
    calc
      _ ≤ ∑ _ : Toon G h,z := Finset.sum_le_sum fun b _ => HE _ (ball_basis b)
      _ = _ := by simp [B']
  have hi := HE a ha
  change _ ≤ (10+B')*z
  linarith

end
end YM.FVA2.GradedFar.Continuation
