import YM.GradedFar.Continuation.Wave

/-! The Near-only precision of G.9 and the M.4 result, substituting the MS conversion. -/
namespace YM.FVA2.GradedFar.Continuation.Wave
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
variable {I : Type} (t : ℝ → ℝ) (ht : Tendsto (fun r => t r/gYM G r) τ (𝓝 1)) {K : Set (Points n)}
  (hK : IsCompact K) (hx : K ⊆ conf n)

include H ht
/-- Near (Far empty). This is how to obtain all-positive-order comparison at bounded
stretch (from hypotheses of the assembled estimate: below `hQ` is G.9 just on
these Near-only labels). `F` always on actual test, unperturbed moving U. -/
theorem translate (p : ℕ) (L : ℝ) {F0 : ReadAt G d (fun _ : Fin 0 => 0) I}
    {F : I → ℝ → Points n → Inputs G d → ℂ} (hF : ∀ᶠ r in τ, ∀ i s, ∀ x∈K, ∀ u,
      F i r x u= F0 (r,s) i x 0 u vacant)
    (hQ : RoundedAt N F0 (upper G 1 1) K {0} t p) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in τ, ∀ i, ∀ x∈K, ∀ u, Within L u →
      ‖F i r x u - crop p (t r) (Wave.value N M x u)‖ ≤ C * t r^(p+1) := by
  obtain ⟨C,hC,a,hq⟩ := hQ L 1
  obtain ⟨s,h⟩ := (Window.windows_eventually _ _).mp hq
  let S := max 0 s
  refine ⟨C*((1+S)^a)*2^(p+1), by unfold S; positivity,?_⟩
  filter_upwards [h,has_room simple 1 1 one_pos one_pos (exp S),hF,ht.eventually (lt_mem_nhds
    (show (1/2:ℝ)<1 by norm_num)),positive_g simple] with r hr hy hf hp hu i x hx u hU
  rw [hf i S x hx, ← only_value N M H x u S 0]
  obtain he := hr S (le_max_right ..) hy i x hx 0 (mem_singleton _) u hU vacant (fun i => i.elim0)
  apply he.trans; change C*g r^(p+1)*(1+S)^a ≤ _
  have hh : g r ≤ 2*t r := by linarith only [(lt_div_iff₀ hu).mp hp]
  calc
    _ ≤ C*(2*t r)^(p+1)*(1+S)^a := by unfold S; gcongr
    _ = _ := by ring

-- OPE result arithmetic entrance
variable {Z : ChangeAt G} {D0 : TagAt G (fun _ : Fin 1 => h) I h} {F0 : ReadAt G d (fun _ : Fin 1 => h) I}
  {packet : PacketAt G d I h}
include hK hx
/-- The target price for positions in the same field measuring frame, directly on OPE inputs.
For given q, G.6 expense v, can in particular always arrange `v+q ≪ B`, `p≫B` sufficient
and compare by p vs q as in (1695), in these hypotheses.
-/
theorem coefficient {D B C c L R η : ℝ} {P p q : ℕ} (hc : 0<c) (hC : c≤C) (hb : 0<B)
    (hp : Deep p P B h h η) (hη : 0 < η) (hP : q+1 ≤ P) (hq : q ≤ p)
    (hd : ∀ᶠ (w : Window) in windows (band G c C B),
      ∀ i (b : Toon G h), ∃ δ : Sec G h →ₗ[ℂ] ℂ, DCoat Z D0 w i RootG (probe b) = δ)
    (frame : ReplacementAt N M h Z (upper G C B) t p)
    (full : RoundedAt N F0 (upper G C B) K {RootG} t p)
    (hsingle : RoundedAt N D0 (upper G C B) {0} {RootG} t p)
    (spatial : Spatial Z F0 D0 packet (upper G C B) D L R K {RootG})
    (fit : ∀ b : Toon G h, Within R (probe b)) (hv : 0 ≤ D) (hs : Stiff B P η D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in τ, ∀ i x, x∈K → ∀ u, Within L u →
      Ball (C*t r^(q+1)) (packet r i x u - Wave.cropped N M x u h q (t r)) := by
  simp_rw [Wave.fee _ _ H]
  exact deleted H t hb hc hC ht hK hx hp hη hP hq hd frame full hsingle spatial fit hv hs
end
end YM.FVA2.GradedFar.Continuation.Wave
