import YM.GradedFar.Continuation.Margin

/-! Safe pivot at the **very** exterior in Margin. -/
namespace YM.FVA2.GradedFar.Continuation
namespace Margin
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open Window
open Stretch (till Deep Stiff)
open scoped Topology BigOperators Classical
variable {G : Gauge} {n h : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

variable {I : Type} (t : ℝ → ℝ) {c C η B : ℝ} (hb : 0<B) (hc : 0<c) (hC : c ≤ C)
  {p P : ℕ} (ht : Tendsto (fun r => t r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
local notation "g" => gYM G
local notation "b₁" => boarded simple (band G c C B)
local notation "l₀" => Window.windows (band G c C B)
local notation "τ" => 𝓝[>] (0:ℝ)

lemma probes_fit (G : Gauge) (h : ℕ) : ∃ R : ℝ, 0 < R ∧ ∀ b : Toon G h, Within R (probe b) := by
  let W (t : Toon G h × Toon G h) : ℝ := ‖coord t.1 (O.Read.prism (theory t.2))‖
  obtain ⟨R,hR⟩ := Finite.bddAbove_range W
  exact ⟨max R 1,lt_max_of_lt_right zero_lt_one,fun b i q => le_trans
    (show W (q,b) ≤ R from hR (mem_range_self _)) (le_max_left ..)⟩

include H hb hc hC ht
lemma weighted_fall (p : ℕ) (q z : Toon G h) : Tendsto (fun w : Window => toll q w *
      crop p (t w.len) (DX N M q RootG (probe z) w.sep)) l₀ (𝓝 (Read.GramP G h z q)) := by
  let X w := DX N M q RootG (probe z) w
  let L := b₁
  let T (w : Window) := t w.len
  obtain ⟨R,_hr,h⟩ := probes_fit G h
  have hY : Ledger L p q.size (fun i => X (L.s i)) := Ledger.from_charge
    (charge_center H isCompact_singleton (singleton_subset_iff.mpr ok_wall) (fun _:Unit => probe z)
      (fun _:Unit => (⟨RootG, mem_singleton _⟩ : ({RootG} : Set (Points 1)))) p (fun _ => h z) q) (fun _ => ())
  have hT : ∀ᶠ i in L.l, |T i|≤2*L.g i := ((Window.windows_short _).eventually (paid_reading simple t ht)).mono
    fun i hi => hi.2.2.2
  have hw := hY.below hT (Nat.zero_le p)
  have htoll : Bill L 0 (-(q.size:ℝ)) (toll q) := by
    refine ⟨1,zero_lt_one,0,?_⟩
    filter_upwards with i
    unfold post; rw [pow_zero,neg_neg,exp_nat_mul,toll_norm, pow_zero, one_mul,one_mul,one_mul]
    apply le_of_eq; rfl
  have hm := htoll.times hw
  rw [neg_add_cancel] at hm
  obtain ⟨D,hD,a,hm⟩ := hm
  have he : (1/2:ℝ)-B*0 < (((0+1:ℕ):ℝ))-B*0 := by norm_num
  have hz : Tendsto (fun w : Window => g w.len ^ (1/2:ℝ)) l₀ (𝓝 0) :=
    (Stretch.power_tends simple (1/2) (by norm_num)).comp (Window.windows_short _)
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (by filter_upwards with w; exact dist_nonneg) ?_ hz
  filter_upwards [hm, Stretch.trade simple hc (hc.trans_le hC) hb he a hD] with i hi hp
  rw [dist_eq_norm,← leading H q z i,← mul_sub]
  change ‖toll q i * (_ - crop 0 (T i) (X (L.s i)))‖ ≤ _ at hi
  rw [show crop 0 (T i) (X (L.s i)) = coeff 0 (X (L.s i)) from (by simp [crop])] at hi
  simp only [rpow_zero,rpow_natCast,mul_one,Nat.reduceAdd] at hp
  apply hi.trans
  simp only [post,neg_zero,zero_mul,exp_zero,mul_one]
  convert hp using 1
  · rfl
  · change D*g i.1^((0:ℕ)+1)*(1+i.2)^a = _; ring
  rfl
-- additional true error
variable {Z : ChangeAt G} {D0 : TagAt G (fun _ : Fin 1 => h) I h}
-- normalize columns (multiply T^grade), compare this very tested matrix.
def measuredAt {I : Type} (Z : ChangeAt G) (D0 : TagAt G (fun _ : Fin 1 => h) I h) (w : Window) (i : I) :
    Matrix (Toon G h) (Toon G h) ℂ := fun b a => DCoat Z D0 w i RootG (probe b) (theory a)
omit H hb hc hC ht in
def markedAt {I : Type} (Z : ChangeAt G) (D0 : TagAt G (fun _ : Fin 1 => h) I h) (w : Window) (i : I) :
    Matrix (Toon G h) (Toon G h) ℂ := fun b a => toll a w * measuredAt Z D0 w i b a

def allEyes (G : Gauge) (c C B : ℝ) (I : Type) :=
  comap (Prod.fst : Window × I → _) (Window.windows (band G c C B))

variable
    (hp : Stretch.Deep p P B h h η) (hη : 0<η) (hP : 0<P)
variable (hD : ∀ L R, WithinError N M D0 Z (upper G C B) {0} {RootG} t p L R)
include hD hp hη -- get even if P=0
/-- Along *all* the windows and eyes. -/
theorem safe (z q : Toon G h) :
    Tendsto (fun w : Window × I => markedAt Z D0 w.1 w.2 z q) (allEyes G c C B I) (𝓝 (Read.GramP G h z q)) := by
  have htwin : Tendsto (Prod.fst : Window × I → Window) (allEyes G c C B I) l₀ := tendsto_comap
  let X (w : Window × I) := toll q w.1 * crop p (t w.1.len) (DX N M q RootG (probe z) w.1.sep)
  have wx : Tendsto X (allEyes G c C B I) (𝓝 (Read.GramP G h z q)) :=
    (weighted_fall H t hb hc hC ht p q z).comp htwin
  apply tendsto_of_tendsto_of_dist wx
  obtain ⟨R,r,hR⟩ := probes_fit G h
  obtain ⟨D,d,a,hf⟩ := hD 1 R
  let Δ:= Glyph.size q
  have he : 1 - B * 0 < ((p+1:ℕ):ℝ)- B * ((h+Δ:ℕ):ℝ) := by
    have hx : B*Δ ≤ B*h := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Dframe.size_le q)) hb.le
    have hy : 0<B*η := mul_pos hb hη
    have hz : 0 ≤ (P:ℝ) := Nat.cast_nonneg _
    unfold Stretch.Deep at hp
    push_cast; linarith
  have ht0 : Tendsto (fun w : Window × I => g w.1.len) (allEyes G c C B I) (𝓝 0) := (shrink simple).comp
    ((Window.windows_short _).comp htwin)
  refine squeeze_zero' (by filter_upwards with w; exact dist_nonneg) ?_ ht0
  filter_upwards [htwin.eventually (Stretch.trade simple hc (hc.trans_le hC) hb he a d),
    htwin.eventually (hf.filter_mono (narrower ..))] with w hw hr
  have hv := hr w.2 0 (mem_singleton _) RootG (mem_singleton _) (fun _ => theory q)
    (fun i => ball_basis q) (probe z) (hR z)
  rw [dist_comm,dist_eq_norm]
  change ‖toll q w.1 * DCoat Z D0 w.1 w.2 RootG (probe z) (theory q) - X w‖ ≤ _
  unfold X; rw [← mul_sub,norm_mul,toll_norm,← DX_eq,Dx,responses_eq]
  apply (mul_le_mul_of_nonneg_left hv (show 0≤ (exp w.1.2)^q.size by positivity)).trans
  simp only [rpow_zero,rpow_one,mul_one,rpow_natCast] at hw
  simp only [Fin.sum_univ_one]
  apply le_trans _ hw
  apply le_of_eq
  dsimp only [Window.len,Window.Stretch,Window.sep]
  rw [pow_add]; unfold Δ; ring
end
end Margin
end YM.FVA2.GradedFar.Continuation
