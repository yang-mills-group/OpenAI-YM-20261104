import YM.GradedFar.Physical.Needed
/-! Consume onsets, keeping all labels, and derive M.3. -/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O.Score O.Enh
open Continuation Continuation.Window
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : WilsonPrescription G) {d : Fin n → ℕ} {e : Fin m → ℕ}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J : FramesH P) (Q : OPE.Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (t : ℝ → ℝ)
-- use w.sep and w.len public.
/-- M.3 requirement (pointwise). δQ evaluated as an ℓ¹ price on the dual in these coordinates
and all unit input values. Gaps chosen after the required geometry exponents. -/
def Tolerates (d : Fin n → ℕ) (e : Fin m → ℕ) (K : Set (Points n)) (S : Set (Points m))
    (k h p : ℕ) (c C η B L R' : ℝ) :=
    ∃ C' : ℝ, 0<C' ∧ ∀ᶠ (w : Window) in windows (band G c C B), ∀ i : View U, ∀ x∈K, ∀ y ∈ S,
      ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R' v →
      let F := Ywide U J w i x y u v; let D := Dwide U J w i y v (h:=h)
      let cW := packet U J Q d h w.len i x u; let c' := cActual N x u h p (t w.len)
      let delt := F-crop p (t w.len) (Yx N M x y u v w.sep)
      let E := fun a => D a - crop p (t w.len) (Dx N M y v w.sep a)
      ∀ a, Ball 1 a →
        ‖delt‖+‖E a‖+weigh h E+‖delt-E c'‖+‖F-D cW‖+‖F-D c'‖ ≤ C'*Continuation.Stretch.till G k h η w
variable {J Q t N M U} {K : Set (Points n)} {S : Set (Points m)}
  (ht : Tendsto (fun r => t r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
  (old : OldCost U J Q) (source : SourceCost N U J t) (frame : Scaled N M J t)
  (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
include H ht old source frame hK hx hS hy
/-- Follow M.2 to M.3 with given clock and true input choices. The finite-vertex
care already supplies this before the inverse. *Conditionally* on the precise
portions of the physical hypotheses called here (and no claims supplying them).
All sufficiently large real B, then p any sufficiently large after B, use aperture
[r units] `c*g^(-B) ≤ exp(w.sep)=T ≤ C*g^(-B)`. -/
theorem lease (hn : 0<n) (d : Fin n → ℕ) (e : Fin m → ℕ) {η c C : ℝ}
    (hη : η < 1) (hc : 0<c) (hC : c ≤ C) (h p : ℕ) (L R' : ℝ) :
    ∀ᶠ B : ℝ in atTop, ∀ᶠ j : ℕ in atTop, Tolerates N M U J Q t d e K S p h j c C η B L R' := by
  obtain ⟨D,hD,hs⟩ := old n m hn d e h K S hK hx hS hy L R' C (hc.trans_le hC)
  filter_upwards [Continuation.Stretch.can_stiffen p hη D] with B ⟨hf,hb⟩
  filter_upwards [Continuation.Stretch.can_deepen p B (∑ j, e j) h η] with j hp
  let T := ({(0:Points 1)} : Set _)
  have hT : T ⊆ conf 1 := singleton_subset_iff.mpr (fun _ _ _ => Subsingleton.elim ..)
  obtain ⟨C',hC',hq⟩ := tolerance H t hK hx hS hy ht hc hC hb hp hD hf (fun i => frame (e i) j _ _ hb (hc.trans_le hC))
    (source n m _ _ _ _ _ hK hx hS hy B C hb (hc.trans_le hC))
    (source 1 m _ _ _ T S isCompact_singleton hT hS hy B C hb (hc.trans_le hC)) (hs B hb)
  refine ⟨C',hC',?_⟩
  filter_upwards [hq] with w h i x hK y hS u hu v hv F D cW V delt E a ha
  -- transfer
  unfold E delt D F; simp_rw [center_same, full_same]
  exact h i x hK y hS u hu v hv a ha

end
end YM.FVA2.GradedFar.Physical
