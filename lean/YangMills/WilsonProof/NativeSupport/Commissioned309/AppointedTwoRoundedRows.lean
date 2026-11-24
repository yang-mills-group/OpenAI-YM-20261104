import YM.GradedFar.Physical.Output

namespace YM.FVA2.GradedFar.Physical.AppointedTwoRoundedRows
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

variable {U J Q N M t} {K : Set (Points n)} {S : Set (Points m)}
variable (ht : Tendsto (fun r => t r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
    (old : OldCost U J Q) (frame : Scaled N M J t)
    (hK : IsCompact K) (hx : K ⊆ conf n) (L : ℝ)
include H ht hK hx

omit hK hx in
theorem kernelFromEmptyExterior (d : Fin n → ℕ) (p : ℕ)
    (empty : RoundedAt N (Y0 U J d (fun _ : Fin 0 => 0))
      (upper G 1 1) K {0} t p) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View U, ∀ x∈K, ∀ u : Inputs G d, Within L u →
      ‖alone U J i r x u - crop p (t r) (Wave.value N M x u)‖ ≤ D * t r^(p+1) := by
  refine Wave.translate H t ht p L ?_ empty
  · filter_upwards with r i s x hx u
    exact alone_eq U J i (r,s) x u

include old frame
/-- Now pay for M.4 *conditional* on the (G.6) physical and (G.9) comparison
for the detecting h, etc., all in the stated true roster. -/
theorem measuredFromTwoRows (hn : 0<n) (d : Fin n → ℕ) (h q : ℕ)
    (numerator : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      RoundedAt N (Y0 U J d (fun _ : Fin 1 => h)) (upper G 1 B) K {RootG} t p)
    (centered : ∀ p : ℕ, ∀ B : ℝ, 0 < B →
      RoundedAt N (Y0 U J (fun _ : Fin 1 => h) (fun _ : Fin 1 => h))
        (upper G 1 B) {(0 : Points 1)} {RootG} t p) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ i : View U, ∀ x∈K, ∀ u : Inputs G d, Within L u →
      Ball (D*t r^(q+1)) (packet U J Q d h r i x u - Wave.cropped N M x u h q (t r)) := by
  let S : Set (Points 1):={RootG}; let e:Fin 1→ℕ := fun _ => h
  have hy : S ⊆ O.Enh.Outside 1 := singleton_subset_iff.mpr ok_wall
  obtain ⟨L',hl,hw⟩ := Continuation.Margin.probes_fit G h
  obtain ⟨D,hD,hc⟩ := old _ _ hn d e h K S hK hx isCompact_singleton hy L L' 1 one_pos
  let η:ℝ := 1/2
  obtain ⟨B,hB,hb⟩ := (Continuation.Stretch.can_stiffen (q+1) (show η<1 by norm_num [η]) D).exists
  obtain ⟨p,hp,hq⟩ := ((Continuation.Stretch.can_deepen (q+1) B h h η).and (eventually_ge_atTop q)).exists
  have hv := frame h p B 1 hb one_pos
  have hf := numerator p B hb
  have hi := centered p B hb
  exact Wave.coefficient H t ht hK hx zero_lt_one le_rfl hb hp (show 0<η by norm_num[η]) le_rfl hq
    (Eventually.of_forall fun w i b => ⟨receive U J w i _ _ h,funext fun a => ((receive_leg U J ..).trans (center_same U J ..)).symm⟩)
    hv hf hi (hc B hb) hw hD hB
end
end YM.FVA2.GradedFar.Physical.AppointedTwoRoundedRows

