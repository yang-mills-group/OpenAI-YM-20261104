import YM.GradedFar.Continuation.Through

/-!
# At the reflection margin for a detector

Keep the estimator calculations in their scopes. Choose the h-cap point test (positive
axis in the §F pin's convention for determinant proof, prism on the external label).
Same pair & branch in these formulas. We give a variation to the M.4 price argument
that works on just the stated hypotheses of this continuation: can even
expose the Maxwell leading and margin at T^heft-weighted *columns of the very measured*
matrix instead of transporting the final Gram back by `(H_r)⁻¹ H_s`. Then don't also
need the separate, uniform (in B-ranges) price proof for that operator's norm.
-/
namespace YM.FVA2.GradedFar.Continuation
namespace Margin
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Window
open scoped Topology BigOperators Classical
variable {G : Gauge} {n h k : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

def probe (b : Toon G h) : Inputs G (fun _ : Fin 1 => h) := fun _ => O.Read.prism (theory b)

def toll (u : Toon G h) (w : Window) := (↑(w.Stretch^u.size):ℂ)

/-- Column engineering weight, not applied to the entire test. -/
lemma toll_power (u : Toon G h) (w : Window) : toll u w = Extent.token (-w.sep) u.size := by
  rw [Extent.token,neg_neg,toll,Complex.ofReal_pow]; rfl
@[simp] lemma toll_norm (u : Toon G h) (w : Window) : ‖toll u w‖ = w.Stretch^u.size := by
  rw [toll,Complex.norm_of_nonneg ((show 0≤w.Stretch^u.size by unfold Window.Stretch; positivity))]
include H

-- leading scale relation, on arbitrary labels
open Facets in
lemma stage0 {p : Stage n} (η : ℝ) (v : Tags G h n) : book N h _ (posing η p) 0 (Level.Dial h η ∘ v) =
    book N h _ p 0 v := by
  obtain hL := (H.dilation (Teller.logNu 1)).check
  have hp := congrArg (fun F : Way G h => F _ p 0 v) (hL.reads η h)
  change Dframe.status _ (scaling η (book N h) _ p) 0 v = MS.Book.Program.substitute _ (book N h _ p) 0 v at hp
  rwa [Dframe.Silver.status_lead, MS.Book.Program.pay0, (hL.paid _ _).zero] at hp

/-- The maxwell leading on the exterior pair, *after* K applied (degree 0), order as billed. -/
lemma leading (q z : Toon G h) (w : Window) :
    toll q w * coeff 0 (DX N M q RootG (probe z) w.sep) = Read.GramP G h z q := by
  let t := w.sep
  let V := outgoing RootG
  let S := (⟨V,ok_wall⟩ : Stage (1+1))
  let S' := Facets.posing (-t) S
  obtain hp : outgoing (squeeze (-t) RootG) ∈ conf 2 := O.Enh.lives (-t) ok_wall
  have he : (⟨outgoing (squeeze (-t) RootG),hp⟩ : Stage 2)=S' := Subtype.ext (squeeze_home (-t)).symm
  let u := fun _ : Fin 1 => theory q
  let v := probe z
  let P := Fin.append u v
  have hw := stage0 H (p:=S) (-t) P
  rw [← DX_eq, Dx_configuration H _ _ _ _ _ t le_rfl (fun i=>le_rfl) hp]
  rw [tally, Finset.finsuppAntidiag_zero, Finset.sum_singleton]
  let b := theory q
  change toll q w * _ = Maxwell.Free.bond G _ _ b.val (O.Read.prism (theory z)).val
  have hh : coeff 0 (GroupS.gaugeN N.scheme N.criterion M (Teller.logNu 1) (-t) h)=1 :=
    ((H.dilation (Teller.logNu 1)).check.paid _ _).zero
  simp_rw [Finsupp.coe_zero,Pi.zero_apply,hh]
  let D := Level.Dial (G:=G) h (-t)
  let R := book N h _ S' 0
  let C := freezeFar R (D ∘ v)
  have lit (p : Sec G h) : toll q w * C (fun _ => p) = C (fun _ => toll q w • p) := by
    have hp := C.map_smul_univ (fun _ => toll q w) (fun _ => p)
    rwa [Fin.prod_univ_one, smul_eq_mul,eq_comm] at hp
  change toll q w * Measure.outlook N.scheme N.criterion h _ ⟨_,hp⟩ 0 (Fin.append u (D ∘ v))=_
  rw [he]; change toll q w * C _ = _
  rw [lit (theory q)]
  have hu : C (fun _ => toll q w • b) = book N h _ S 0 P := by
    apply Eq.trans ?_ hw
    apply congrArg R
    funext i; fin_cases i
    · exact (toll_power q w) ▸ (Level.exact₀ (-t) q).symm
    rfl
  rw [hu,book, (H.separatedOPE (Teller.logNu 1)).wilson.wardRank h _ S]
  change Maxwell.Wick.moment G V _ = _
  unfold V outgoing RootG; rw [O.Enh.lamp,Maxwell.Free.bond_eval]
  congr 1
  ext1 j; fin_cases j <;> rfl
end
end Margin
end YM.FVA2.GradedFar.Continuation
