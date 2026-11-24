import YM.Integration.WilsonPositionProgramFixedFrame

/-! Shift a separated program from reporting-mesh units back to the submitted physical
radius. The running charge and inverse field frame both come from the selected MS match. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramDilation
open Filter Function Set Finset Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Book.Program MS.Fleet
open scoped Topology BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G)
    {g : G.Simple} {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    (μ : ℝ) {d n : ℕ} (v : Tags G d n) (k : ℕ)
local notation "charge" => GroupS.ψ Z.criterion M μ
local notation "frame" => GroupS.gaugeN Z.scheme Z.criterion M μ
local notation "U" => Measure.outlook Z.scheme Z.criterion d

def factor (s : ℝ) (a : Days n) (j : ℕ) (t : Fin n→Dframe.Toon G d) : ℂ :=
  cut (charge s) j (a none) * Dframe.each t (pulseU a (mirror (frame s d)) v)

def value (s : ℝ) (read : (Fin n→Dframe.Toon G d)→ℕ→ℂ) : ℂ :=
  ∑ a∈tally k n, ∑ j∈Iic (a none), ∑ t, factor Z (M:=M) μ v s a j t * read t j

include H in
theorem polynomial (a : Days n) (j : ℕ) (t : Fin n→Dframe.Toon G d) :
    Rhythm (fun s=>factor Z (M:=M) μ v s a j t) := by
  have law := (H.dilation μ).check
  apply Rhythm.mul
  · exact Rhythm.unit.mpr ((law.smooth.pow j) (a none))
  · change Rhythm (fun s=>∏ i,(MS.Theater.Daylight (Press.portDeck G) d).coord (t i)
      (PowerSeries.coeff (a (some i)) (mirror (frame s d)) (v i)))
    exact Rhythm.prod _ (fun i _=>law.invert d (a (some i)) (v i) _)

include H in
/-- The inverse geometric rescaling is tested on exactly the filed signed roster. -/
theorem original (x : Stage n) (s : ℝ) :
    U n (Facets.posing s x) k (Level.Dial d s ∘ v) =
      value Z (M:=M) μ v k s (fun t j=>U n x j (Dframe.fill t)) := by
  have law := (H.dilation μ).check
  have step : Facets.scaling s U=Facets.actMark (mirror (frame s d)) (Facets.couple (charge s) U) := by
    rw [←law.reads,Facets.acts,(law.paid s d).turn',Facets.acts_h]
  change Facets.scaling s U n x k v = _
  rw [step]
  unfold Facets.actMark
  rw [Dframe.seen]
  unfold Facets.couple
  simp only [rules,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  unfold value factor
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro j _
  rw [Dframe.stencil_he (U n x j) (pulseU a _ v),Finset.mul_sum]
  exact sum_congr rfl fun t _=>by ring

private theorem majorant (f : ℝ→ℂ) (h : Rhythm f) :
    ∃ p : ℝ[X], ∀ s, ‖f s‖ ≤ p.eval |s| := by
  obtain ⟨p,rfl⟩ := Rhythm.from_poly.mp h
  refine ⟨∑ i∈p.support,Polynomial.monomial i ‖p.coeff i‖,?_⟩
  intro s
  change ‖p.eval (s:ℂ)‖ ≤ _
  conv_lhs => rw [Polynomial.eval_eq_sum]; unfold Polynomial.sum
  refine (norm_sum_le p.support (fun i=>p.coeff i*(s:ℂ)^i)).trans_eq ?_
  simp [Polynomial.eval_finsetSum,norm_pow,Real.norm_eq_abs]

include H in
/-- One finite polynomial in the absolute logarithmic change of units prices every signed
coefficient replacement, uniformly over all compact and cutoff positions. -/
theorem paid :
    ∃ p : ℝ[X], ∀ s (A B : (Fin n→Dframe.Toon G d)→ℕ→ℂ) (E:ℝ),
      (∀ t (j:ℕ),j≤k → ‖A t j-B t j‖≤E) → 0≤E →
      ‖value Z (M:=M) μ v k s A-value Z (M:=M) μ v k s B‖ ≤ p.eval |s| * E := by
  choose p price using fun (a:Days n) (j:ℕ) (t:Fin n→Dframe.Toon G d)=>
    majorant _ (polynomial Z H μ v a j t)
  refine ⟨∑ a∈tally k n, ∑ j∈Iic (a none), ∑ t,p a j t,?_⟩
  intro s A B E h hn
  unfold value
  simp only [Polynomial.eval_finsetSum,Finset.sum_mul,←sum_sub_distrib,←mul_sub]
  refine (norm_sum_le ..).trans (sum_le_sum (fun a ha=>?_))
  refine (norm_sum_le ..).trans (sum_le_sum (fun j hj=>?_))
  refine (norm_sum_le ..).trans (sum_le_sum (fun t _=>?_))
  rw [norm_mul]
  have jk := (mem_Iic.mp hj).trans (((totaled a).mp ha) ▸ single_le_sum
    (f:=fun u=>a u) (fun _ _=>Nat.zero_le _) (mem_univ none))
  exact (mul_le_mul_of_nonneg_left (h t j jk) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (price a j t s) hn)

end YM.Integration.WilsonPositionProgramDilation
