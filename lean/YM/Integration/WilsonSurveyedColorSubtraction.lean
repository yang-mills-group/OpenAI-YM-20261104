import YM.Integration.WilsonSurveyedColorCoordinates
import YM.FVA2.TurningPole

/-! The color change on the complete dimensional amplitude, its dilation and
the finite part after pole subtraction. The Laurent and evanescent terms
stay in the same ledger until the punctured-regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorSubtraction
open Function Set Filter MS MS.Plane MS.Arts MS.Arts.Pilot MS.Koszul MS.Landau
open MS.Color MS.Rock MS.Rock.Path MS.Rock.Oceans MS.Hem MS.Hem.Mell
open MS.Alps MS.Shine MS.Pearl MS.Train MS.Dock MS.Emit MS.Outlook MS.Heat
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open scoped Classical BigOperators Topology
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)

def allDims : Mob G →ₗ[ℂ] Mob G where
  toFun F m := turn U (F m)
  map_add' F H := funext fun m => map_add (turn U) (F m) (H m)
  map_smul' c F := funext fun m => map_smul (turn U) c (F m)

private def scaled {m : ℕ} (a : ℂ) (t : ℝ) (F : Rack G m) : Rack G m :=
  fun l => amount (a+(mass l:ℂ)) t * F (sr t l)

private theorem first {m : ℕ} (a : ℂ) (t : ℝ) (F : Rack G m) (i : Mode (Cfield G m) (SectorP m)) :
    Koszul.D i (scaled a t F) = scaled (a+(wfield i.1:ℂ)) t
      (Koszul.D (i.1,Real.exp t • i.2) F) := by
  funext l
  change amount (a+(mass (i::l):ℂ)) t * F (sr t (i::l)) =
    amount ((a+(wfield i.1:ℂ))+(mass l:ℂ)) t * F ((i.1,Real.exp t • i.2)::sr t l)
  rw [Price_cons,Int.cast_add,add_assoc]
  rfl

private theorem commutes {m : ℕ} (a : ℂ) (t : ℝ) (F : Rack G m)
    (l : Legs (Mode (Cfield G m) (SectorP m))) : turn U (scaled a t F) l = scaled a t (turn U F) l := by
  induction l generalizing a F with
  | nil => rfl
  | cons i l ih =>
    change Koszul.D i (turn U (scaled a t F)) l = Koszul.D i (scaled a t (turn U F)) l
    rw [derivative,first]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,first]
    change _ = amount _ t * Koszul.D (i.1,Real.exp t • i.2) (turn U F) (sr t l)
    rw [derivative]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]
    exact mul_left_comm ..

theorem dilation (a : ℂ) (t : ℝ) (F : Mob G) :
    allDims U (plow a t F)=plow a t (allDims U F) :=
  funext fun m => funext fun l => commutes U a t (F m) l

abbrev coat := tapeL (fun _ : ℂ => allDims U)
abbrev ledger := blast 0 (coat U)

theorem parade (h : ℕ) (F : Flats G) (y t : ℝ) :
    coat U (Parade F h y t) = Parade (ledger U F) h y t := by
  induction F using Finsupp.induction_linear with
  | zero => rw [map_zero,pageZ,map_zero]
  | add x y hx hy => rw [map_add,page_add,page_add,map_add,hx,hy]
  | single i f =>
    rw [ledger,blast_sl,Nat.add_zero]
    ext1 z
    change allDims U _ = _
    rw [page_sl,page_sl,hikeP,hikeP,map_smul,dilation]
    rfl

theorem limit {ι : Type} {L : Filter ι} {A : ι → Mob G} {F : Mob G} (h : Wind A L F) :
    Wind (fun i => allDims U (A i)) L (allDims U F) := by
  intro m l
  have finite := (pilot (D:=Arts.L m) (P:=SectorP m) U).sense.reaches l
  change Tendsto (fun i => turn U (A i m) l) L (𝓝 (turn U (F m) l))
  simpa only [emits] using h.center m finite

theorem finitePart {h : ℕ} {F F' : Flats G} (sent : ledger U F = F')
    (left : Stay h F) (right : Stay h F') (y t : ℝ) :
    allDims U (hereZ h F y t) = hereZ h F' y t := by
  have hl := limit U (live0 (s:=y) (y:=t) left).wind
  have hr := (live0 (s:=y) (y:=t) right).wind
  apply hl.unique
  exact hr.congr (Eventually.of_forall fun z =>
    (congrFun ((parade U h F t y).trans (by rw [sent])) z).symm)

end YM.Integration.WilsonSurveyedColorSubtraction
end
