import YM.GradedFar.Books.Balance
import YM.OPE.Eye.Views

/-!
# Keeping hypotheses on the actual books
Here there's no assertion promising tallness on a chosen History. Fix the actual
book throughout (and use Maxwell & RG free equivalences in client). Derived facts
on exactly its prescribed fields -- see `Elected` use. This first file
works on **any** submitted orientation of these actual project fields. -/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} (N : WilsonPrescription G) {d : Fin n → ℕ} {e : Fin m → ℕ}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P)
abbrev FramesH {R : Family G} (P : Table R.book) := ℝ → (d : ℕ) → Sec G d ≃ₗ[ℂ] P.Field d
abbrev View := OPE.Viewers U × E4
variable (J : FramesH P)

/-- Continuum W (or H, depending on J) on actual `s` physical arguments. -/
def familyPoint (d : ℕ): Plans G d := fun r n x=> (P.classMoment (OPE.spectator U none)
    (fun _ : Fin n=>d) (r • x)).compLinearMap (fun _=> (J r d).toLinearMap)
-- angle candidate equivalence; notation `reshape` below.
def next (d : ℕ) : Rolled G d := fun r s=> (J (resize r s) d).trans (J r d).symm
lemma refits (d : ℕ) : refit (next J d) (familyPoint U J d) := by
    intro r s h hV n v x hx
    have he : (resize r s) • x= r • (exp s • x) := (smul_smul ..).symm
    unfold familyPoint; rw [he]; apply congrArg (P.classMoment _ _ _); funext i
    change J _ _ (v i)= J _ _ ((J _ _).symm _); exact (LinearEquiv.apply_symm_apply ..).symm
lemma hasMotion (d : ℕ) : travels (Zenith (next J d)) := by
    constructor
    · intro r; simp [next,Zenith,Moving.forwards,resize]; exact chairs_one
    intro r s t; unfold Zenith; rw [← chairs_mul]; apply congr_arg; ext1 u
    have he : resize r (s+t)= resize (resize r s) t:= by unfold resize; rw [exp_add,mul_assoc]
    have hu : J (resize r (s+t)) d u= J (resize (resize r s) t) d u:= by rw [he]
    change (J r d).symm _ = (J r d).symm (J (resize r s) d ((J (resize r s) d).symm _)); rw [LinearEquiv.apply_symm_apply]; exact congrArg _ hu

/-- These are the mixed receipts in Section. Jobs require actual `F` frame. Make operator order
on the first slot particularly explicit. Keep the `Read.prism` second field in every term. Real
map `dial` up/down with K. -/
lemma earlier_op (u v : Dframe.Toon G h) (r s : ℝ) : Books.mix (familyPoint U J h) (next J h) r s v u =
    P.classMoment (OPE.spectator U none) (fun _=> h) (r • Books.rootPoints)
      (Fin.append (fun _:Fin 1 => J (resize r s) h (Scale.Level.Dial h s (Dframe.theory u)))
        (fun _:Fin 1=> J r h (O.Read.prism (Dframe.theory v)))) := by
    apply congrArg (P.classMoment _ _ _); funext i; fin_cases i
    · change J r h ((J r h).symm _) = _; apply LinearEquiv.apply_symm_apply
    rfl

end
end YM.FVA2.GradedFar.Physical
