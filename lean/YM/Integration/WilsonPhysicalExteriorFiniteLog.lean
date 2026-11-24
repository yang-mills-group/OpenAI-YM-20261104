import YM.Integration.MSExteriorFiniteScales
import YM.FVAAlt2.Moving.Grain

/-! Before all meshes, addresses and finite bare amplitudes, the original dressed
periodic readings have uniformly bounded polynomial degree in the subtraction log.
The independent running-coupling series is kept inside the original substitution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFiniteLog
open Filter Finset MS MS.Land MS.Menus MS.Rake MS.Logarithm
open MS.Book MS.Book.Convolve RegulatorIR RegulatorIR.FVAAlt2
open YM.FVAAlt2 Labels Source Precision
open scoped BigOperators Classical

variable {X : Type}
local notation "PS" => PowerSeries ℂ

private theorem mul {f g : ℝ → X → ℂ} (hf : Ready f) (hg : Ready g) :
    Ready (fun u i => f u i*g u i) :=
  Ready.pair (LinearMap.mul ℝ (X → ℂ)) hf hg

private theorem sum {L : Type} (s : Finset L) (f : L → ℝ → X → ℂ)
    (hf : ∀ j ∈ s, Ready (f j)) : Ready (fun u i => ∑ j ∈ s, f j u i) := by
  convert Ready.sums s hf using 1
  funext u i
  simp only [Finset.sum_apply]

private theorem polynomial (P : Polynomial ℝ) (s : X→ℝ) :
    Ready (fun u i => ((P.eval (u-s i):ℝ):ℂ)) := by
  have hx : Ready (fun u : ℝ => fun _i : X => (u:ℂ)) := by
    convert MS.Logarithm.status Polynomial.X (fun _i : X => (1:ℂ)) using 1
    funext u i
    simp [Complex.real_smul]
  have hd : Ready (fun u : ℝ => fun i => (u:ℂ)-(s i:ℂ)) :=
    hx.sub (Ready.const (fun i => (s i:ℂ)))
  have hp (j : ℕ) : Ready (fun u : ℝ => fun i => ((u:ℂ)-(s i:ℂ))^j) := by
    induction j with
    | zero => simpa only [pow_zero] using (Ready.const (fun _ : X => (1:ℂ)))
    | succ j ih => simpa only [pow_succ] using mul ih hd
  have H := sum (range (P.natDegree+1)) (fun j u i => (P.coeff j:ℂ)*((u:ℂ)-(s i:ℂ))^j)
    (fun j _ => mul (Ready.const (fun _ : X => (P.coeff j:ℂ))) (hp j))
  convert H using 1
  funext u i
  rw [Polynomial.eval_eq_sum_range]
  push_cast
  rfl

private def SeriesLaw (F : ℝ → X → PS) : Prop :=
  ∀ k, Ready (fun u i => PowerSeries.coeff k (F u i))

private theorem fixed (A : X → PS) : SeriesLaw (fun _ => A) :=
  fun k => Ready.const (fun i => PowerSeries.coeff k (A i))

private theorem times {F H : ℝ → X → PS} (hf : SeriesLaw F) (hh : SeriesLaw H) :
    SeriesLaw (fun u i => F u i*H u i) := by
  intro k
  simp_rw [PowerSeries.coeff_mul]
  exact sum _ _ (fun j _ => mul (hf j.1) (hh j.2))

private theorem power {F : ℝ → X → PS} (hf : SeriesLaw F) (j : ℕ) :
    SeriesLaw (fun u i => F u i ^ j) := by
  induction j with
  | zero => simpa only [pow_zero] using fixed (fun _ : X => (1:PS))
  | succ j ih => simpa only [pow_succ] using times ih hf

private theorem product {L : Type} (s : Finset L) (F : L → ℝ → X → PS)
    (hf : ∀ a, SeriesLaw (F a)) : SeriesLaw (fun u i => ∏ a ∈ s, F a u i) := by
  induction s using Finset.induction with
  | empty => simpa only [Finset.prod_empty] using fixed (fun _ : X => (1:PS))
  | insert a s ha ih => simpa only [Finset.prod_insert ha] using times (hf a) ih

private theorem shift (P : ℕ → Program.Plan) (s : X → ℝ) :
    SeriesLaw (fun u i => Program.shift P (u-s i)) := by
  intro k
  simp only [Program.shift,PowerSeries.coeff_mk]
  by_cases hk : k=0
  · simpa only [if_pos hk] using Ready.const (fun _i : X => (0:ℂ))
  by_cases hl : k=1
  · simpa only [if_neg hk,if_pos hl] using Ready.const (fun _i : X => (1:ℂ))
  simpa only [if_neg hk,if_neg hl] using polynomial (P k).coupling s

private theorem redo (P : ℕ → Program.Plan) (s : X → ℝ) (A : X → PS) :
    SeriesLaw (fun u i => Lobby.redo P (u-s i) (A i)) := by
  intro k
  simp only [Lobby.redo,LinearMap.coe_mk,AddHom.coe_mk,PowerSeries.coeff_mk,
    Program.rules,smul_eq_mul]
  exact sum _ _ (fun j _ => mul (power (shift P s) j k)
    (Ready.const (fun i => PowerSeries.coeff j (A i))))

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {L : Labels.Frames G} {U : Source.Hol G}
variable {J : Type} [Fintype J] [LinearOrder J]

/-- The actual native periodized finite book, at every order, simultaneously for
arbitrary cutoffs and periods, offsets, test fields and signed bare coefficient arrays.
Only the *same* presold prescription and field labels are fixed. -/
theorem dated (P : Prescription B) (R : Lobby.Registry L U) (v : J → Label B)
    (s ε : X→ℝ) (A : X → Sound.Formal.Episode J L) (k : ℕ) :
    Ready (fun u i => PowerSeries.coeff k (Sound.Formal.dated P (u-s i) R v (ε i) (A i))) := by
  simp only [Sound.Formal.dated,PowerSeries.coeff_C_mul,Sound.Formal.songbook,map_sum]
  apply mul (Ready.const _)
  apply sum
  intro a _
  apply times (F:=fun u i => ∏ j, Billing.bore v P (u-s i) j (a j))
    (H:=fun u i => Lobby.redo P.team (u-s i)
      (Sound.Formal.baseV R (fun j => Lobby.owner (a j)) (A i)))
  · apply product
    intro j m
    simp only [Billing.bore,PowerSeries.coeff_mk,MS.Menus.oil]
    exact polynomial _ s
  · exact redo _ _ _

end YM.Integration.WilsonPhysicalExteriorFiniteLog
