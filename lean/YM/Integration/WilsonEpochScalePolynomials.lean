import YM.Integration.WilsonEpochPostedPositions
import YM.Integration.MSExteriorFiniteScales

/-! The genuine finite D/reset and the separately fixed MS point coefficient
share a regulator-independent polynomial degree in the log scale. The
estimate at finitely many reference scales is consequently sufficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochScalePolynomials
open Function Filter Set Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register FVA2.Scale MS MS.Land
open scoped Topology Classical BigOperators

theorem finite {I : Type} {f : I → ℝ → ℂ} (h : FVA2.Scale.Pace f) :
    MS.Logarithm.Ready (fun t i => f i t) := by
  obtain ⟨e,h⟩ := h
  choose P hP he using h
  let a (j : ℕ) (i : I) := (P i).coeff j
  have each (j : ℕ) : MS.Logarithm.Ready (fun t : ℝ => t^j • a j) := by
    simpa using MS.Logarithm.status ((Polynomial.X : Polynomial ℝ)^j) (a j)
  have common := MS.Logarithm.Ready.sums (Finset.range (e+1)) (fun j _ => each j)
  convert common using 1
  funext t i
  rw [he i]
  simp only [Finset.sum_apply,Pi.smul_apply]
  change (P i).eval (t:ℂ) = ∑ j ∈ Finset.range (e+1), t^j • a j i
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hP i))]
  apply Finset.sum_congr rfl
  intro j _
  simp [a,Complex.real_smul,mul_comm]

variable {G : Gauge} {hG : G.Simple} (Z : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)
    {n d : ℕ} (p : Tags G d n) (k : ℕ)

abbrev Good (n : ℕ) := {v : Sample n // familiar v ∈ conf n}

def gap (ν : ℝ) (v : Good n) : ℂ :=
  Dframe.postedPoint ν Z.scheme S d v.1 k p - Dframe.meteor ν T d (familiar v.1) k p

include M

theorem original : MS.Logarithm.Ready (gap Z (T:=T) (S:=S) p k) := by
  obtain ⟨e,he⟩ := FVA2.Scale.Known.serves Z.scheme S p (id : Sample n → Sample n) k
  have hfinite (v : Sample n) : FVA2.Scale.Price e (fun t => Dframe.postedPoint t Z.scheme S d v k p) := by
    simpa only [Reg.Point.story,PowerSeries.coeff_mk,id_eq] using he v
  have hs := M.details.toServed.toPosted.toQuoted.toContract.toMission.toSchemeV.born.1
  have hlimit (x : Points n) (hx : x ∈ conf n) :
      FVA2.Scale.Price e (fun t => Dframe.meteor t T d x k p) :=
    FVA2.Scale.Price.stride (F:=Gate x) (Eventually.of_forall hfinite)
      (fun t => Dframe.tB t Z.scheme S T hG hs k p x hx)
  apply finite (f:=fun v : Good n => fun t => gap Z (T:=T) (S:=S) p k t v)
  refine ⟨e,fun v=> ?_⟩
  have h := (hfinite v.1).add (hlimit _ v.2).neg
  simpa only [max_self,sub_eq_add_neg,gap] using h

end YM.Integration.WilsonEpochScalePolynomials
end
