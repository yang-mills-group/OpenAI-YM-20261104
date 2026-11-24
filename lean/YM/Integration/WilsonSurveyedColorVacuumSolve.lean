import YM.Integration.WilsonSurveyedColorVacuumRank

/-! Descending open-rank comparison for one genuine coefficient of the
funded MS integral equation. It starts above the two actual arity caps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumSolve
open Function Set Filter Finset MS Plane Koszul Heat Flux Arts Pilot Spin Arc Wire Rock Path Oceans
open Landau Alps Garment Shine Hem Mell Pearl Train Dock City
open WilsonSurveyedColorQuotient WilsonSurveyedColorSubtraction WilsonSurveyedColorVacuumJoint
open WilsonSurveyedColorVacuumComponents WilsonSurveyedColorVacuumRank
open scoped Classical BigOperators Topology
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)

theorem one {h : ℕ} {b : Bool} {t u r s : ℤ} {J L X Y : Flats G} {f g p q : Coat G}
    (left : Bob b h t r J X f p) (right : Bob b h u s L Y g q)
    (driving : Pact (ledger U J) L) (opening : Spotty (coat U f) g) :
    Pact (ledger U X) Y := by
  obtain ⟨jl,hx,_⟩ := left
  obtain ⟨jr,hy,_⟩ := right
  let M := max r.toNat s.toNat
  have start (k : ℕ) (e : M<k) : Seen U k X Y := by
    intro i
    filter_upwards [(hx i).cap,(hy i).cap] with z hX hY
    simp only [Action.atSlot]
    change allDims U (spot (k:ℤ) (X i z)) = spot (k:ℤ) (Y i z)
    have he1 : r < (k:ℤ) := by dsimp [M] at e; omega
    have he2 : s < (k:ℤ) := by dsimp [M] at e; omega
    rw [noneAbove he1 hX,noneAbove he2 hY,map_zero]
  have down (k : ℕ) (prior : Seen U ((k:ℤ)+2) X Y) : Seen U k X Y := by
    have hl := (color U).send ((rank (G:=G) k).send jl)
    have hr := (rank (G:=G) k).send jr
    apply (uniqueK hl hr ?_ (bare U opening k).symm).1
    simp only [map_add]
    exact pact_sym (common (select U driving k) (loop U hx hy _ prior))
  have reached (n : ℕ) : ∀ k : ℕ, M<k+n → Seen U k X Y := by
    induction n with
    | zero => intro k ek; exact start k (by omega)
    | succ n ih =>
      intro k ek
      apply down k
      exact_mod_cast ih (k+2) (by omega)
  intro i
  have finite : ∀ᶠ z in dotty, ∀ k ∈ Finset.range (M+1),
      (color U).film ((rank (G:=G) k).film X) i z = (rank (G:=G) k).film Y i z :=
    (eventually_all_finset _).mpr (fun k _ => reached (M+1) k (by omega) i)
  filter_upwards [finite,(hx i).cap,(hy i).cap] with z provided hX hY
  rw [WilsonSurveyedColorVacuumDrive.atSlot]
  change allDims U (X i z) = Y i z
  funext m w
  have eq (k : ℕ) : allDims U (spot (k:ℤ) (X i z)) = spot (k:ℤ) (Y i z) := by
    by_cases e : k ≤ M
    · have a := provided k (Finset.mem_range.mpr (by omega))
      simp only [Action.atSlot] at a
      exact a
    · have er : r < (k:ℤ) := by dsimp [M] at e; omega
      have es : s < (k:ℤ) := by dsimp [M] at e; omega
      rw [noneAbove er hX,noneAbove es hY,map_zero]
  have a := eq w.length
  rw [mask U] at a
  have ht := congrFun (congrFun a m) w
  simpa only [spotted (Eq.refl (w.length:ℤ))] using ht

end YM.Integration.WilsonSurveyedColorVacuumSolve
end
