import YM.Integration.WilsonOriginalObservedRoseGround

/-! Choose the independently renormalized ground at the measuring length before the physical cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseGroundMenu

open Filter Function Lattice Wilson Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 XSpace.Rose XSpace.Photo XSpace.Retirement XSpace.Graph3
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerFiniteTangent (credit cost roster)
open WilsonMaxwellThermometerOriginal (lower)
open scoped Topology Classical

variable {G : Gauge} (W : Initialize G) {V : Store G} (K : Pick V)
    {I : Type} [Fintype I] (basis : Module.Basis I ℂ (Sec G 6))

theorem original (simple : G.Simple) (cap δ : ℝ→ℝ) (openings : ℝ→Set Mesh)
    (bought : ∀r,openings r ∈ Front) :
    ∃ m : ℝ→Mesh, ∀r, m r∈openings r ∧ ∀ (_:0<δ r) (u:Sec G 6) (P Q:Module.End ℂ (Sec G 4)),
      Equivariant P → Equivariant Q → cost basis (roster u (P (lower G)) (Q (lower G))) ≤ cap r →
      ‖credit W K (m r) u (P (lower G)) (Q (lower G))‖ ≤ δ r := by
  obtain ⟨C,hC,earned⟩:=WilsonOriginalObservedRoseGround.original W K basis simple
  let serves (r:ℝ) (m:Mesh) := m∈openings r ∧ ∀ (_:0<δ r) (u:Sec G 6) (P Q:Module.End ℂ (Sec G 4)),
    Equivariant P → Equivariant Q → cost basis (roster u (P (lower G)) (Q (lower G))) ≤ cap r →
    ‖credit W K m u (P (lower G)) (Q (lower G))‖ ≤ δ r
  have menu (r:ℝ) : ∃m,serves r m := by
    by_cases h : 0<δ r
    · have shrinks : Tendsto (fun m:Mesh => C*m.spacing*cap r) Front (𝓝 0) := by
        have basic : Tendsto (fun m:Mesh => m.spacing) Front (𝓝 0) := frontier.endpt
        simpa only [mul_zero,zero_mul] using (basic.const_mul C).mul_const (cap r)
      have paid : ∀ᶠ m:Mesh in Front, m∈openings r ∧
          ∀ (_:0<δ r) (u:Sec G 6) (P Q:Module.End ℂ (Sec G 4)), Equivariant P → Equivariant Q →
            cost basis (roster u (P (lower G)) (Q (lower G))) ≤ cap r →
            ‖credit W K m u (P (lower G)) (Q (lower G))‖ ≤ δ r := by
        filter_upwards [bought r,earned,shrinks.eventually_lt_const h] with m hm fee price
        refine ⟨hm,fun _ u P Q p q cash=>(fee u P Q p q).trans ?_⟩
        exact (mul_le_mul_of_nonneg_left cash (mul_nonneg hC m.positive.le)).trans price.le
      exact paid.exists
    · have gate : ∀ᶠ m:Mesh in Front,m∈openings r := bought r
      obtain ⟨m,hm⟩:=gate.exists
      exact ⟨m,hm,fun pos=>False.elim (h pos)⟩
  choose m member using menu
  exact ⟨m,member⟩

end YM.Integration.WilsonOriginalObservedRoseGroundMenu
