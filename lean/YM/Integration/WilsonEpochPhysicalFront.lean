import YM.Integration.WilsonEpochMeshTransport

/-! The original position scheme's genuine joint ultraviolet/infinite-volume
filter, realized on the given physical Run above any previously selected
per-cutoff period floor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochPhysicalFront
open Filter Set Function Lattice XSpace XSpace.Cirrus XSpace.Structure1 XSpace.Normalize
open FVA2 FVA2.Register FVA2.Arrival FVA2.Scale MS MS.Land
open WilsonEpochMeshTransport
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)

def entrance (lo : ℕ → ℕ) (c : ℕ) : ℕ :=
  max (lo c) ((c+1) * (R.family.S.denominator c).val ^ c)
def stock (lo : ℕ → ℕ) : Filter (ℕ × ℕ) :=
  comap Prod.fst atTop ⊓ principal {q | entrance R lo q.1 ≤ q.2}

theorem length (lo : ℕ → ℕ) (c per k : ℕ) (hk : k ≤ c) (h : entrance R lo c ≤ per) :
    (c : ℝ) ≤ (mesh R c per).spacing^k * Expense.sides id (mesh R c per) := by
  let u := (R.family.S.denominator c).val
  have hu : 0 < u := (R.family.S.denominator c).property
  have hg : c * u^k ≤ (R.family.side c per).val := calc
    c * u^k ≤ (c+1) * u^c := Nat.mul_le_mul c.le_succ (Nat.pow_le_pow_right hu hk)
    _ ≤ per := (le_max_right _ _).trans h
    _ ≤ (R.family.S.period per).val := R.family.S.period_strict.id_le per
    _ ≤ (R.family.side c per).val := Nat.le_mul_of_pos_right _ hu
  change (c : ℝ) ≤ ((u : ℝ)⁻¹)^k * (R.family.side c per).val
  rw [inv_pow,←div_eq_inv_mul,le_div_iff₀ (pow_pos (by exact_mod_cast hu) _)]
  exact_mod_cast hg

/-- All sequences obeying the funded lower floor are covered at once; the
period may still be enlarged after the signed directions are chosen. -/
theorem realized (lo : ℕ → ℕ) :
    Tendsto (fun q : ℕ × ℕ => mesh R q.1 q.2) (stock R lo) Cirrus.Front := by
  have hc : Tendsto (Prod.fst : ℕ × ℕ → ℕ) (stock R lo) atTop :=
    tendsto_iff_comap.mpr inf_le_left
  have hp : ∀ᶠ q in stock R lo, entrance R lo q.1 ≤ q.2 :=
    (show ∀ᶠ q : ℕ × ℕ in principal {z | entrance R lo z.1 ≤ z.2},
      entrance R lo q.1 ≤ q.2 from eventually_principal.mpr fun _ h => h).filter_mono inf_le_right
  apply Cirrus.goesFront
  refine ⟨R.family.S.shrinks.comp hc,?_⟩
  intro k
  refine tendsto_atTop_mono' (stock R lo) ?_ (tendsto_natCast_atTop_atTop.comp hc)
  filter_upwards [hc.eventually (eventually_ge_atTop k),hp] with q hq hd
  exact length R lo q.1 q.2 k hq hd

theorem invoice (lo : ℕ → ℕ) {P : Mesh → Prop} (paid : ∀ᶠ m in Cirrus.Front, P m) :
    ∀ᶠ c : ℕ in atTop, ∀ per ≥ entrance R lo c, P (mesh R c per) := by
  have h := (realized R lo).eventually paid
  rw [stock,eventually_inf_principal,eventually_comap] at h
  filter_upwards [h] with c hc per hp
  exact hc (c,per) rfl hp

/-- The authentic separately fixed MS matching result at *all* these
physical meshes, for the specified criterion and the original normalized
finite phase, with every test and its own budget inside the cutoff. -/
theorem historical {hG : G.Simple} (N : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match N hG T S dial)
    (lo : ℕ → ℕ) (ν : ℝ) (n d k : ℕ) (p : Tags G d n) (K : Set (Points n))
    (hK : IsCompact K) (hsep : K ⊆ conf n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c : ℕ in atTop, ∀ per ≥ entrance R lo c,
      ∀ a : Test n, tsupport a ⊆ K → ∀ b : ℝ, TestBudget.Bound a b →
        ‖Scale.System.positions N.scheme N.criterion d (mesh R c per) k n a p -
          Scale.System.Readout N.scheme N.criterion T ν d k n a p‖ ≤
            b*C*(R.family.S.a c)^MS.Tide.mildG := by
  obtain ⟨C,hC,he⟩ := M.uniformTest ν n d k p K hK hsep
  exact ⟨C,hC,invoice R lo he⟩

end YM.Integration.WilsonEpochPhysicalFront
end
