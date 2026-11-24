import YM.Integration.WilsonEpochPostedComparison

/-! Position version of the finite UV source comparison. All physical labels
and positions are submitted separately; the continuous center is kept when
applying the original uniform estimate on separated compact sets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochPostedPositions
open Function Filter Set Lattice XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register MS MS.Land FormalBulk08.Flat
open WilsonEpochPhysicalFront WilsonEpochMeshTransport WilsonEpochPositionCoefficients
open WilsonEpochSubmittedReports
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : ℕ}

def point (d : ℕ) (v : Sample n) (b : List (Folio G) → PowerSeries ℝ) (k : ℕ) : Point G d n :=
  ∑ t : Fin n → Dframe.Toon G d,
    (PowerSeries.coeff k (WilsonEpochMeshTransport.position v.F t v.layout b)) • Dframe.each t

theorem pay (d : ℕ) (v : Sample n) (b : List (Folio G) → PowerSeries ℝ)
    (k : ℕ) (p : Tags G d n) :
    point d v b k p = readPoint v.F n d k v.layout p b := by
  simp only [point,readPoint,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

variable (R : PhysicalNext.Repeat.Legato.Run G)
  (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (α : G.ColorIndex)

theorem all_orders (Y : Initialize G) (c per D d : ℕ) (v : Sample n)
    (hv : v.F = mesh R c per) :
    point d v (graph R L α Y c per D) =
      live Y d v + point d v (residual R Y v.F.p.side) := by
  rw [actual_field]
  funext k
  apply MultilinearMap.ext
  intro p
  have hs : v.F.p.side = R.family.side c per := by rw [hv]; rfl
  change point d v (actual R Y (R.family.side c per)) k p =
    live Y d v k p + point d v (residual R Y v.F.p.side) k p
  rw [pay,pay,←hs]
  exact (comparison R Y v.F n d k v.layout 0 p).1

def publish {d : ℕ} (ν : ℝ) (S : Prescription (Press.portDeck G))
    (m : Mesh) (f : ℕ → Point G d n) : ℕ → Point G d n :=
  Dframe.status (Dframe.D ν S m d) (MS.Book.Program.substitute (Dframe.reset ν S m) f)

theorem posted (Y : Initialize G) (S : Prescription (Press.portDeck G)) (ν : ℝ)
    (c per D d : ℕ) (v : Sample n) (hv : v.F=mesh R c per) :
    publish ν S v.F (point d v (graph R L α Y c per D)) =
      Dframe.postedPoint ν Y S d v + publish ν S v.F (point d v (residual R Y v.F.p.side)) := by
  rw [all_orders R L α Y c per D d v hv]
  funext k
  apply MultilinearMap.ext
  intro p
  simp only [publish,Dframe.postedPoint,Dframe.orderT,map_add,Pi.add_apply,
    _root_.add_apply,Dframe.seen,Finset.sum_add_distrib]

theorem measured {hG : G.Simple} (Z : WilsonPrescription G)
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG T S dial)
    (lo : ℕ → ℕ) (ν : ℝ) (d k : ℕ) (p : Tags G d n) (K : Set (Points n))
    (hK : IsCompact K) (hs : K ⊆ conf n) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ c : ℕ in atTop, ∀ per ≥ entrance R lo c, ∀ D (v : Sample n),
      v.F=mesh R c per → welcome v → familiar v ∈ K →
      ‖publish ν S v.F (point d v (graph R L α Z.scheme c per D)) k p -
        Dframe.meteor ν T d (familiar v) k p‖ ≤
      ‖publish ν S v.F (point d v (residual R Z.scheme v.F.p.side)) k p‖ +
        C*(R.family.S.a c)^MS.Tide.mildG := by
  obtain ⟨C,hC,good⟩ := (M.exactbreg ν n d k p K hK hs).1
  refine ⟨C,hC,?_⟩
  filter_upwards [invoice R lo good] with c hc per hp D v hv hv' hk
  let f₀ := Dframe.postedPoint ν Z.scheme S d v k p
  let f₁ := Dframe.meteor ν T d (familiar v) k p
  let g := publish ν S v.F (point d v (residual R Z.scheme v.F.p.side)) k p
  have hnew : publish ν S v.F (point d v (graph R L α Z.scheme c per D)) k p = f₀ + g :=
    congrArg (fun r : ℕ → Point G d n => r k p) (posted R L α Z.scheme S ν c per D d v hv)
  have hj := hc per hp v hv hv' hk
  rw [show Speed.chip v.F = (R.family.S.a c)^MS.Tide.mildG by rw [hv]; rfl] at hj
  rw [hnew]
  change ‖f₀+g-f₁‖ ≤ ‖g‖ + _
  rw [show f₀+g-f₁=g+(f₀-f₁) by abel]
  exact (norm_add_le _ _).trans (add_le_add_right hj ‖g‖)

end YM.Integration.WilsonEpochPostedPositions
end
