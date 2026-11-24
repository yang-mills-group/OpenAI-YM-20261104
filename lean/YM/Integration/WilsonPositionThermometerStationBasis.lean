import YM.Integration.WilsonPositionThermometerStationReading

/-! One original station for fields whose prescribed coordinates move with the
coupling. The basis is filed before the position scheme is computed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationBasis
open Function Set Filter Table Climb Trace Trace.Pilot Next.UVStress OPE OPE.Orbits
open MergeProof.East Next.Rank PhysMS PhysMS.Frame
open WilsonPositionThermometerOrientedStation WilsonPositionThermometerStationReading
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {Y : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy}
    {d : ℕ} {I W : Type} [Fintype I] (b : Module.Basis I ℂ ((Bel C.book).Field d))

def render (A : Filing C d I) (w : (Bel C.book).Field d) : (Bel C.book).Field d :=
  ∑ i, (b.repr w i) • A.vector i

def onBasis (A : Filing C d I) (w : W → (Bel C.book).Field d) : Filing C d W :=
  ⟨A.horizon,A.level,A.grade,A.station,A.lift,fun i => render b A (w i)⟩

private theorem projection (A : Filing C d I) (P : tower S) (m : ℕ) (r : ℝ)
    (paid : Filed (f:=f) (Y:=Y) H b r P m A) (w : W → (Bel C.book).Field d) (i : W) :
    P d (w i) = S.project d (along (onBasis b A w) (onBasis b A w).lift i) := by
  obtain ⟨k,j,h,V,L,u⟩ := A
  subst d
  change P j (w i)=S.project j (L j (∑ t, b.repr (w i) t • u t))
  rw [← b.sum_repr (w i)] at ⊢
  simp only [map_sum,map_smul]
  simp_rw [← (show ∀ t, P j (b t)=S.project j (L j (u t)) from fun t => (paid.2.2.2.2 t).1)]
  simp

variable (P Q : ℝ → tower S) (A : ℝ → Filing C d I)
variable (paid : ∀ m : ℕ, ∀ᶠ r in trail, Filed (f:=f) (Y:=Y) H b r (P r) m (A r))

include paid in
theorem converges (w : ℝ → (Bel C.book).Field d) (t : (Bel C.book).Field d) (ht : Tendsto w trail (𝓝 t)) :
    Tendsto (fun r => render b (A r) (w r)) trail (𝓝 t) := by
  have e (i : I) : Tendsto (fun r => (A r).vector i) trail (𝓝 (b i)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    obtain ⟨m,hm⟩ := (cost_clears.eventually (gt_mem_nhds he)).exists
    filter_upwards [paid m] with r h
    rw [dist_eq_norm]
    exact ((h.2.2.2.2 i).2).trans_lt hm
  have rate := tendsto_finsetSum Finset.univ (fun i _ =>
    ((((b.coord i).continuous_of_finiteDimensional).tendsto _).comp ht).smul (e i))
  rw [show (∑ i, b.coord i t • b i) = t from b.sum_repr t] at rate
  exact rate

include paid in
theorem moving [Finite W] (w : ℝ → W → (Bel C.book).Field d) (u : W → (Bel C.book).Field d)
    (t : ∀ i, Tendsto (fun r => w r i) trail (𝓝 (u i)))
    (project : ∀ᶠ r in trail, ∀ i, Q r d (u i)=P r d (w r i))
    (m : ℕ) :
    ∀ᶠ r in trail, Filed (f:=f) (Y:=Y) H u r (Q r) m (onBasis b (A r) (w r)) := by
  have close (i : W) := Metric.tendsto_nhds.mp (converges b P A paid (fun r => w r i) (u i) (t i))
    _ (cost_pos m)
  filter_upwards [paid m,project,eventually_all.mpr close] with r h hl hc
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,fun i=>⟨(hl i).trans (projection b (A r) (P r) m r h (w r) i),?_⟩⟩
  exact (dist_eq_norm _ _).symm.trans_le (hc i).le

end YM.Integration.WilsonPositionThermometerStationBasis
end
