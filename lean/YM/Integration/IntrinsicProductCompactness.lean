import YM.Integration.MeasuredIntrinsicWilsonProduct

/-! Compactness of the original intrinsic terminal reports, including
all grades of all input slots on the same physical grid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.IntrinsicProductCompactness
open Function Filter MeasureTheory Extraction Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards OPE.Log
open Frontier6.Road PhysMS Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct FundedIntrinsicReadout IntrinsicPhysicalCell
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} {D : ℕ}
variable {I : Type} [Fintype I] {d : I → ℕ}

/-- The actual terminal report on every live regulated model. -/
def value (H : C.Makes) (b : ℕ) (w : ℕ × ℕ) (u : Config G (C.side w.1 w.2) → ℂ) : C.label D :=
  if h : Opened C D b w.2 ∧ b ≤ w.1 then label H h.1 h.2 u else 0

theorem value_eq (H : C.Makes) {b : ℕ} {w : ℕ × ℕ} (ho : Opened C D b w.2) (live : b≤w.1)
    (u : Config G (C.side w.1 w.2) → ℂ) : value H b w u = label H ho live u := by
  simp only [value,dif_pos (And.intro ho live)]

/-- The purchased terminal label controls the norm of the same original
canonical report, using the measured cost of their difference. -/
theorem budget (F : Spec.Final C f S) (facility : Facilities C f S)
    {b m j : ℕ} {w : ℕ × ℕ} {x : I → Cover} {v : (i : I) → C.label (d i)}
    {cap fee bound K : ℝ} {Z : Indices C d → C.label D} (hK : 0≤K)
    (normCap : ∀ N p (y : C.label D), m ≤ N → ‖y‖ ≤ K*Next.UVStress.quota C D m N p y)
    (receipt : Full F.room.cutoff b m j D x v cap fee bound w Z) :
    ∃ (_ : Opened C D b w.2) (live : b≤w.1),
      Booked C w.1 w.2 D (leaves C j d x v w.1 w.2) b live ∧
        ‖value (D:=D) F.room.cutoff b w (leaves C j d x v w.1 w.2)‖ ≤ chart C D b*bound+K*cap := by
  obtain ⟨ho,hs,hf,book,_,cost,stock,_,_⟩ := receipt
  let live := hs.trans hf.le
  let Y := leaves C j d x v w.1 w.2
  let z := ∑ u, weight v u • Z u
  let report := topReport C w.1 w.2 D F.room.cutoff b ho live Y
  let P := (C.factory D w.1 w.2).terminal
  have bank : ‖z‖ ≤ K*cap := (normCap w.1 w.2 z hf.le).trans (mul_le_mul_of_nonneg_left stock hK)
  have bill : ‖P report-z‖ ≤ chart C D b*bound := calc
    _ = ‖P (report-P.symm z)‖ := by rw [map_sub,P.apply_symm_apply]
    _ ≤ chart C D b*mCost C D w.1 w.2 b (report-P.symm z) := terminal_cost facility F.room.cutoff D w.1 w.2 b ho live _
    _ ≤ _ := mul_le_mul_of_nonneg_left cost (chart_nonneg ..)
  refine ⟨ho,live,book,?_⟩
  rw [value_eq F.room.cutoff ho live]
  change ‖P report‖ ≤ _
  calc
    _ = ‖(P report-z)+z‖ := by rw [sub_add_cancel]
    _ ≤ ‖P report-z‖+‖z‖ := norm_add_le .. 
    _ ≤ _ := add_le_add bill bank

theorem grade (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    {b m j : ℝ → ℕ} {h a c : ℝ} (hb : Height C.S trail LogV b h) (hm : Height C.S trail LogV m a)
    (hj : Height C.S trail LogV j c) (hh : 0<h) (ha : h<a) (hc : a<c)
    (v : ℝ → (i : I) → C.label (d i)) (D : ℕ) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
      ∃ A : ℝ, ∀ᶠ w in f.fuse, ∃ (_ : Opened C D (b t) w.2) (live : b t ≤ w.1),
        Booked C w.1 w.2 D (leaves C (j t) d x (v t) w.1 w.2) (b t) live ∧
        ‖value (D:=D) F.room.cutoff (b t) w (leaves C (j t) d x (v t) w.1 w.2)‖ ≤ A := by
  obtain ⟨W,r,μ,L,g,e,Z,_,fund⟩ := FundedIntrinsicProduct.basis (d:=d) F facility anchor to_log_zoom D hb hm hj hh ha hc
  filter_upwards [fund 0,hm.grows.eventually_ge_atTop (C.ref D)] with t paid hmD
  intro x hx
  obtain ⟨K,hK,normCap⟩ := Next.UVStress.quota_stop C F.room.cutoff hmD
  have whole := combine L.toPackage F.room.cutoff hmD x (v t) (g t) (e t) (Real.exp (0*LogV t)) (Z t x) (paid x hx)
  exact ⟨_,whole.mono fun w receipt => budget F facility hK normCap receipt⟩

private theorem cont {m : I → ℕ} (j : ℕ) (x : I → Cover) (v : (i : I) → C.label (m i)) (w : ℕ × ℕ) :
    Continuous (leaves C j m x v w.1 w.2) := by
  rw [show leaves C j m x v w.1 w.2 = fun U => ∏ i, C.O w.1 w.2 (v i) (location C.S j w.1 w.2 (x i)) U
    from funext fun U => Finset.prod_apply ..]
  exact continuous_finsetProd _ fun i _ => C.continuousO ..

/-- The canonical regulator outputs of the full product stay in a bounded
set of actual reference labels on the original fused tail. -/
theorem bounded (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    {b m j : ℝ → ℕ} {h a c : ℝ} (hb : Height C.S trail LogV b h) (hm : Height C.S trail LogV m a)
    (hj : Height C.S trail LogV j c) (hh : 0<h) (ha : h<a) (hc : a<c) (D : ℕ) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
      ∃ A : ℝ, ∀ᶠ w in f.fuse, ‖value (D:=D) F.room.cutoff (b t) w (field F R J v t (j t) x w)‖ ≤ A := by
  have each := eventually_all.mpr (fun g : Grades d => grade F facility anchor hb hm hj hh ha hc
      (fun t i => component F R J v g t i) D)
  filter_upwards [each] with t stocked
  intro x hx
  choose A priced using fun g : Grades d => stocked g x hx
  refine ⟨∑ g, A g,?_⟩
  filter_upwards [eventually_all.mpr priced] with w paid
  obtain ⟨ho,live,_,_⟩ := paid (fun _ => 0)
  let Y (g : Grades d) := leaves C (j t) (levels g) x (component F R J v g t) w.1 w.2
  have booked (g : Grades d) : Booked C w.1 w.2 D (Y g) (b t) live := by
    obtain ⟨_,_,book,_⟩ := paid g; exact book
  have add := IntrinsicProductLinearity.booked_sum C w.1 w.2 D (b t) F.room.cutoff ho live
    (fun _ : Grades d => (1:ℂ)) Y (fun g => cont ..) booked
  simp only [one_smul] at add
  have eq : value (D:=D) F.room.cutoff (b t) w (field F R J v t (j t) x w) =
      ∑ g, value (D:=D) F.room.cutoff (b t) w (Y g) := by
    simp_rw [value_eq F.room.cutoff ho live]
    unfold label
    rw [field_expansion,add.2,map_sum]
  rw [eq]
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum fun g _ => by obtain ⟨_,_,_,h⟩ := paid g; exact h

/-- One actual canonical field label survives on a nontrivial subfilter
of the same original family at the fixed physical positions. -/
theorem sublimit (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    {b m j : ℝ → ℕ} {h a c : ℝ} (hb : Height C.S trail LogV b h) (hm : Height C.S trail LogV m a)
    (hj : Height C.S trail LogV j c) (hh : 0<h) (ha : h<a) (hc : a<c) (D : ℕ) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
      ∃ (l : Filter (ℕ × ℕ)) (z : C.label D), l.NeBot ∧ l ≤ f.fuse ∧
        Tendsto (fun w => value (D:=D) F.room.cutoff (b t) w (field F R J v t (j t) x w)) l (𝓝 z) := by
  filter_upwards [bounded F facility anchor R J v hb hm hj hh ha hc D] with t bound
  intro x hx
  obtain ⟨A,paid⟩ := bound x hx
  obtain ⟨l,sub,live,z,hz⟩ := Next.UVStress.finite_extract _ A paid
  exact ⟨l,z,live,sub,hz⟩

end YM.Integration.IntrinsicProductCompactness
