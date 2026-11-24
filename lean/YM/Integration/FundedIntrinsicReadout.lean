import YM.Integration.IntrinsicProductLinearity

/-! The original rounded multipoint insertion and its intrinsic Wilson
report are paid on the same full sum of funded columns at every cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedIntrinsicReadout
open Function Filter Lattice Wilson RG Cells OPE OPE.Log MergeProof MergeProof.Ribbons Frontier6.Road
open MultilinearCellCapture FundedIntrinsicProduct Trace.Physical.GermGraph RG16.Literal
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {W r μ}

/-- One coefficient family simultaneously pays the bare signed cell and
the canonical report of the independently labelled product. -/
def Full (H : C.Makes) (b m j D : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (cap price bound : ℝ) (w : ℕ × ℕ) (Z : Indices C d → C.label D) : Prop :=
  ∃ (ho : Opened C D b w.2) (hs : b ≤ m) (hf : m < w.1),
    let live := hs.trans hf.le
    let source := leaves C j d x v w.1 w.2
    let label := ∑ u, weight v u • Z u
    let gap := leafGap C j D d x v w.1 w.2 label
    Booked C w.1 w.2 D source b live ∧
    topReport C w.1 w.2 D H b ho live source =
      ∑ u, weight v u • topReport C w.1 w.2 D H b ho live (leaves C j d x (basisLabels u) w.1 w.2) ∧
    mCost C D w.1 w.2 b
      (topReport C w.1 w.2 D H b ho live source - (C.factory D w.1 w.2).terminal.symm label) ≤ bound ∧
    Next.UVStress.quota C D m w.1 w.2 label ≤ cap ∧
    Interior ((center C.S w.2 live 0).chamber 0) gap ∧
    (center C.S w.2 live 0).rootTest (C.beta w.1 w.2) gap ≤ price

theorem Full.weaken {H : C.Makes} {b m j D : ℕ} {x : I → Cover} {v : (i : I) → C.label (d i)}
    {cap fee e e' : ℝ} {w : ℕ × ℕ} {Z : Indices C d → C.label D}
    (src : Full H b m j D x v cap fee e w Z) (he : e ≤ e') :
    Full H b m j D x v cap fee e' w Z := by
  obtain ⟨ho, hs, hf, hb, hrepr, hbound, hquota, hlocal, hroot⟩ := src
  exact ⟨ho, hs, hf, hb, hrepr, hbound.trans he, hquota, hlocal, hroot⟩

/-- Combine the exact funded original sheets on the original fused tail.
The upper bound for the report uses the same labels as the replicated cell. -/
theorem combine (L : Package C W r μ) (H : C.Makes) {b m j D : ℕ}
    (hm : C.ref D ≤ m) (x : I → Cover) (v : (i : I) → C.label (d i))
    (cap fee : Indices C d → ℝ) (bound : ℝ) (Z : Indices C d → (ℕ × ℕ) → C.label D)
    (stages : ∀ u : Indices C d, ∀ᶠ w in f.fuse,
      Stage L H b m j D x (basisLabels u) (cap u) (fee u) bound w (Z u w)) :
    ∀ᶠ w in f.fuse, Full H b m j D x v (∑ u, ‖weight v u‖ * cap u)
      (∑ u, ‖weight v u‖ * fee u) (∑ u, ‖weight v u‖ * bound) w (fun u => Z u w) := by
  have paid (u : Indices C d) : ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b ≤ w.1,
      m ≤ w.1 ∧ Next.UVStress.quota C D m w.1 w.2 (Z u w) ≤ cap u ∧
        Interior ((center C.S w.2 hb 0).chamber 0) (leafGap C j D d x (basisLabels u) w.1 w.2 (Z u w)) ∧
        (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2)
          (leafGap C j D d x (basisLabels u) w.1 w.2 (Z u w)) ≤ fee u :=
    (stages u).mono fun w ⟨_,hs,hf,_,_,_,hq,hi,hp⟩ => ⟨hs.trans hf.le, hf.le, hq, hi, hp⟩
  have root := profile_selected H hm (fun _ : Indices C d => x) basisLabels (weight v) cap fee Z paid
  filter_upwards [eventually_all.mpr stages, root] with w leavesPaid allPaid
  obtain ⟨ho, hs, hf, _⟩ := leavesPaid (fun _ => 0)
  let live : b ≤ w.1 := hs.trans hf.le
  let fields (u : Indices C d) := leaves C j d x (basisLabels u) w.1 w.2
  have cont (u : Indices C d) : Continuous (fields u) := by
    change Continuous (∏ i, C.O w.1 w.2 (basisLabels u i) (Cells.location C.S j w.1 w.2 (x i)))
    rw [show (∏ i, C.O w.1 w.2 (basisLabels u i) (Cells.location C.S j w.1 w.2 (x i))) =
      fun U => ∏ i, C.O w.1 w.2 (basisLabels u i) (Cells.location C.S j w.1 w.2 (x i)) U from
      funext fun U => Finset.prod_apply ..]
    exact continuous_finsetProd _ fun i _ => C.continuousO .. 
  have rows (u : Indices C d) : Booked C w.1 w.2 D (fields u) b live ∧
      mCost C D w.1 w.2 b (topReport C w.1 w.2 D H b ho live (fields u) -
        (C.factory D w.1 w.2).terminal.symm (Z u w)) ≤ bound := by
    obtain ⟨_, hs', _, _, ⟨_, _, _, _, path, _⟩, hreport, _⟩ := leavesPaid u
    exact ⟨(path b le_rfl hs').2.2.1, hreport⟩
  have report := IntrinsicProductLinearity.booked_sum C w.1 w.2 D b H ho live
    (weight v) fields cont (fun u => (rows u).1)
  have bill := IntrinsicProductLinearity.report_gap C w.1 w.2 D b H ho live
    (weight v) fields (fun u => Z u w) (fun _ => bound) cont (fun u => (rows u).1)
    (fun u => (rows u).2)
  obtain ⟨_, _, hq, hlocal, hprice⟩ := allPaid
  refine ⟨ho, hs, hf, ?_, ?_, ?_, hq, ?_, ?_⟩
  · rw [leaves_expansion j w.1 w.2 x v]; exact report.1
  · rw [leaves_expansion j w.1 w.2 x v]; exact report.2
  · rw [leaves_expansion j w.1 w.2 x v]; exact bill
  · rwa [leafGap, leaves_expansion j w.1 w.2 x v]
  · rwa [leafGap, leaves_expansion j w.1 w.2 x v]

/-- The same funded physical counterterm has the signed engineering
remainder and all exponential accuracies for the complete intrinsic report. -/
theorem engineering {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (v : α → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE l T (fun t => v t i k) (-(d i : ℝ))) :
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height C.S l T b h ∧ Height C.S l T m a ∧
      Height C.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ cap fee : α → ℝ, ∃ Z : α → (I → Cover) → Indices C d → (ℕ × ℕ) → C.label D,
        RateLE l T fee (-(D:ℝ)-1/32) ∧ ∀ q : ℝ, ∀ᶠ t in l,
          ∀ (x : I → Cover), Plot C (b t) (m t) (j t) x → ∀ᶠ w in f.fuse,
            Full F.room.cutoff (b t) (m t) (j t) D x (v t) (cap t) (fee t) (Real.exp (q*T t))
              w (fun u => Z t x u w) := by
  obtain ⟨h, a, c, hh, ha, h₁, hc, hmargin⟩ :=
    engineering_margin D (∑ i, d i) (Fintype.card I)
  obtain ⟨b, hb⟩ := found hT C.path.levels.fits.mesh hh.le
  obtain ⟨m, hm⟩ := found hT C.path.levels.fits.mesh (hh.trans ha).le
  obtain ⟨j, hj⟩ := found hT C.path.levels.fits.mesh (zero_lt_one.trans hc).le
  obtain ⟨W, r, μ, L, g, e, Z, hr, stage⟩ :=
    FundedIntrinsicProduct.basis (d:=d) F facility anchor hT D hb hm hj hh ha (h₁.trans hc)
  refine ⟨b, m, j, h, a, c, hb, hm, hj, hh, ha, h₁, hc,
    (fun t => ∑ u, ‖weight (v t) u‖ * g t u), (fun t => ∑ u, ‖weight (v t) u‖ * e t u),
    Z, ?_, ?_⟩
  · apply (weighted_rate hT v e (fun i => -(d i : ℝ)) _ hv (fun u => (hr u).2)).mono
    push_cast at hmargin ⊢
    rw [Finset.sum_neg_distrib]
    linarith only [hmargin]
  · intro q
    let ρ := ∑ i, -(d i : ℝ)
    let s := q-ρ-1
    have wallet := weighted_rate hT v (fun t _ => Real.exp (s*T t)) (fun i => -(d i : ℝ))
      s hv (fun _ => (RateIs.exp s hT).pays hT)
    have hr' : ρ + s < q := by dsimp only [s]; linarith
    filter_upwards [hm.grows.eventually_ge_atTop (C.ref D), stage s, wallet q hr'] with t hstock rows cash
    intro x hx
    exact (combine L.toPackage F.room.cutoff hstock x (v t) (g t) (e t) _ (Z t x) (rows x hx)).mono
      fun _ hfull => hfull.weaken ((le_abs_self _).trans cash)

end YM.Integration.FundedIntrinsicReadout
