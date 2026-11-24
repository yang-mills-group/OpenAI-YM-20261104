import YM.Integration.WilsonSeparatedMacroscopicReturn
import YM.Integration.WilsonMacroscopicSmearedDisplacement

/-! An original RG17.External, with the exact physical .charge and its
own measured absolute unit price. Translation to its actual offset
roster preserves a single fused comparison over all regular near cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedRegisteredExterior
open Function Filter Set MeasureTheory Lattice Extraction Table Spec OPE OPE.Orbits OPE.Cards OPE.Nesting
open Next.Rank RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Trace.Pilot Frontier6.Road SharedIntrinsicWilsonGrid IntrinsicWilsonTensor WilsonPhysicalRetainedCluster
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}
variable {I : Type} [Fintype I] {d : I→ℕ} {D:ℕ}

private theorem separated {C:Family G} {b m j:ℕ} {x:I → Cover} (plot:Plot C b m j x)
    {E:Type} [Fintype E] {y:E→E4} {η:ℝ} (ηp:0<η) (width:C.S.a (m+1)<η) (clear:ClearOf 0 y η) :
    Injective (beside (C.S.gridPoint j ∘ x) y) := by
  let near:=C.S.gridPoint j ∘ x
  have inner : Injective near := by
    intro k l eq
    by_contra ne
    have h:=plot.spaced k l ne
    change 2*C.S.a j*((C.path.levels.budget j).B:ℝ)^2<‖near k-near l‖ at h
    rw [eq,sub_self,norm_zero] at h
    exact (not_lt_of_ge (mul_nonneg (mul_nonneg (by norm_num) (C.S.a_pos _).le) (sq_nonneg _))) h
  have outer : Injective y := by
    intro k l eq
    by_contra ne
    have h:=clear.spread k l ne
    rw [eq,sub_self,norm_zero] at h
    exact ηp.not_ge h
  apply beside_distinct.mpr
  refine ⟨inner,outer,?_⟩
  intro k l eq
  have h:=clear.openSpace l
  change η≤‖(0:E4)-y l‖ at h
  change near k=y l at eq
  rw [zero_sub,norm_neg,←eq] at h
  have fit:=plot.fit k
  change 8*‖near k‖<C.S.a (m+1) at fit
  linarith only [fit,width,h,norm_nonneg (near k)]

private theorem total (F : Final R.family f V) (X : RG17.External R.family V) :
    Integrable (fun z=>‖X.test z‖*(1+‖X.pay 0 (V.unit 0) z‖)) := by
  have hT : Integrable (fun z=>X.test z) := X.test.continuous.integrable_of_hasCompactSupport X.test.hasCompactSupport
  apply (hT.norm.add (X.pay_integrable F 0 (V.unit 0)).norm).congr
  filter_upwards with z;simp only [Pi.add_apply,norm_mul,mul_add,mul_one]

private theorem current (F : Final R.family f V) (X : RG17.External R.family V) (near:I→E4) (v:Labels V d)
    (safe : ∀ z∈tsupport X.test,Injective (beside near (X.offset z))) :
    Integrable (fun z=>X.test z*whole V near v (X.offset z) X.labels) := by
  refine RG17.localized X.test _ (fun z hz=>?_)
  let loc (t:Points (X.n+1)) : Orbits.Loc I (Fin X.n) := (near,(0:E4),X.offset t)
  have hc : Continuous loc := continuous_const.prodMk (continuous_const.prodMk X.continuous_offset)
  exact (Orbits.whole_cont_at v X.labels V F.room.kernel (x:=loc z) (safe z hz)).comp (f:=loc) hc.continuousAt

def tested (Bank : Retained (d:=d) R D) (F : Final R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ→tower V) (r:ℝ) (j:ℕ)
    (x:I → Cover) (s:ℕ×ℕ) (X:RG17.External R.family V) (c:ℝ) : Prop :=
  let near := R.family.S.gridPoint j ∘ x
  ∀ v:(i:I)→Input R.family (d i),
    let response (z:Points (X.n+1)) := X.test z * whole V near (Frame.born J r v) (X.offset z) X.labels
    let reported := V.project D (basket R Bank F Q J v r x s)
    Integrable response ∧ Integrable (fun z=>X.test z*X.pay D reported z) ∧
      ‖(∫ z,response z)-X.charge F D reported‖ ≤ (c*(∏ i,‖v i‖))*WilsonMacroscopicSmearedDisplacement.price X

/-- The integrated external reading is exactly its original X.charge
on the finite retained report label. All times, cells, fields, and
regulator quantifiers are those of the original physical campaigns. -/
theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {z₀:ℝ}
    (source : FundedOriginalProperties.{u} hG z₀ W) (pace : WilsonWindowReportingPace.Slow R.kit) {H:ℕ} (hH:0<H)
    (F : Final R.family f V) (fac : Facilities R.family f V) (anchor:I) (P : Plan R.family D (Fintype.card I) (∑ i,d i)) :
    ∃ Bank : Retained (d:=d) R D, ∀ (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→tower V), Leading F J → ∀ A : (Bel R.family.book).Hierarchy,
    (∀ m:ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) m) → ∀ X:RG17.External R.family V,
    ∀ σ:ℝ,σ<1/32 → ∀ g:ℝ→ℝ,Coupling G g → ∀ k:ℕ,∀ ε:ℝ,0<ε →
    ∀ᶠ r in trail,∀ L:Set (I → Cover),L.Finite →
      (∀ x∈L,Plot R.family (P.b r) (P.middle r) (P.j r) x) → ∀ᶠ s in f.fuse,∀ x∈L,
        tested Bank F Q J r (P.j r) x s X (ε*g r^k*r^D*r^σ) := by
  obtain ⟨Bank,buy⟩ := WilsonSeparatedMacroscopicReturn.original hG W source pace hH F fac anchor P
  refine ⟨Bank,?_⟩
  intro Q J lead A obey X σ cap g hg k ε εp
  obtain ⟨η,ηp,clear⟩ := X.range_open
  have small : Tendsto (fun r=>R.family.S.a (P.middle r+1)) trail (𝓝 0) :=
    R.family.S.shrinks.comp ((tendsto_add_atTop_nat 1).comp P.mid.grows)
  filter_upwards [buy Q J lead A obey (Fin X.n) X.degree X.labels η ηp σ cap g hg k ε εp,
    small.eventually (gt_mem_nhds ηp)] with r wholePrice width L finite placed
  filter_upwards [wholePrice L finite placed] with s paid x hx
  let near := R.family.S.gridPoint (P.j r) ∘ x
  have safe (z) (hz : z∈tsupport X.test) : Injective (beside near (X.offset z)) := separated (placed _ hx) ηp width (clear z hz)
  intro v
  let ins:=Frame.born J r v
  let reported:=V.project D (basket R Bank F Q J v r x s)
  let c:=ε*g r^k*r^D*r^σ*(∏ i,‖v i‖)
  have hi := current F X near ins safe
  have hj := X.pay_integrable F D reported
  refine ⟨hi,hj,?_⟩
  change ‖(∫ z,X.test z*whole V near ins (X.offset z) X.labels)-(∫ z,X.test z*X.pay D reported z)‖≤c*_
  rw [←integral_sub hi hj]
  have point : ∀ z:Points (X.n+1),‖X.test z*whole V near ins (X.offset z) X.labels-X.test z*X.pay D reported z‖ ≤
      (‖X.test z‖*(1+‖X.pay 0 (V.unit 0) z‖))*c := by
    intro z
    by_cases hz:z∈tsupport X.test
    · have row:=paid x hx (X.offset z) (clear z hz) (safe z hz) none (Or.inl rfl) v
      rw [←mul_sub,norm_mul]
      exact (mul_le_mul_of_nonneg_left row (norm_nonneg (X.test z))).trans_eq
        (by simp only [c,WilsonSeparatedMacroscopicProbe.bill,RG17.External.pay,spectator,Option.elim_none];ring)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  exact (norm_integral_le_of_norm_le ((total F X).mul_const c) (Eventually.of_forall point)).trans_eq
    (by rw [integral_mul_const];change WilsonMacroscopicSmearedDisplacement.price X*c=_;ring)

end YM.Integration.WilsonSeparatedRegisteredExterior
