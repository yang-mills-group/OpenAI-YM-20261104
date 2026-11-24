import YM.LocalTaylorR2.Reset.Recoil
import YM.LocalTaylorR2.Ingress
/-!
# Re-express also the Taylor error (before H01, trunk+exp(soft) stage)

 Tracing logs and clover emission as inserted in the actual preliminary trunk.
 K remains common, with carries separately by Tap.logarithm, not assuming
 summability of a lifted price after H01. Includes forced partner itself with
 the actual +1 reserve, together consumed by the `Local`-to-trunk adapter.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Recoil
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe
variable {G:Gauge} {n:Side} {J: Listing G n} {p:BudgetPoint} {v w y: Collection.Source G n}
    {E Y H κ μ :ℝ} {W:PathData G} {c:Clip} {σ C Λ:ℝ}
-- particularly not simplifying the hard ledger, even on regular-cost branch
abbrev rest (W:PathData G)(c:Clip)(p:BudgetPoint)(J:Listing G n)(v:Collection.Source G n)(β τ α:ℝ):= trunk W c p (shelves J W p) (branch J W c p v α) (β+α+Averaging.delta (J.read v)) (Collection.vac v τ)
variable (hv : Collection.Local J p v E κ) (hG:G.Simple)
    (hW : W.Bounds c σ C Λ) (hc: WilsonStartup.Decent c p)(hx:Geo.Width p c σ)(hn:20<n.val)
include hv hG hW hc hx hn

structure Stamped (W:PathData G)(c:Clip)(p:BudgetPoint) (J:Listing G n)(v:Collection.Source G n)(σ C Λ β τ α e w k:ℝ) : Prop where
    covers : (rest W c p J v β τ α).Lawful σ C Λ e w
    labels : Payments.Fittings (branch J W c p v α) (shelves J W p) p
    money : ∃ x y, Payments.softCost p (shelves J W p) y k ∧ Payments.hardCost p (shelves J W p) x w ∧ Payments.rooted (branch J W c p v α) x y
    density U : (rest W c p J v β τ α).eval U * Real.exp (∑' i, (branch J W c p v α).logarithm i U) = earlyValue J W c p v β τ α U

lemma stamp (β τ α:ℝ): Stamped W c p J v σ C Λ β τ α (regularNeed G p c σ C α E) κ (softNeed G p c σ C α E) := by
  let d:= Averaging.delta (J.read v)
  have hi:=hv.fittings hG hW hc hn α d
  have hw:=RG01.Vacuum.localK hv
  have hd:=Averaging.delta_bound hG hv.projects
  obtain ⟨u,hu,hb⟩:=hv.cheap
  obtain ⟨k,hk,hK⟩:=hv.expensive
  obtain ⟨he,hL⟩ := Collection.Local.quote_family hW hc hx α _ hu hb hd
  have hQ (i : ℕ) := Collection.Local.quote_soft (R:=W) (c:=c) hG α d hu hv.smooth (numbering _ i)
  -- K is the same, not differenced. addresses are definitionally equiv
  exact ⟨⟨hW,hi.regular,hi.support,hi.moves, ⟨_, fun i=> Collection.Local.quote_regular hG hW hc α d hu hv.smooth (numbering _ i), fun x=>Cost.equiv (numbering _) (he x)⟩, hw⟩,hi,⟨k,_,⟨fun i => (norm_nonneg _).trans (hQ i 1),fun x => Cost.equiv (numbering _) (hL x)⟩,⟨fun i=>(hk i).1,hK⟩, fun i U=>⟨(hk i).2 U,hQ i U⟩⟩,hv.raw_evaluator hG hW hc hx α hn β τ ⟩

variable {β τ α:ℝ} {R: Rep G n}

omit hv hG hW hc hn hx
lemma enlarge {β τ α κ' E' μ' :ℝ} (h : Stamped W c p J v σ C Λ β τ α E κ μ) (he:E≤ E')(hk:κ ≤ κ')(hw:μ≤μ'): Stamped W c p J v σ C Λ β τ α E' κ' μ' := by
  obtain ⟨x,y,hq,hk',ht⟩:=h.money
  obtain ⟨hr,hp⟩:=h.covers
  refine ⟨⟨hr,{hp with boundE:= ?_,boundK:=?_}⟩,h.labels,⟨x,y,⟨hq.1,fun x=> Cost.enlarge (hq.2 x) hw⟩,⟨hk'.1,fun x=> Cost.enlarge (hk'.2 x) hk⟩,ht⟩,h.density⟩
  · obtain ⟨b,hB,hA⟩:=hp.boundE; exact ⟨b,hB,fun x=> Cost.enlarge (hA x) he⟩
  obtain ⟨b,hB,hA⟩:=hp.boundK; exact ⟨b,hB,fun x=> Cost.enlarge (hA x) hk⟩

lemma renew (hq : Stamped W c p J v σ C Λ β τ α E κ μ) (hr: R.eval=earlyValue J W c p v β τ α) : Renew R (rest W c p J v β τ α):=by
  intro U _ he
  have he': flags p.threshold U=∅:=he
  have h i : (branch J W c p v α).logarithm i U=0:=not_ne_iff.mp fun h=>hq.labels.visits i U h (by rw [Healthy,he']; simp)
  simpa only [hr,h,tsum_zero,Real.exp_zero,mul_one] using (hq.density U).symm

structure Difference (J:Listing G n) (W:PathData G) (c:Clip) (p:BudgetPoint) (v x y: Collection.Source G n) (α:ℝ) : Prop where
    reg : (branch J W c p v α).regular - (branch J W c p x α).regular = (branch J W c p y 0).regular
    log : (branch J W c p v α).logarithm - (branch J W c p x α).logarithm = (branch J W c p y 0).logarithm
    forced : (branch J W c p v α).forced=(branch J W c p x α).forced ∧ (branch J W c p v α).forced=(branch J W c p y 0).forced
include hG hv
lemma painted (α : ℝ) (hw: Collection.Local J p w H κ) (he : v.logRead=w.logRead+y.logRead) (hk: v.hardRead=w.hardRead) (ht:v.hardRead=y.hardRead): Difference J W c p v w y α:= by
  have h : (v-w).logRead=y.logRead:=by change v.logRead-w.logRead=_; rw [he]; ring
  have hd:=CalendarStep.kineticFee hG hv hw he
  refine ⟨funext fun i=> ?_, funext fun i=> funext fun U=> ?_,hk,ht⟩
  · change archive _ W c _ _ _ _ - archive _ W c _ _ _ _=archive J W c y 0 _ (numbering _ i)
    rw [Collection.archive_sub hv.smooth hw.smooth _ α,hd]; simp only [archive,h]
  change loses J W c _ _ _ _ _ U - loses J W c _ _ _ _ _ U=loses J W c _ y 0 _ (numbering _ i) U
  rw [Collection.throws_sub hv.smooth hw.smooth,hd]; simp only [loses,h]

end YM.LocalTaylorR2.Recoil
