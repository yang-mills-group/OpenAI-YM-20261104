import YM.OPE.Prices.Circuit
import YM.Integration.OriginalProductCellMatch
import YM.Integration.MultilinearCellCapture

/-! Original finite Wilson matching with the scale prices of `OPE.funding`.
The tagged label and the source receipt use the very same family at every
finite cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedProductCellMatch
open OPE
open Filter Function Set Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open scoped Topology BigOperators
variable {G:Gauge}{C:Family G}{ι κ : Type*}{I:Type}[Fintype I][DecidableEq I](i₀:I){l : Filter ι} {f : Filter κ} {T : ι→ℝ} {a b c : ℝ}
variable {m k j q:ι→ℕ}
variable (hG:G.Simple){W r D} (L: Package C W r D)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "P'"=> C.path.levels.budget
local notation "Λ" => C.S.scale
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "τ" => fly C.path.levels
local notation "X" => bling C.path.levels

variable (h:C.Makes)(d:I→ℕ)(s: (i:I)→ C.label (d i))(t:ℕ)
structure SourcedPrice (L : Package C W r D)(g o : ℝ)(n : ℕ) (d : I→ℕ)(s:(i:I)→ C.label (d i))(J m j:ℕ) : Prop where
    quote (N p:ℕ)(hn:j<N)(hm:J ≤ N) : ∀ (r:I→Site (C.side j p)), (∀ i,loops C j p (r i) (m+1)=0) → Next.Rank.Edition.Spaced (C.path.levels.budget j).B r →
       let V:= Cells.center C.S p hm 0; let f (i:I):=C.O N p (s i) ((C.S.toDepth hn.le p).embed (r i)); (∀ i, Cells.Interior (V.chamber 0) (f i))→ (∀ z:C.label n, Cells.Interior (V.chamber 0) (C.O N p z 0)) →
       ∀ (stop : ℕ) (href : C.ref n ≤ stop), stop ≤ J → ∃ z:C.label n,
       let source : Config G (C.side N p) → ℂ := fun U => ∏ i, f i U
       let g' := source - C.O N p z 0
       OriginalProductCellMatch.SourceAt C N m p n J L.system stop href source g o z ∧
       Next.UVStress.quota C n m N p z ≤ g ∧ Cells.Interior (V.chamber 0) g' ∧ V.rootTest (C.beta N p) g' ≤ o
    admits : C.ref n ≤ J
    live : J≤ m
    step : C.ref n ≤ m
    goes : m+1 ≤ j
local notation "Z'"=> ((∑ x,d x:ℕ):ℝ)*c +4*(Fintype.card I:ℝ)*(c-a)
local notation "X'"=> ((t:ℝ)+1/16)*(a-b)-(Z')
-- PriceAt along scales; with geometry paid elsewhere
include i₀ h hG
/-- The funding of every separated tuple of fixed original fields retains
its served coefficient and calibrated primary, down to each chosen stop. -/
theorem grid_funding (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hj:Height C.S l T j c)(hT:Tendsto T l atTop)(he:b<a)(ht:a<c) (hΩ:∀ᶠ i in l, Push.GridApprox.room C.path.levels (k i) (m i) (lensScope C t)) :
    ∃ g o : ι→ℝ, RateIs l T g ((Z')-t*a) ∧ RateLE l T o (-(X')) ∧
       (∀ᶠ i in l,0<o i) ∧ ∀ᶠ i in l, SourcedPrice L (g i) (o i) t d s (k i) (m i) (j i):=by
    let P:= Stock.Tabs.chosen C.path.levels 1 L.tabs ∘ k; have hP:Height C.S l T P b:= hk.stock L.tabs
    have ha:∀ i,Stock.Tabs.opens C.path.levels 1 (k i) (P i):=fun i=>Stock.Tabs.opened ..
    let M:= Fintype.card I; have hM: 0 < M:= Fintype.card_pos_iff.mpr ⟨i₀⟩
    obtain ⟨y,hy,hF,hY⟩:= halls hG L.halos M hM
    obtain ⟨χ,hχ⟩:= L.productCuts.mother
    let B (i:I):= 1+(C.labels.level (d i)).coeffSize (s i); have hf i:0<B i:= add_pos_of_pos_of_nonneg one_pos (Work.G08.size_nonneg ..)
    let x i:= ManyCopies.initial C.path δ η (m i) (j i) (y (j i)) (∏ p,plumR C (d p) (B p) (j i)) M
    have hx:RateIs l T x (-(Z')):= (Height.gathered hm hj hT (height0 hy hj) (Height.plumBudget d B hf hj hT hG) hG M).swap (by unfold M; ring)
    let e i:= terminalCost C t (m i) (x i); let g i:=2*e i; let z i:= Real.exp ((X')*T i); have hZ:=RateIs.exp (X') hT; have hg:= key_cost hm hT hx hG t; have hp:= terminalAfford hG L hP hm hT he hx t hg hZ (by linarith only [he]); let o i:=2*(stakes C (k i) (P i) / z i)
    refine ⟨g, o, ((RateIs.const hT zero_lt_two).mul hg).swap (by ring),?_ , Eventually.of_forall (fun i=>mul_pos zero_lt_two (div_pos (Real.exp_pos _) (Real.exp_pos _))),?_⟩
    · simp_rw [o,div_eq_mul_inv]; simpa only [zero_add] using! ((RateLE.const (2:ℝ) hT).mul ((stock_price L.tabs hG hk hT).mul (hZ.inv.pays hT)))
    have hb:=briar C hG L.accounting; have hm':= hm.step C.path.levels.fits.mesh; let S i:= m i+1; have hW' := (((height0 hb hm').power 2).add (RateIs.const hT one_pos) hT).mul hm'.mesh
    filter_upwards [hk.mesh.overtakes (hW'.pays hT) hT (by simp; linarith),hP.earlier he hT hm, hm'.earlier ht hT hj, hp, hx.pos, hΩ, hk.grows.eventually_ge_atTop (C.ref t), eventually_all.mpr (fun x=>hj.grows.eventually_ge_atTop (C.ref (d x)))] with i hψ hPi hS hp hx hr hK hd
    have hf'(p:ℕ): ((P' (S i)).B^2+1:ℕ) ≤ (C.S.toDepth (((ha i).1.trans hPi.le).trans (Nat.le_succ (m i))) p).count.val:= by
       let v:= C.S.toDepth (((ha i).1.trans hPi.le).trans (m i|>.le_succ)) p; have hl: ((P' (S i)).B:ℝ)^2+1 ≤ v.count.val:=by
          apply le_of_mul_le_mul_right _ (C.S.a_pos (S i)); exact hψ.le.trans_eq ((C.S.embeds_scale v).symm.trans (mul_comm ..))
       exact_mod_cast hl
    refine ⟨fun N p hn hz r he hw hi₀ hi₁ stop href hstop=> ?_,hK,(ha i).1.trans hPi.le,hK.trans ((ha i).1.trans hPi.le),hS.le⟩
    -- careful let V etc introduction reflexive
    exact OriginalProductCellMatch.capture_product C N (m i) p t (k i) (P i) i₀ (z i) (fun p=> plumR C (d p) (B p) (j i)) r (ha i).1 hPi.le hn hS.le d s h L.system L.literal (hχ t) L.tabs (ha i) stop href (hstop.trans (ha i).1) hd (fun p=>paid_new C N _ _ (d p) h (s p) (B p) (hf p) (le_add_of_nonneg_left zero_le_one) (hd p) hn) (fun p=>stockpit _ _ _ _ (hf p)) hr he (hf' _) hw (hy.pos (j i)) (hF (j i)) (Or.inr (fun q₀ _ hp=> hY (j i) q₀ hp.le)) _ (fun _=>rfl) hi₀ hi₁ hx le_rfl (Real.exp_pos _)
      hp.1 le_rfl hp.2
end YM.Integration.FundedProductCellMatch

namespace YM.Integration.FundedProductCellMatch
open Function Filter Lattice Wilson RG Cells OPE OPE.Log MergeProof MergeProof.Ribbons Frontier6.Road
open MultilinearCellCapture
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {W r μ}
variable (L : Package C W r μ)

/-- A regulated choice of the same priced label retains the calibrated
coefficient of the exact independently rounded original physical product. -/
def SourcedStamp (b m j D : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (f : Extraction.Order) (stop : ℕ) (href : C.ref D ≤ stop) (cap price : ℝ) : Prop :=
  ∃ Z : (ℕ × ℕ) → C.label D, ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b ≤ w.1,
    m ≤ w.1 ∧
    OriginalProductCellMatch.SourceAt C w.1 m w.2 D b L.system stop href
      (leaves C j d x v w.1 w.2) cap price (Z w) ∧
    Next.UVStress.quota C D m w.1 w.2 (Z w) ≤ cap ∧
    Interior ((center C.S w.2 hb 0).chamber 0) (leafGap C j D d x v w.1 w.2 (Z w)) ∧
    (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2) (leafGap C j D d x v w.1 w.2 (Z w)) ≤ price

/-- The true sourced price yields the compensated product on the original
regulator tail at every admissible stop. -/
theorem on_grid (hC : C.Makes) {b m j D stop : ℕ} {cap price : ℝ}
    (x : I → Cover) (v : (i : I) → C.label (d i))
    (paid : SourcedPrice L cap price D d v b m j)
    (shape : Plot C b m j x) (href : C.ref D ≤ stop) (hs : stop ≤ b) :
    SourcedStamp L b m j D x v f stop href cap price := by
  have hN := Cards.largeMesh f
  have hp : Tendsto (@Prod.snd ℕ ℕ) f.fuse atTop := tendsto_atTop.mpr fun t => by
    rw [Extraction.Order.fused, Extraction.Order.late]
    filter_upwards [f.per.cofinal.eventually_ge_atTop t] with p ht
    exact Eventually.of_forall fun _ => ht
  let fits (w : ℕ × ℕ) (z : C.label D) := ∃ hb : b ≤ w.1,
    m ≤ w.1 ∧ OriginalProductCellMatch.SourceAt C w.1 m w.2 D b L.system stop href
      (leaves C j d x v w.1 w.2) cap price z ∧ Next.UVStress.quota C D m w.1 w.2 z ≤ cap ∧
    Interior ((center C.S w.2 hb 0).chamber 0) (leafGap C j D d x v w.1 w.2 z) ∧
    (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2) (leafGap C j D d x v w.1 w.2 z) ≤ price
  have available : ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ z, fits w z := by
    filter_upwards [hp.eventually shape.marsh, hN.eventually (near_center C b D hC),
      eventually_all.mpr (fun i => hN.eventually (near_center C b (d i) hC)),
      hN.eventually_gt_atTop j] with w scene counterFit fieldFit hj
    have hj' : j < w.1 := hj
    let hb : b ≤ w.1 := shape.first.trans (m.le_succ.trans (shape.last.trans hj'.le))
    let T := center C.S w.2 hb 0
    let y := (wrap (C.side j w.2)) ∘ x
    let field (i : I) := C.O w.1 w.2 (v i) ((C.S.toDepth hj'.le w.2).embed (y i))
    have hi (i : I) : Interior (T.chamber 0) (field i) := by
      apply fieldFit i hb w.2
      rw [C.S.embeds_place, (scene.2 i).2]
      exact (shape.fit i).le.trans (C.S.strictAnti.antitone (shape.first.trans m.le_succ))
    have hc (z : C.label D) : Interior (T.chamber 0) (C.O w.1 w.2 z 0) :=
      counterFit hb w.2 _ (by rw [latzero]; simp [(C.S.a_pos b).le]) _
    obtain ⟨z, hsource, hcost, hlocal, hbound⟩ :=
      paid.quote w.1 w.2 hj' hb y (fun i => (scene.2 i).1) scene.1 hi hc stop href hs
    have source : leaves C j d x v w.1 w.2 = (fun U => ∏ i, field i U) := by
      funext U
      simp only [leaves, field, y, comp_apply, Finset.prod_apply, Cells.location, dif_pos hj'.le]
    have eq : leafGap C j D d x v w.1 w.2 z =
        (fun U => ∏ i, field i U) - C.O w.1 w.2 z 0 := by rw [leafGap, source]
    exact ⟨z, hb, m.le_succ.trans (shape.last.trans hj'.le), source ▸ hsource, hcost,
      eq ▸ hlocal, eq ▸ hbound⟩
  let Z (w : ℕ × ℕ) : C.label D := if h : ∃ z, fits w z then h.choose else 0
  refine ⟨Z, available.mono ?_⟩
  intro w hw
  change fits w (Z w)
  simpa only [Z, dif_pos hw] using hw.choose_spec

/-- Uniform finite-coordinate source prices of one original family with the
four-dimensional placement cost and exterior stocks before the grid. -/
theorem basis_bank {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) {a h c : ℝ} {b m j : α → ℕ}
    (hb : Height C.S l T b h) (hm : Height C.S l T m a) (hj : Height C.S l T j c)
    (ha : h < a) (hc : a < c) :
    let load := ((∑ i, d i : ℕ) : ℝ) * c + 4 * (Fintype.card I : ℝ) * (c-a)
    ∃ W r μ, ∃ L : LogPackage C W r μ, ∃ gain error : α → Indices C d → ℝ,
      (∀ u, RateIs l T (fun t => gain t u) (load - D*a) ∧
        RateLE l T (fun t => error t u) (-(((D:ℝ)+1/16)*(a-h)-load))) ∧
      ∀ᶠ t in l, C.ref D ≤ b t ∧ ∀ (x : I → Cover), Plot C (b t) (m t) (j t) x →
        ∀ (stop : ℕ) (href : C.ref D ≤ stop), stop ≤ b t →
          ∀ u : Indices C d, SourcedStamp L.toPackage (b t) (m t) (j t) D x (basisLabels u)
            f stop href (gain t u) (error t u) := by
  obtain ⟨W, r, μ, L⟩ := facility.costlier
  choose g e hg he hpos hp using fun u : Indices C d =>
    grid_funding anchor facility.simpleGate L.toPackage F.room.cutoff d (basisLabels u) D
      hb hm hj hT ha hc (height_room hb hm hT ha _)
  refine ⟨W, r, μ, L, (fun t u => g u t), (fun t u => e u t), fun u => ⟨hg u, he u⟩, ?_⟩
  filter_upwards [eventually_all.mpr hp, hb.grows.eventually_ge_atTop (C.ref D)] with t ht hbase
  exact ⟨hbase, fun x hx stop href hs u =>
    on_grid L.toPackage F.room.cutoff x (basisLabels u) (ht u) hx href hs⟩
/-- One regulated set of sources for the entire raw multilinear
combination. The price uses the exact coefficient-weighted sum of those
particular labels. -/
def SourcedCombination (b m j D : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (f : Extraction.Order) (stop : ℕ) (href : C.ref D ≤ stop) (cap price : Indices C d → ℝ) : Prop :=
  ∃ Z : Indices C d → (ℕ × ℕ) → C.label D, ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b ≤ w.1,
    m ≤ w.1 ∧
    (∀ u : Indices C d,
      OriginalProductCellMatch.SourceAt C w.1 m w.2 D b L.system stop href
        (leaves C j d x (basisLabels u) w.1 w.2) (cap u) (price u) (Z u w) ∧
      Next.UVStress.quota C D m w.1 w.2 (Z u w) ≤ cap u ∧
      Interior ((center C.S w.2 hb 0).chamber 0)
        (leafGap C j D d x (basisLabels u) w.1 w.2 (Z u w)) ∧
      (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2)
        (leafGap C j D d x (basisLabels u) w.1 w.2 (Z u w)) ≤ price u) ∧
    let joint := ∑ u, weight v u • Z u w
    let gap := leafGap C j D d x v w.1 w.2 joint
    Next.UVStress.quota C D m w.1 w.2 joint ≤ ∑ u, ‖weight v u‖ * cap u ∧
      Interior ((center C.S w.2 hb 0).chamber 0) gap ∧
      (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2) gap ≤ ∑ u, ‖weight v u‖ * price u

/-- Multilinearity combines the very same basis-source columns and their
signed residuals on one original cutoff tail. -/
theorem combine {b m j D stop : ℕ} (hC : C.Makes) (hm : C.ref D ≤ m)
    (href : C.ref D ≤ stop) (x : I → Cover) (v : (i : I) → C.label (d i))
    (cap price : Indices C d → ℝ)
    (hs : ∀ u : Indices C d, SourcedStamp L b m j D x (basisLabels u) f stop href (cap u) (price u)) :
    SourcedCombination L b m j D x v f stop href cap price := by
  let Z (u : Indices C d) := (hs u).choose
  have rows (u : Indices C d) := (hs u).choose_spec
  have paid (u : Indices C d) : ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ hb : b ≤ w.1,
      m ≤ w.1 ∧ Next.UVStress.quota C D m w.1 w.2 (Z u w) ≤ cap u ∧
        Interior ((center C.S w.2 hb 0).chamber 0) (leafGap C j D d x (basisLabels u) w.1 w.2 (Z u w)) ∧
        (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2)
          (leafGap C j D d x (basisLabels u) w.1 w.2 (Z u w)) ≤ price u :=
    (rows u).mono fun _ ⟨hb, hm', _, he⟩ => ⟨hb, hm', he⟩
  have hsum := profile_selected hC hm (fun _ : Indices C d => x) basisLabels (weight v)
    cap price Z paid
  refine ⟨Z, ?_⟩
  filter_upwards [hsum, eventually_all.mpr rows] with w he hrows
  obtain ⟨hb, hm', hq, hi, hp⟩ := he
  refine ⟨hb, hm', fun u => (hrows u).choose_spec.2, hq, ?_, ?_⟩
  · rwa [leafGap, leaves_expansion j w.1 w.2 x v]
  · rwa [leafGap, leaves_expansion j w.1 w.2 x v]

/-- After the individual dimensions have been paid, the price of the
complete signed product has a strict 1/32 surplus. Its matching column is
the exact weighted sum of the displayed native source columns. -/
theorem engineering {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (v : α → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE l T (fun t => v t i k) (-(d i : ℝ))) :
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height C.S l T b h ∧ Height C.S l T m a ∧
      Height C.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ W r μ, ∃ L : LogPackage C W r μ, ∃ cap price : α → Indices C d → ℝ,
        RateLE l T (fun t => ∑ u, ‖weight (v t) u‖ * price t u) (-(D : ℝ) - 1/32) ∧
        ∀ᶠ t in l, C.ref D ≤ b t ∧ ∀ (x : I → Cover), Plot C (b t) (m t) (j t) x →
          ∀ (stop : ℕ) (href : C.ref D ≤ stop), stop ≤ b t →
            SourcedCombination L.toPackage (b t) (m t) (j t) D x (v t) f stop href
              (cap t) (price t) := by
  obtain ⟨h, a, c, hh, ha, h₁, hc, hmargin⟩ :=
    engineering_margin D (∑ i, d i) (Fintype.card I)
  obtain ⟨b, hb⟩ := found hT C.path.levels.fits.mesh hh.le
  obtain ⟨m, hm⟩ := found hT C.path.levels.fits.mesh (hh.trans ha).le
  obtain ⟨j, hj⟩ := found hT C.path.levels.fits.mesh (zero_lt_one.trans hc).le
  obtain ⟨W, r, μ, L, g, e, hr, hs⟩ := basis_bank (d := d) F facility anchor hT D hb hm hj ha
    (h₁.trans hc)
  refine ⟨b, m, j, h, a, c, hb, hm, hj, hh, ha, h₁, hc, W, r, μ, L, g, e, ?_, ?_⟩
  · apply (weighted_rate hT v e (fun i => -(d i : ℝ)) _ hv (fun u => (hr u).2)).mono
    push_cast at hmargin ⊢
    rw [Finset.sum_neg_distrib]
    linarith only [hmargin]
  · filter_upwards [hs, hm.grows.eventually_ge_atTop (C.ref D)] with t ht hm'
    exact ⟨ht.1, fun x hx stop href hstop => combine L.toPackage F.room.cutoff hm' href x
      (v t) (g t) (e t) (ht.2 x hx stop href hstop)⟩
end YM.Integration.FundedProductCellMatch
