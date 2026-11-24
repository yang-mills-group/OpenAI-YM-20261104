import YM.Integration.FundedProductCellMatch
import YM.Integration.PricedWholeProduct

/-! Original finite Wilson matching with the scale prices of `OPE.funding`.
The tagged label and the source receipt use the very same family at every
finite cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedIntrinsicProduct
open Trace.Physical.GermGraph
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
structure Quotation (H : C.Makes) (L : Package C W r D) (cap price : ℝ)
    (n : ℕ) (d : I → ℕ) (s : (i : I) → C.label (d i)) (J m j : ℕ) : Prop where
  live : J ≤ m
  goes : m+1 ≤ j
  opened : ∀ p, Opened C n J p
  quote (N p : ℕ) (hn : j < N) (hb : J ≤ N) (positions : I → Site (C.side j p))
    (hslots : ∀ i, loops C j p (positions i) (m+1) = 0)
    (separation : Next.Rank.Edition.Spaced (C.path.levels.budget j).B positions) :
    let cell := Cells.center C.S p hb 0
    let field (i : I) := C.O N p (s i) ((C.S.toDepth hn.le p).embed (positions i))
    (∀ i, Cells.Interior (cell.chamber 0) (field i)) →
    (∀ z : C.label n, Cells.Interior (cell.chamber 0) (C.O N p z 0)) →
    let source : Config G (C.side N p) → ℂ := fun U => ∏ i, field i U
    ∃ z : C.label n,
      OriginalProductCellMatch.SourceAt C N m p n J L.system J (opened p).post source cap price z ∧
      WholeProductCapture.Retained C N m p n J H (opened p) live (by omega) source z (cap/2) ∧
      Next.UVStress.quota C n m N p z ≤ cap ∧
      Cells.Interior (cell.chamber 0) (source - C.O N p z 0) ∧
      cell.rootTest (C.beta N p) (source - C.O N p z 0) ≤ price
local notation "Z'"=> ((∑ x,d x:ℕ):ℝ)*c +4*(Fintype.card I:ℝ)*(c-a)
local notation "X'"=> ((t:ℝ)+1/16)*(a-b)-(Z')
-- PriceAt along scales; with geometry paid elsewhere
include i₀ h hG
/-- The funding of every separated tuple of fixed original fields retains
its served coefficient and calibrated primary, down to each chosen stop. -/
theorem funding (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hj:Height C.S l T j c)(hT:Tendsto T l atTop)(he:b<a)(ht:a<c) (hΩ:∀ᶠ i in l, Push.GridApprox.room C.path.levels (k i) (m i) (lensScope C t)) :
    ∃ g o : ι→ℝ, RateIs l T g ((Z')-t*a) ∧ RateLE l T o (-(X')) ∧
       (∀ᶠ i in l,0<o i) ∧ ∀ᶠ i in l, Quotation h L (g i) (o i) t d s (k i) (m i) (j i):=by
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
    filter_upwards [hk.mesh.overtakes (hW'.pays hT) hT (by simp; linarith),hP.earlier he hT hm, hm'.earlier ht hT hj, hp, hx.pos, hΩ, hk.grows.eventually_ge_atTop (C.ref t), eventually_all.mpr (fun x=>hj.grows.eventually_ge_atTop (C.ref (d x))),hk.grows.eventually (open_late C hG t)] with i hψ hPi hS hp hx hr hK hd hopen
    have hf'(p:ℕ): ((P' (S i)).B^2+1:ℕ) ≤ (C.S.toDepth (((ha i).1.trans hPi.le).trans (Nat.le_succ (m i))) p).count.val:= by
       let v:= C.S.toDepth (((ha i).1.trans hPi.le).trans (m i|>.le_succ)) p; have hl: ((P' (S i)).B:ℝ)^2+1 ≤ v.count.val:=by
          apply le_of_mul_le_mul_right _ (C.S.a_pos (S i)); exact hψ.le.trans_eq ((C.S.embeds_scale v).symm.trans (mul_comm ..))
       exact_mod_cast hl
    refine ⟨(ha i).1.trans hPi.le, hS.le, hopen, fun N p hn hz r he hw hi₀ hi₁ => ?_⟩
    -- careful let V etc introduction reflexive
    have hhalf : g i / 2 = e i := by dsimp [g]; ring
    rw [hhalf]
    exact PricedWholeProduct.capture_product_receipt C N (m i) p t (k i) (P i) i₀ (z i) (fun p=> plumR C (d p) (B p) (j i)) r (ha i).1 hPi.le hn hS.le d s h L.system L.literal (hχ t) L.tabs (ha i) (k i) (hopen p).post (ha i).1 (hopen p) hd (fun p=>paid_new C N _ _ (d p) h (s p) (B p) (hf p) (le_add_of_nonneg_left zero_le_one) (hd p) hn) (fun p=>stockpit _ _ _ _ (hf p)) hr he (hf' _) hw (hy.pos (j i)) (hF (j i)) (Or.inr (fun q₀ _ hp=> hY (j i) q₀ hp.le)) _ (fun _=>rfl) hi₀ hi₁ hx le_rfl (Real.exp_pos _)
      hp.1 le_rfl hp.2

end YM.Integration.FundedIntrinsicProduct

namespace YM.Integration.FundedIntrinsicProduct
open Function Filter Lattice Wilson RG Cells OPE OPE.Log MergeProof MergeProof.Ribbons Frontier6.Road
open MultilinearCellCapture Trace.Physical.GermGraph RG16.Literal Bid
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {W r μ}
variable (L : Package C W r μ)

/-- The intrinsic calibrated report of the actual product has an explicit
price against the one label carried in its signed trajectory. -/
def WrappingPrice (H : C.Makes) (D b m : ℕ) (cap bound : ℝ) : Prop :=
  ∀ (N p : ℕ) (ho : Opened C D b p) (hb : b ≤ m) (hm : m < N)
    (field : Config G (C.side N p) → ℂ) (z : C.label D),
    WholeProductCapture.Retained C N m p D b H ho hb hm field z (cap/2) →
    mCost C D N p b
      (topReport C N p D H b ho (hb.trans hm.le) field - (C.factory D N p).terminal.symm z)
      ≤ bound

/-- A positive stopping height pays every prescribed exterior-time
exponential for the wrapping displacement of the funded receipt. -/
theorem wrapping_price {α : Type*} {l : Filter α} {T cap : α → ℝ} (H : C.Makes)
    (hG : G.Simple) (hT : Tendsto T l atTop) (D : ℕ) {a h cost : ℝ} {b m : α → ℕ}
    (hb : Height C.S l T b h) (hm : Height C.S l T m a) (hh : 0 < h)
    (hc : RateIs l T cap cost) (q : ℝ) :
    ∀ᶠ t in l, WrappingPrice H D (b t) (m t) (cap t) (Real.exp (q*T t)) := by
  let γ := (1/8:ℝ)*(a-h)
  let σ := (q-cost+γ-1)/h
  have hg : RateIs l T (fun t => gainChart C.path (m t) (b t)) γ := by
    refine ⟨Eventually.of_forall (fun _ => Real.exp_pos _), ?_⟩
    simp only [gainChart, Real.log_exp, mul_div_assoc, sub_div, γ]
    exact tendsto_const_nhds.mul (hm.pace.sub hb.pace)
  have he : RateIs l T (fun t => Real.exp (σ*C.S.scale (b t))) (σ*h) := by
    refine ⟨Eventually.of_forall (fun _ => Real.exp_pos _), ?_⟩
    simp only [Real.log_exp, mul_div_assoc]
    exact tendsto_const_nhds.mul hb.pace
  have hhalf := hc.div (RateIs.const hT (by norm_num : (0:ℝ) < 2))
  have hbudget := ((RateLE.const (price (C:=C) D) hT).mul (he.pays hT)).mul
    (hhalf.div hg |>.pays hT)
  have hσ : 0+σ*h+(cost-0-γ) < q := by
    dsimp only [σ]; rw [div_mul_cancel₀ _ hh.ne']; linarith
  filter_upwards [hb.grows.eventually (WholeProductCapture.wrapping_flat C H hG D σ),
    hbudget q hσ] with t hwrap hprice N p ho hs hf field z paid
  exact (hwrap N (m t) p ho hs hf field z (cap t/2) paid).trans
    ((le_abs_self _).trans hprice)

/-- All fields here use the original regulator pair and one selected label. -/
def Stage (H : C.Makes) (b m j D : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (cap price bound : ℝ) (w : ℕ × ℕ) (z : C.label D) : Prop :=
  ∃ (ho : Opened C D b w.2) (hs : b ≤ m) (hf : m < w.1),
    let field := leaves C j d x v w.1 w.2
    let hb := hs.trans hf.le
    let gap := leafGap C j D d x v w.1 w.2 z
    OriginalProductCellMatch.SourceAt C w.1 m w.2 D b L.system b ho.post field cap price z ∧
    WholeProductCapture.Retained C w.1 m w.2 D b H ho hs hf field z (cap/2) ∧
    mCost C D w.1 w.2 b (topReport C w.1 w.2 D H b ho hb field -
      (C.factory D w.1 w.2).terminal.symm z) ≤ bound ∧
    Next.UVStress.quota C D m w.1 w.2 z ≤ cap ∧
    Interior ((center C.S w.2 hb 0).chamber 0) gap ∧
    (center C.S w.2 hb 0).rootTest (C.beta w.1 w.2) gap ≤ price

/-- Retain the same funded label across the original fused regulator tail. -/
theorem on_grid (H : C.Makes) {b m j D : ℕ} {cap price bound : ℝ}
    (x : I → Cover) (v : (i : I) → C.label (d i))
    (paid : Quotation H L cap price D d v b m j)
    (shape : Plot C b m j x) (hwrap : WrappingPrice H D b m cap bound) :
    ∃ Z : (ℕ × ℕ) → C.label D, ∀ᶠ w : ℕ × ℕ in f.fuse,
      Stage L H b m j D x v cap price bound w (Z w) := by
  have hN := Cards.largeMesh f
  have hp : Tendsto (@Prod.snd ℕ ℕ) f.fuse atTop := tendsto_atTop.mpr fun t => by
    rw [Extraction.Order.fused, Extraction.Order.late]
    filter_upwards [f.per.cofinal.eventually_ge_atTop t] with p ht
    exact Eventually.of_forall fun _ => ht
  have available : ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ z, Stage L H b m j D x v cap price bound w z := by
    filter_upwards [hp.eventually shape.marsh, hN.eventually (near_center C b D H),
      eventually_all.mpr (fun i => hN.eventually (near_center C b (d i) H)),
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
    have hf : m < w.1 := lt_of_le_of_lt (m.le_succ.trans shape.last) hj'
    obtain ⟨z, hsource, hretain, hcost, hlocal, hbound⟩ :=
      paid.quote w.1 w.2 hj' hb y (fun i => (scene.2 i).1) scene.1 hi hc
    have source : leaves C j d x v w.1 w.2 = (fun U => ∏ i, field i U) := by
      funext U
      simp only [leaves, field, y, comp_apply, Finset.prod_apply, Cells.location, dif_pos hj'.le]
    have eq : leafGap C j D d x v w.1 w.2 z =
        (fun U => ∏ i, field i U) - C.O w.1 w.2 z 0 := by rw [leafGap, source]
    have retained : WholeProductCapture.Retained C w.1 m w.2 D b H (paid.opened w.2)
        paid.live hf (leaves C j d x v w.1 w.2) z (cap/2) := source ▸ hretain
    exact ⟨z, paid.opened w.2, paid.live, hf, source ▸ hsource, retained,
      hwrap _ _ _ _ _ _ _ retained, hcost, eq ▸ hlocal, eq ▸ hbound⟩
  let fits := Stage L H b m j D x v cap price bound
  let Z (w : ℕ × ℕ) : C.label D := if h : ∃ z, fits w z then h.choose else 0
  refine ⟨Z, available.mono ?_⟩
  intro w hw
  change ∃ z, fits w z at hw
  change fits w (Z w)
  simpa only [Z, dif_pos hw] using hw.choose_spec

theorem Stage.reprice {H : C.Makes} {b m j D : ℕ}
    {x : I → Cover} {v : (i : I) → C.label (d i)} {cap fee old bound : ℝ}
    {w : ℕ × ℕ} {z : C.label D} (source : Stage L H b m j D x v cap fee old w z)
    (price : WrappingPrice H D b m cap bound) : Stage L H b m j D x v cap fee bound w z := by
  obtain ⟨ho, hs, hf, hsource, hretain, _, hquota, hloc, hroot⟩ := source
  exact ⟨ho, hs, hf, hsource, hretain, price _ _ _ _ _ _ _ hretain, hquota, hloc, hroot⟩

/-- A single engineering-rate budget supplies the exact signed basis,
its physical root test, its original finite trajectory and its intrinsic
report with any fixed exponential accuracy at a positive stopping height. -/
theorem basis {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) {a h c : ℝ} {b m j : α → ℕ}
    (hb : Height C.S l T b h) (hm : Height C.S l T m a) (hj : Height C.S l T j c)
    (hh : 0 < h) (ha : h < a) (hc : a < c) :
    let load := ((∑ i, d i : ℕ) : ℝ) * c + 4 * (Fintype.card I : ℝ) * (c-a)
    ∃ W r μ, ∃ L : LogPackage C W r μ, ∃ gain error : α → Indices C d → ℝ,
    ∃ Z : α → (I → Cover) → Indices C d → (ℕ × ℕ) → C.label D,
      (∀ u, RateIs l T (fun t => gain t u) (load - D*a) ∧
        RateLE l T (fun t => error t u) (-(((D:ℝ)+1/16)*(a-h)-load))) ∧
      ∀ q : ℝ, ∀ᶠ t in l, ∀ (x : I → Cover), Plot C (b t) (m t) (j t) x →
        ∀ u : Indices C d, ∀ᶠ w : ℕ × ℕ in f.fuse,
          Stage L.toPackage F.room.cutoff (b t) (m t) (j t) D x (basisLabels u)
            (gain t u) (error t u) (Real.exp (q*T t)) w (Z t x u w) := by
  obtain ⟨W, r, μ, L⟩ := facility.costlier
  choose g e hg he hpos hp using fun u : Indices C d =>
    funding anchor facility.simpleGate L.toPackage F.room.cutoff d (basisLabels u) D
      hb hm hj hT ha hc (height_room hb hm hT ha _)
  let certified (t : α) (x : I → Cover) (u : Indices C d) (Z : (ℕ × ℕ) → C.label D) :=
    ∀ᶠ w in f.fuse, Stage L.toPackage F.room.cutoff (b t) (m t) (j t) D x (basisLabels u)
      (g u t) (e u t) 1 w (Z w)
  let pick (t : α) (x : I → Cover) (u : Indices C d) : (ℕ × ℕ) → C.label D :=
    if h : ∃ Z, certified t x u Z then h.choose else 0
  refine ⟨W, r, μ, L, (fun t u => g u t), (fun t u => e u t), pick, fun u => ⟨hg u, he u⟩, ?_⟩
  intro q
  filter_upwards [eventually_all.mpr hp, eventually_all.mpr (fun u : Indices C d =>
    wrapping_price F.room.cutoff facility.simpleGate hT D hb hm hh (hg u) 0),
    eventually_all.mpr (fun u : Indices C d =>
    wrapping_price F.room.cutoff facility.simpleGate hT D hb hm hh (hg u) q)] with t hprice hzero hwrap
  intro x hx u
  have existsSource : ∃ Z, certified t x u Z := by
    simpa only [certified, zero_mul, Real.exp_zero] using
      (on_grid (f:=f) L.toPackage F.room.cutoff x (basisLabels u) (hprice u) hx (hzero u))
  have source : certified t x u (pick t x u) := by
    simpa only [pick, dif_pos existsSource] using existsSource.choose_spec
  exact source.mono fun _ hsource => Stage.reprice L.toPackage hsource (hwrap u)

end YM.Integration.FundedIntrinsicProduct
