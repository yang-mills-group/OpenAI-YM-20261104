-- Ported from base Lotus/Spectrum, Pane. Here many marked V-dependent vertices
import YM.QCDVacuum.Stall.Town
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Pane
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Township
variable {Jx : Type}[Fintype Jx]{τx : Jx ↪ Wing} (M : Township τx R T) (X : Coat T F) (k:Finset ℕ)
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider  Hues Rotation
open Packets Art Silica Poll Pond
variable {X':Coat T F} {H: Support c} {I : Finset (Tubular f G)} {Z : Support c} {k k' : Finset ℕ} {l : ℕ}
    {u v : Air f G} (p:Molecule S)
abbrev floret (W a:ℝ)(Ñ:ChartRatio G)(l : Finset ℕ) (n:ℕ)(w:Air f G):=(M.hire p X.V).paidU X a (worldZ X R.beta w) * Polar.floating X a R W Ñ w l n (p\((tick τx p).map (registry S τx)))
lemma census (hX : Intake P T X.x R) (hp:Room P S T X.x) (hl:500≤l) (ht:Borough X X' Z u v k k' R) (he:ground R T l X.B p⊆ Z): M.floret X p W a Ñ k l u=M.floret X' p W a Ñ k' l v:=by
  unfold floret; rw [M.chivalry X _ X.V X'.V (agrees_mono ht.actual he), M.coins X _ _ X' Z v ht hp hl hX he]; apply congr_arg; exact ht.flops hp hl hX _ W Ñ ((show ground R T l X.B (p\ _)⊆ ground R T l X.B p from Finset.biUnion_subset.mpr (fun i hi=>subset_biUnion_of_mem _ (Finset.sdiff_subset hi))).trans he)
lemma drift_b {A : Type*} [MeasurableSpace A] (Y : A→ F.Slice G) (V : A→ Config G c) (w : A→ Air f G) (hg:ShellAccess S G X.x W X.width C) (ht:Intake P T X.x R)(he:LocalRatio Ñ)(hV:Measurable V)(hY:Measurable Y)(h:Measurable w): Measurable fun t=> M.floret (Art.drive X (V t) (Y t)) p W a Ñ k l (w t):=by
  unfold floret
  let r t:=drive X (V t) (Y t); let b t:=worldZ (r t) R.beta (w t)
  have hp:Measurable b:=(compassBro ht.ready hV X hY hg R.beta).2.2 _ h
  exact (M.tax_m X p Y V b hY hV hp).mul (Shield.collectionB X hg ht he hV hY h ..)

def cinema (W a:ℝ) (Ñ:ChartRatio G) (l:ℕ) (I : Finset (Tubular f G)):=
    ∫ Y, (∫ z, Shield.lens₀ (Pond.circuit I X.relating) z * M.floret (X.wrapY Y) p W a Ñ (own p) l (Pond.spill I z)) ∂F.order G

lemma page (h: Intake P T X.x R) (hp:ShellAccess S G X.x W X.width C)(hx:LocalRatio Ñ): Measurable fun V=> M.cinema (vary X V) p W a Ñ l I:=by
  let E':= (Config G c × F.Slice G) × Body (↥ I)
  let V (t:E'):= t.1.1; let Y (t:E'):= t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2* M.floret (drive X (V i) (Y i)) p W a Ñ (own p) l (Pond.spill I i.2)
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have hh := c_measured X.shutter (A:=fun i=> (vary X (V i)).plate) (fun i j=> (Art.borel_plate X h.ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j=> hh.1 i.val j.val : Borel fun i=> Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (M.drift_b X p Y V _ hp h hx hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd))
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=MeasureTheory.volume)).integral_prod_right' (ν:=F.order G)).measurable
lemma synchronizeLK (h:Intake P T X.x R) (hp : ground R T l X.B p ⊆ H) (hr : Room P S T X.x) (hV : Village X X' H)(hl : 500 ≤ l):
    M.cinema X p W a Ñ l (podium S G H X.B)=M.cinema X' p W a Ñ l (podium S G H X.B):=by
  let I:=podium S G H X.B
  have he : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hV.same_cov hr j.val j.property i.val
  unfold cinema; rw [he]; apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  apply congr_arg₂ (·*·) rfl; let v:=Pond.spill I y
  exact M.census (X.wrapY q) p h hr hl (show Borough (X.wrapY q) (X'.wrapY q) H v v (own p) (own p) R from ⟨hV.wrap q q (fun _ _=> rfl),fun _ _=> rfl,fun _ _=>Iff.rfl⟩) hp

lemma selfish (U : Cash W X.x μ L Q o C T R) (hX:X.width=o.K) (hm:X.manifest)(H: Support c)(hP:Healthy (Pressure.temp X.x) (U.unionP p) X.V)(he: U.unionP p⊆ H): M.cinema X p W o.a Q.table Q.halo (podium S G H X.B)=(M.hire p X.V).tithe X (own p) W o.a Q.table Q.halo p:=by
  let B:=podium S G H X.B
  have ht : X.relating.PosDef := (U.laws.data.localP _ X rfl hX hm).sails.fullC
  have hv : (circuit B X.relating).PosDef:= ht.submatrix Subtype.val_injective
  have hh := (M.hire p X.V).tip X (own p) U hX hm p
  unfold cinema Faction.tithe; rw [integral_prod _ hh.2.1]; apply integral_congr_ae; filter_upwards with y
  let g (z : Air f G):= (M.hire p X.V).into X W o.a Q.table (own p) Q.halo p (y,z)
  have hp : Measurable g:= hh.1.meas.comp (measurable_const.prodMk measurable_id)
  let Y:= X.wrapY y; have hz z: M.floret Y p W o.a Q.table (own p) Q.halo z=g z:=by
    unfold g Faction.into Faction.premium floret; rw [if_pos (M.chums ..),show (M.hire p X.V).signs=(tick τx p).map _ from Quartet.hei ..] -- replace
    have hW:= U.laws.data.room; rw [show worldZ Y R.beta z=Y.liftA R.beta z from (shine Y hW hm _ _).symm]; exact congr_arg (_*·) (Polar.afterborn Y o.a R W Q.table z (own p) hW hm Q.buys _ (Finset.disjoint_of_subset_left (Finset.biUnion_subset.mpr (fun i hi=> subset_biUnion_of_mem _ (Finset.sdiff_subset hi))) hP)).symm
  symm; change (∫ i, g i ∂ _)=_; refine Eq.trans ((Pond.gathered (Pond.spill B) (Pond.spill_m B) (Pond.orbit ht.posSemidef B) (Pond.settled _) (f:=g) ?_ hp).trans (Shield.recommends _ hv (fun z=>g (spill B z)))) ?_
  swap; · exact integral_congr_ae (Eventually.of_forall fun z=>congr_arg (_*·) (hz _).symm)
  intro u v h
  exact (M.hire p X.V).concur Y _ _ ⟨Village.refl Y H, (Pond.observe B).1 h,fun _ _=>Iff.rfl⟩ U.laws.data.room Q.buys he U.laws.intake
def grove (W a:ℝ) (Ñ:ChartRatio G)(l:ℕ):= if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely (fun i=> M.cinema ((preps X (roster p)).taggedL i) p W a Ñ l (podium S G (ground R T l X.B p) X.B)) else 0
variable (ht:Intake P T X.x R) (hs:Room P S T X.x) (hp:ShellAccess S G X.x W X.width C) (hN:LocalRatio Ñ) (hl:500≤l)
include ht
include hp hN in
lemma groveB : Measurable fun y=> M.grove (vary X y) p W a Ñ l:=by
  classical
  let Z(v):= vary X v; let H:= ground R T l X.B p
  change Measurable fun y=> if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely (fun i => M.cinema ((preps (Z y) (roster p)).taggedL i) p W a Ñ l (podium S G H X.B)) else 0
  split_ifs
  · refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=>?_)
    let Y:=(preps X (roster p)).taggedL i
    exact M.page Y p ht hp hN
  exact measurable_const
include hs hl in
lemma groveL : LocalOn (ground R T l X.B p) (fun V:Config G c=> M.grove (vary X V) p W a Ñ l):=by
  intro V U hu; let s:=ground R T l X.B p; unfold grove
  change (if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely _ else (0:ℝ))= (if Ac.Spark (areas R T l X.B) p∧ troupe T R l X.B p then likely _ else (0:ℝ)); split
  next he=>
    apply congr_arg likely; funext k
    exact M.synchronizeLK ((preps (vary X V) (roster p)).taggedL k) p ht (hp:=Finset.Subset.refl _) hs (show Village _ ((preps (vary X U) (roster p)).taggedL k) s from ⟨rfl,rfl,rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,hu⟩) hl
  next => rfl
omit ht
-- no changed appointment.C for anal bank
variable (H : Cash W x μ L Q o C T R) {v d b C' B A r: ℝ} {j k : ℕ}{χ:Chi}{Ξ:Utopia H j v d r C' χ} (hΘ:Oboe H j v B k A b Ξ)
    (hX:X.x=x) (hv:X.width=o.K) (he:X.χ=χ) (h:(roster p).flags=∅) (hy:Healthy (Pressure.temp x) (H.unionP p) X.V)
include hX hy h
lemma casin (q: S.Choices)(U V:Config G c)(hq:Agrees (H.unionP p) U V):
    let I:=podium S G (H.unionP p) (radiusB x)
    M.cinema (vary ((planted X p).taggedL q) U) p W a Ñ Q.halo I=M.cinema ((preps (vary X V) (roster p)).taggedL q) p W a Ñ Q.halo I:=by
  intro I; let A:=vary ((planted X p).taggedL q) U; let A':=(preps (vary X V) (roster p)).taggedL q
  have hv : Village A A' (H.unionP p):=by
    refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,hq⟩
    intro i hi; have he : i∉RG.flags (Pressure.temp X.x) X.V:=by rw [hX]; exact Finset.disjoint_left.mp hy hi
    unfold A A' vary taggedL planted preps place; simp [h,he]
  unfold I; rw [← show A.B=radiusB x from congr_arg radiusB hX]; apply M.synchronizeLK A p (show Intake P T A.x R from hX.symm ▸ H.laws.intake) (l:=Q.halo) _ (show Room P S T A.x from hX.symm ▸ H.laws.data.room) hv Q.buys
  change ground R T Q.halo (radiusB X.x) p⊆ _; rw [hX]; exact Subset.refl _
include hv
omit hy in
lemma pictured : (M.hire p X.V).bloom X W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (fun V=> M.grove (vary X V) p W o.a Q.table Q.halo) X.V:=by
  let V:= H.unionP p; have ht:ground R T Q.halo X.B p=V:=by unfold Coat.B; rw [hX]; rfl
  have hB : X.B=radiusB x:=congr_arg radiusB hX
  by_cases hh: Healthy (Pressure.temp x) V X.V
  · rw [masked_eq _ _ _ _ hh,Faction.bloom]; unfold grove; simp_rw [show vary X X.V=X from rfl]
    split
    next hy=>
      rw [if_pos ⟨hy.1,hy.2.1⟩,ht,hB] -- X.B
      apply congr_arg likely; funext k; let K:= (planted X p).taggedL k
      let I:=podium S G V (radiusB x)
      have hf : M.cinema K p W o.a Q.table Q.halo I=(M.hire p X.V).tithe K (Matter.own p) W o.a Q.table Q.halo p:=by
        have H':Cash W K.x μ L Q o C T R:= hX.symm ▸ H -- careful simp.R
        unfold I; rw [← hB]; apply M.selfish K p H' hv (planted_valid X p) V
        · change Healthy (Pressure.temp X.x) (ground R T Q.halo X.B p) X.V; rw [ht,hX]; exact hh
        exact ht.le
      exact hf.symm.trans (M.casin X p H hX h hh k X.V X.V (fun _ _ _=>rfl))
    next hy=>
      rw [if_neg]; rintro ⟨h₁,h₂⟩; apply hy
      have hf : RG.flags (Pressure.temp X.x) X.V ∩ ground R T Q.halo X.B p=(roster p).flags:=by rw [ht,hX,h]; exact Finset.disjoint_iff_inter_eq_empty.mp (show Disjoint _ _ from hh.symm)
      exact ⟨h₁,h₂,hf⟩
  rw [masked_ne _ _ _ _ hh,Faction.bloom,if_neg]
  intro hp; apply hh
  unfold Healthy; rw [← hX,← ht]
  apply Disjoint.symm; exact Finset.disjoint_iff_inter_eq_empty.mpr (hp.2.2.trans h)
end Township
end YM.PhysicalNext.Repeat.Lotus
