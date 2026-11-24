import YM.LocalTaylorR2.Test

/-!
# Using the actual local log as well as its exp

The proof of Zest exposes the corresponding argument of E6 Fairum and
Ambit (dark, exert, wells proof restored here). No alteration of tag or
Haar reads.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Glass
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond  Eider Flux Zest
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {I : Finset (Bond f)} {η r Q q a β b p v d t W σ : ℝ} {C : E → Config G c}
variable (H : Glass P X C x j W) {Y : A→ F.Slice G} (U : A→ Config G f) {Ñ : ChartRatio G} {R : Rep G f}
variable {u : A→ E → Directions G f} {w : A→ E → Air f G} {k : Finset ℕ} (hq : Room P S T X.x)

include H in
private lemma darkZestR2 (h : Intake P T X.x R) (i : LogLetter c f) : Zest (fun l y=> nest T X.x (C y) (U l) R i) x j := by
  obtain ⟨V,hV⟩:=H.sails
  have hp (i : Trans f) {d} (A : ℕ → Atom G d) (a : ℝ) : Zest (fun s (_:E)=> translateValue R.p A a (U s) i) x j := by
    let K:= (A i.2.2).magnitude
    refine Zest.parallel (w:=|a| * (K *R.p.threshold^d)) ?_ ?_
    · unfold K Atom.magnitude; have hv := R.p.threshold_pos; positivity
    intro p; rw [translateValue,norm_mul]; exact mul_le_mul_of_nonneg_left (by
      have hs:= healthy_atom (A i.2.2) R.p (pull i.1 0 (U p)) i.2.1; exact hs) (abs_nonneg _)
  unfold nest; rcases i with i|i|i|i|i|i <;> simp only [Sum.elim]
  · obtain ⟨Z,hZ,h₁⟩:= h.cap.labels.boundE
    refine (Zest.parallel (hZ i).1 (fun u' : A=> ?_) : Zest (fun t _=> R.activities.regularOccurrence R.p i (U t)) x j).against
    unfold Activities.regularOccurrence; by_cases hh : Healthy R.p.threshold (R.activities.reg i).support (U u')
    · rw [masked_eq _ _ _ _ hh]; exact (hZ i).2 _ hh [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hh,norm_zero]; exact (hZ i).1
  · exact hp _ _ _
  · exact hp _ _ _
  · exact hp _ _ _
  · let b:= -Raw.orientation * R.beta
    let v := pairPrice R.path (till X.x) 1 i.2.1 i.2.2.2
    refine Zest.parallel (w:= |b| *v) (mul_nonneg (abs_nonneg _) (Raw.pairPrice_nonneg ..)) ?_
    intro s; unfold pairValue; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (Raw.pair_le ..) (abs_nonneg _)
  apply Zest.single; unfold icicle Polar.twin; split_ifs
  next he=> refine contDiffAt_const.mul ((ContDiffAt.inner ℝ ?_ ?_).div_const _)
            all_goals unfold PathData.ellTerms; exact ((slot_cost _ _ hV.pos (Blaze.turn hV i.1).atLink).smooth.const_smul _)
  exact contDiffAt_const

include H hq
private lemma exertZestR2 (p : Spot c f) (s : Signed) (hp : Zest u x j) : Zest
    (fun t y=> Vine.costs (drive X (C y) (Y t)) (u t y) s p) x j := by
  refine Zest.total _ _ (fun i (_:i∈parents p)=>?_); unfold Vine.pot; change
    Zest (fun t y=> if X.selected s (spot S i) then ‖_‖^2 /2 else (0:ℝ)) _ _
  split_ifs
  next ht=> exact (H.fellows u hq (Y:=Y) (s,i) ht hp).wand (p:=fun y:G.Color=> ‖y‖^2/2)
              ((contDiff_norm_sq ℝ).div_const _)
  next h=> exact Zest.still _

private lemma wellsZestR2 (i : ChainIndex f) (pu : Zest u x j) (pw : Zest w x j) : Zest
    (fun t y=> Polar.spins (drive X (C y) (Y t)) a R (u t y) (w t y) i) x j := by
  let g t y:= drive X (C y) (Y t)
  have hA i : Zest (fun t y=> Polar.patch X a (u t y) i) x j := by
    unfold Polar.patch; split_ifs
    · exact (pu.replay (ContinuousLinearMap.proj i)).wand (tip (X:=X) _)
    exact Zest.still (1:ℝ)
  have hw (p:Tubular f G): Zest (fun t y=> WithLp.ofLp (w t y) p) x j := pw.replay (EuclideanSpace.proj p)
  rcases i with i|i|i|i|i
  · apply (Zest.single (A:=A) (H.gracious i)).wand (p:=fun x:ℝ=> -x/2) (by fun_prop)
  · exact Zest.still (ArmA X.shutter X.blank.plate i/2)
  · exact (Zest.single (A:=A) (H.tenuous i)).wand (p:=fun x:ℝ=>x/2) (by fun_prop)
  · have hT p : Zest (fun t y=> shimmer (g t y) R.beta p) x j := by
      have hh f : Zest (fun t y=> leanB (g t y) f) x j := by
        have hf i:Zest (fun t y=> Vine.bar (g t y) 0 i) x j := by
          change Zest (fun a y=> if X.selected _ _ then _ else 0) x j; split_ifs
          next ht=> exact (H.fellows (u:=fun _ _=>0) (Y:=Y) hq i ht (Zest.still _)).scalar Coat.scale
          next => exact Zest.still _
        exact Zest.total _ _ (fun i _=> (Zest.single (H.figures i.1 _ i.2)).paint
          ((hf i.1).replay (EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) i.2)))
      have hg i:Zest (fun t y=> well (g t y) i) x j := (Zest.total _ _ (fun k _=> (Zest.single (H.brews.2 _ _)).paint (hh k))).against
      exact ((Zest.total _ _ (fun i _=> (Zest.single (H.vest _ _)).paint (hg i))).together (hh p)).scalar (-(gStep R.beta)⁻¹)
    exact (hA _).paint (Zest.total _ _ (fun j' _=> (hw (i,j')).paint (hT _)))
  let v := i.2.1; let l:=i.2.2; let V:=arrive v l
  let b(y:E):= combo v l ((vary X (C y)).finale i.1)
  have he k j':ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun y=> b y k j') x := by
    refine smooth_combo (fun y=> (vary X (C y)).finale i.1) ?_ l v k j'
    intro j hj k q; unfold finale; split_ifs
    · refine ((((per_entry _ (fun y=> (vary X (C y)).relating) x _ _ (fun j=> H.vest k j) (fun j=> H.relate j q)).sub
        (contDiffAt_const (c:= (1:Mat f G) k q))).neg))
    exact H.vest k q
  have hy := Zest.total (univ (α:=G.ColorIndex)) _ (fun j (_: j∈univ)=> (hw (v,j)).paint (Zest.total univ _ (fun k _=>
    (Zest.single (A:=A) (he j k)).paint (hw (V,k)))))
  exact ((hA v).paint (hA V)).paint (hy.scalar (1/2))

lemma logZestR2 (u : A→E → Directions G f) (hU : Zest u x j) (he : Intake P T X.x R)  (ha : 0<a*X.t)
    (ht : 4*a*X.t < Ñ.radius) (hΛ : LocalRatio Ñ) (i : LogIndex c f) (hp : Zest w x j) :
    Zest (fun t y=> Polar.logMoment (drive X (C y) (Y t)) a R Ñ (u t y) (U t) (w t y) i) x j := by
  let S' t y:=drive X (C y) (Y t)
  have hx b i : Zest (fun t y=> X.cone b (u t y) i) x j := (hU.replay (ContinuousLinearMap.proj _)).wand (tip (X:=X) _)
  have hv i:Zest (fun t y=> X.enforce (2*a) (u t y) i) x j := Zest.full _ _ (fun i _=> hx _ _)
  rcases i with i|i|i
  · exact (H.darkZestR2 U he i).paint (hv (X.plaza (space T 0 X.B R i)))
  · rcases i with i|i|i
    · change Zest (fun t y=> if Inside _ X.seeds (200*X.B) then (0:ℝ) else _) _ _
      split_ifs
      · exact Zest.still _
      have hh:Zest (fun t y=> rootface (S' t y) (u t y) (U t) true i.1 i.2) x j :=
        ((H.canopy i.1 i.2).2.via (fun v=> pull i.1 0 (U v))).plusminus (H.exertZestR2 hq _ _ hU)
      exact (((hv (X.booth (rowSite S i))).paint hh).together (H.exertZestR2 (Y:=Y) hq i.2 i.1 (H.settles (Y:=Y) hq))).scalar (-R.beta*Raw.orientation)
    · change Zest (fun t y=> if voyage X.seeds _ i then 0 else (vary X (C y)).condensation i) x j
      change Zest (fun t y=> if voyage X.seeds (200*X.B) i then 0 else (vary X (C y)).condensation i) x j
      split_ifs
      · exact Zest.still _
      exact Zest.single (H.condiment i)
    change Zest (fun t y=>X.solo (u t y) Ñ a i) x j; unfold solo; split_ifs
    · exact (hU.replay (ContinuousLinearMap.proj _)).wand (elevator (X:=X) hΛ ha ht)
    exact Zest.still _
  exact H.wellsZestR2 hq i hU hp
omit hq H
end YM.ConnectedActivityE6.Blaze.Glass

namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Itinerary Channel Next.Foundations Zest
variable {C' : ℝ} {j:ℕ}
-- Log-index injection (not identifying other heads of equal support)
def identityLog (i:LogIndex c f) : Head S := Sum.inr (.inr (.inl i))
def weightLog (_H:Cash W s μ L Q o C T R) (i : LogIndex c f) : Test T := fun _ X w=>
    Polar.logMoment X o.a R Q.table (worldZ X R.beta w) (X.input (worldZ X R.beta w)) w i

variable (H)
lemma logTest (i:LogIndex c f) : Kept H (H.supportP (identityLog i)) (weightLog H i) := by
  constructor
  · intro F X X' w v ht hK Z hh hl hV
    have hr : Intake P T X.x R:= ht.symm ▸ H.laws.intake
    have he : Room P S T X.x:= ht.symm ▸ H.laws.data.room
    have hx : ground R T Q.halo X.B {identityLog i}⊆Z := by unfold ground Coat.B; rw [singleton_biUnion,ht]; exact hh
    have hp:= Borough.flops (show Borough X X' Z w v ∅ ∅ R from ⟨hl,(observe _).1 hV,fun _ _=> Iff.rfl⟩) he Q.buys hr o.a W Q.table hx
    simp only [Polar.floating, Finset.prod_singleton,identityLog,Polar.ember,Sum.elim] at hp
    exact Real.exp_injective (sub_left_inj.mp hp)
  · intro E _ F X hx hk V Y w hp hv ht
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    let f i':= weightLog H i F (Art.drive X (V i') (Y i')) (w i')
    have he : Measurable (fun i'=> Real.exp (f i')-1):= bornB X (show ShellAccess S G X.x W X.width o.γ from (by rw [hx,hk]; exact H.laws.data.access)) hr Q.table_exists hp hv ht o.a Q.halo ∅ (identityLog i)
    have hh := Real.measurable_log.comp (f:=fun i'=> Real.exp (f i')-1+1) (he.add measurable_const)
    change Measurable f; simpa only [sub_add_cancel, Function.comp_def,Real.log_exp] using hh
  · intro F X hx hk hp z w
    have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
    have h : ShellAccess S G X.x W X.width o.γ:=by rw [hx,hk]; exact H.laws.data.access
    have he := H.laws.data.funds
    have hy := Stained.fights X z h hr Q.halo ∅ Q.table_exists
      (show 0<o.a*X.t from mul_pos o.large (show Room P S T X.x from hx.symm ▸ H.laws.data.room).fiery)
      (show 4*o.a*X.t<Q.table.radius from (by unfold Coat.t; rw [he.length_eq,hx]; exact H.laws.data.covers)) hp (worldZ X R.beta w) w (identityLog (S:=S) i)
    rw [← Stained.flight X z hr.ready h] at hy
    exact Real.exp_injective (sub_left_inj.mp (show Real.exp _-1=Real.exp _-1 from hy))
  intro F X hx hk hp j b A E _ _ _ V x hq hz hA
  have hr : Intake P T X.x R:= hx.symm ▸ H.laws.intake
  have he : Room P S T X.x:= hx.symm ▸ H.laws.data.room
  have hh:= H.laws.data.funds
  have hw:=mul_pos o.large he.fiery; rw [← hx,← hh.length_eq] at hA
  let X' (t:F.Slice G×Air f G):= X.wrapY t.1; let F' t:=worldZ (X' t) R.beta t.2; let S' k y:= steer (X' k) b (fun i=> prune b (F' k i)) (V y)
  let Y t y:=vary (X' t) (V y); let T' t:= (X' t).input (F' t)
  let K t y:= sweepZ (Y t y) R.beta (S' t y)
  have hv: Zest S' x j := (hq.foreshadow (Y:=Prod.fst) F' hz).1
  let L' : Directions G f→ₗ[ℝ] Air f G := { toFun t:= WithLp.toLp _ (stand t),map_add' _ _:=rfl,map_smul' _ _:=rfl }
  have hK: Zest K x j := (((hv.plusminus (hq.settles (Y:=Prod.fst) he)).scalar (gStep R.beta)⁻¹).replay L'.toContinuousLinearMap)
  refine (hq.logZestR2 (Y:=Prod.fst) T' he S' hv hr hw (show 4*o.a*X.t<Q.table.radius from (by unfold Coat.t; rw [hh.length_eq,hx]; exact H.laws.data.covers)) Q.table_exists i hK).congr ?_
  obtain ⟨p,hF⟩:= hq.sails
  filter_upwards [Silica.nearby X hz hq.lifts hF,hq.brews.1] with y hy hT t
  have ht:= thatch (X' t) hz (V y) o.a W {identityLog (S:=S) i} Q.halo Q.table (show Drivable (X' t) b A (V y) from ⟨hy.good⟩) hw hA hT he hr t.2
  dsimp only at ht
  simp only [Polar.floating, Finset.prod_singleton,identityLog,Polar.ember,Sum.elim] at ht
  exact Real.exp_injective (sub_left_inj.mp ht.symm)
end YM.LocalTaylorR2.Port
