import YM.OPE.Compatible.Passage
import YM.OPE.Compatible.Laws
import YM.Work.B02.Slab

/-!
# Compressed products

Use evaluator for all characters and all their probability mixtures, in
particular for the representing unselected expectation. We work in
operator norm at every stage. This also allows joint testing with no
almost-every-phase loss. All product/correlation statements are for
separated insertions only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cov.Display
open Function Set Filter Table MeasureTheory Survey OS OS.Ground
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
  (U : Spec.Final C f S)
variable {I J B l:Type} [Fintype I] [Fintype J] {φ : Filter l} {T : l → ℝ} {κ t b s c : ℝ}
  {X:l → I → E4} {Y:l → J → E4} {O:l → E4}

abbrev Round := U.α.unselected.algebra

/-- Compression in the true ground algebra, at separated quotient-field inputs. -/
def object (x : I → E4) (p : I → S.Tag) : Round U := viewing U x (Ward.expose ∘ p)

lemma object_sees (r : Viewers U) (x : I → E4) (p : I → S.Tag) (hx : Injective x) :
    glance U r (object U x p) = kernel (spectator U r) x p :=
  (glance_sees U r x (Ward.expose ∘ p) hx).trans (kernel_expose _ _ _).symm

-- use everywhere, not a local non-Banach integral default
instance : CompleteSpace (Round U : Type) := by
  haveI : IsClosed (U.α.unselected.algebra : Set U.α.room.VacuumOp) := isClosed_closure
  letI : CStarAlgebra U.α.unselected.algebra := StarSubalgebra.cstarAlgebra _
  exact inferInstanceAs (CompleteSpace (U.α.unselected.algebra : Type))

lemma object_live (x : I → E4) (hx : Injective x) (p : I → S.Tag) :
    ContinuousAt (fun x => object U x p) x := by
  let t := Ward.expose ∘ p
  let v (y:I→E4) := worded y t
  obtain ⟨s,d,hs⟩ := Spread.Resolution.place_exists ((worded_distinct t).2 hx)
  let c := t ∘ runNames I
  let Y (x:I→E4) := Points.across s (points (x ∘ runNames I))
  have hy : Continuous Y := by unfold Y Points.across points; fun_prop
  have he (x:I→E4) : Word.carry (v x) s = Word.realize c (Y x) := by
    unfold c v worded Word.carry Word.realize
    rw [List.map_ofFn]; rfl
  let V := U.α.room
  let P := U.α.unselected
  have hs : Slab timeAxis d (Word.realize c (Y x)) := he x ▸ hs
  have ho : {y | Slab timeAxis d (Word.realize c y)} = YM.Work.B02.region timeAxis d (Fintype.card I) :=
    Set.ext fun y => YM.Work.B02.in_region d c y
  have ha : {y | Slab timeAxis d (Word.realize c y)} ∈ 𝓝 (Y x) := ho.symm ▸
    (YM.Work.B02.region_open d _).mem_nhds ((YM.Work.B02.in_region ..).1 hs)
  have hb : ContinuousAt (fun x : I → E4 => P.place d (Word.realize c (Y x))) x :=
    ((U.phase.phase.lengths.regular d _ c).continuousOn.continuousAt ha).comp hy.continuousAt
  have hh : ContinuousAt (fun x : I → E4 => P.atom (Word.realize c (Y x)) d) x :=
    continuousAt_const.clm_comp (hb.clm_comp continuousAt_const)
  -- use placement equality near x in the subtype topology
  apply (Topology.IsInducing.continuousAt_iff (Topology.IsEmbedding.subtypeVal).isInducing).mpr
  apply hh.congr
  filter_upwards [open_inj.mem_nhds hx, hy.continuousAt.tendsto.eventually ha] with i hi hp
  have hg := (show Slab timeAxis d (Word.carry (v i) s) from (he i).symm ▸ hp)
  symm
  change (viewing U i t).val = _
  rw [viewing,dif_pos hi, Ground.overline P U.phase.phase.still _ _ s hg]; change P.atom _ _=_; rw [he]

variable (μ : Measure U.α.space.X) [IsProbabilityMeasure μ]
lemma all_live (v : (Round U:Type)) : Integrable (fun i => glance U (some i) v) μ :=
  (U.phase.phase.decomposition.weak v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma mix_contract (v : Round U) : ‖∫ i,glance U (some i) v ∂μ‖ ≤ ‖v‖ :=
  (norm_integral_le_of_norm_le (integrable_const ‖v‖) (Eventually.of_forall fun i => glance_bound U (some i) v)).trans (by simp)

def blend (μ : Measure U.α.space.X) [IsProbabilityMeasure μ] : (Round U:Type) →L[ℂ] ℂ := LinearMap.mkContinuous
  (E:=(Round U:Type))
    { toFun := fun v => ∫ i,glance U (some i) v ∂μ
      map_add' := fun a b => by
        simp_rw [map_add]; exact integral_add (all_live U μ a) (all_live U μ b)
      map_smul' := fun t x => by simp only [map_smul,RingHom.id_apply,integral_smul] }
  1 (fun v => one_mul ‖v‖ |>.symm ▸ mix_contract U μ v)
lemma blend_bound (v : Round U) : ‖blend U μ v‖ ≤ ‖v‖ := mix_contract U μ v
lemma blend_kernel (x : I → E4) (p : I → S.Tag) (hx : Injective x) :
    blend U μ (object U x p) = ∫ i, kernel (spectator U (some i)) x p ∂μ := by
  change (∫ i,_ ∂μ)=_
  simp_rw [← object_sees U _ x p hx]

omit [IsProbabilityMeasure μ] in
lemma blend_ground (v : Round U) : (∫ i, glance U (some i) v ∂U.α.space.μ) = glance U none v :=
  U.phase.phase.decomposition.ground v

/- Short-distance discrepancy -/
def signal (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) (y:J → E4) (q:J→ S.Tag) (a : Tones U) :=
  beam U a r x p o • object U (beside (sole o) y) (beside (sole (title U a)) q)

def drift (k : ℕ) (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) (y:J → E4) (q:J→ S.Tag) : Round U :=
  object U (beside x y) (beside p q) - ∑ a∈ shades (facets U) k,signal U r x p o y q a

lemma drift_reveals (k : ℕ) (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) (y:J → E4) (q:J→ S.Tag)
    (hx : Injective (beside x y)) (hy : Injective (beside (sole o) y)) (v : Viewers U) :
    glance U v (drift U k r x p o y q) = kernel (spectator U v) (beside x y) (beside p q) -
      Cov.insert S (spectator U v) o y q k (trunc U k r x p o) := by
  let V := spectator U v
  let hv := (spectate U v)
  have he i (hi:i ∈ shades (facets U) k) : Cov.insert S V o y q k ((legends U).there k i) =
      kernel V (beside (sole o) y) (beside (sole (title U i)) q) := by
    rw [Catalogue.present _ _ i ((shadows ..).mp hi), Cov.insert,
      lowerOne V (Ward.expose ∘ q) _ _ (spectate_ready U v) hv.laws.toSymmetric hy _ (spectate_respects U v)]
    exact insert_apply S hv.laws.toSymmetric (spectate_respects U v) o y q _ _ hy
  rw [drift,map_sub,map_sum,object_sees U _ _ _ hx]
  unfold trunc
  rw [map_sum]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by
    unfold signal; rw [map_smul,map_smul,object_sees U _ _ _ hy, he i hi]

-- Also formula independent of `insert`
lemma drift_blend (k : ℕ) (r : ℝ) (x : I → E4) (p : I → S.Tag) (o : E4) (y:J → E4) (q:J→ S.Tag)
    (hx : Injective (beside x y)) (hy : Injective (beside (sole o) y)) :
    blend U μ (drift U k r x p o y q) = (∫ i, kernel (spectator U (some i)) (beside x y) (beside p q) ∂μ) -
      ∑ a∈ shades (facets U) k, beam U a r x p o *
        ∫ i, kernel (spectator U (some i)) (beside (sole o) y) (beside (sole (title U a)) q) ∂μ := by
  unfold drift signal
  rw [map_sub,map_sum]
  simp_rw [map_smul,blend_kernel U μ _ _ hy,blend_kernel U μ _ _ hx]; rfl

lemma price_from_viewers (k : ℕ) (p : I → S.Tag) (q : J → S.Tag) (r:l→ℝ) (x:l→ I→E4) (o:l→E4) (y:l→J→E4)
    (hx : ∀ᶠ i in φ, Injective (beside (x i) (y i)) ∧ Injective (beside (sole (o i)) (y i)))
    (hr : Tendsto r φ (𝓝[>] 0))
    (h : ∀ v:l→Viewers U, RateLE φ T (fun i=>
      kernel (spectator U (v i)) (beside (x i) (y i)) (beside p q) -
        Cov.insert S (spectator U (v i)) (o i) (y i) q k (ray U k (x i) p (o i))) κ) :
    RateLE φ T (fun i => drift U k (r i) (x i) p (o i) (y i) q) κ := by
  intro a ha
  let D i v := kernel (spectator U v) (beside (x i) (y i)) (beside p q) -
        Cov.insert S (spectator U v) (o i) (y i) q k (ray U k (x i) p (o i))
  filter_upwards [hx, hr.eventually (p:=fun i => 0 < i) self_mem_nhdsWithin,
    (hr.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds (Signal.period_pos (supplies S) k)),
    universalize (p:=fun i v => ‖D i v‖ ≤ Real.exp (a*T i)) (fun v => h v a ha)] with i hi he hp hh
  apply (glance_contract U (Real.exp_nonneg _)).2; intro v
  rw [drift_reveals U k _ _ _ _ _ _ hi.1 hi.2, trunc_ray U k he hp.le]
  exact hh v
end YM.OPE.Cov.Display
