import YM.Gaps1020.Local.Germ
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel
/-!
# Buying the thermal Taylor terms at a joint log leaf

A shape limit retains the true path/molecule lengths. No reanalyticity of
the input E on field charts is assumed: it enters as a held exponent vertex
subject to the physical eligibility and profile cutoffs. A weighted sheet
here has integer exponent-power allocation (including error slots). The
conditional kernel with full argument costs is paid on the product of vertex
functions *together*, not a product of separate integral bounds.

For warning heads we will not buy this Taylor charge. Instead exclude those
leaves with an exceptional estimate at arbitrary order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

-- A path witness extracted along with the Oboe in the enhanced construction.
-- All parameters shared so the conditional angular prices can be multiplied.
-- Purchase is after L, by the same Clutch and FlareW proofs.
def HasClutch (Ξ : Utopia H j v d r C' χ) (A:ℝ) : Prop := -- keep dependence via its type
    let _:=Ξ.goalsL
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F:Forest S.ratio) (X:Coat T F)
      (U:E→ Config G c) (x:E) (z:Air f G), X.x=s→ X.width=o.K→ X.χ=χ → X.manifest → U x=X.V → Mode U x j v →
        ∃ u:E→Directions G f, Clutch X z o.a R.beta d x j U u (fun y=>course X A R.beta z (U y))

section brush
variable {Ξ:Utopia H j v d r C' χ}
variable (h:HasClutch Ξ A) (hΘ:Oboe H j v B k A b Ξ)
variable (hX:X.x=s) (hk:X.width=o.K) (he:X.χ=χ) (hV:Mode V x j v) (hv: V x=X.V)
variable (p : Molecule S)
-- no warning, no packet, no forced fine label.
def HeadsAreLog (p:Molecule S):Prop:= ∀ i∈p, ∃ t: LogIndex c f,i=Sum.inr (.inr (.inl t))
lemma notWarning_isLog {p : H.ThinP} (he:∀ i∈p.val, ∃ u : LogIndex c f ⊕ WarningAt c f,i = Sum.inr (.inr u))
    (hp:blaze p.val=∅) : HeadsAreLog p.val := by
  intro i hi; obtain ⟨t|t,rfl⟩:= he i hi
  · exact ⟨t,rfl⟩
  have hh : t∈blaze p.val := mem_toRight.mpr (mem_toRight.mpr (mem_toRight.mpr hi)); rw [hp] at hh; simp at hh

def charge (Q:ConnectedActivityE6.Target G P)(L:Side)(s r:ℝ)(j:ℕ)(ℓ:ℝ):= Q.goal L s * (1+r*(2*ℓ))^j

variable (hlog : HeadsAreLog p)(ht:troupe T R Q.halo (radiusB s) p)
    (hP:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hm:H.shapeW p ≤ ℓ) (hρ: charge Q L s r j ℓ ≤ ρ⁻¹) -- shape bounded by survivor cap
include h hX hk he hV hv hlog ht hP hm hρ
lemma vertex (hM:X.manifest)(z:Air f G) (i:↑p) :
    Brush j ρ⁻¹ 1 (fun y:E=> row p R Q.table W o.a Q.halo (vary X (V y)) (course X A R.beta z (V y)) i.val) x := by
  let w y:=course X A R.beta z (V y)
  obtain ⟨u,hu⟩:= h E F X V x z hX hk he hM hv hV
  let c i:= Ξ.tag i; let a(i:Head S):= spanW T R X.B Q.halo i
  have hQ:=H.laws.data
  have he (i:Head S)(hi:i∈p) : Brush j (c i) (r*a i) (fun y=> row p R Q.table W o.a Q.halo (vary X (V y)) (w y) i) x := by
    have hT:= Ξ.stream E _ X V u w x z hX hk he hM hV hu (own p) i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hi) (show Healthy (Pressure.temp X.x) (H.unionP p) X.V from hX.symm ▸ hP))
    apply Brush.shimmy (f:=fun y=> ember (vary X (V y)) o.a R W Q.table (u y) (X.input (worldZ X R.beta z)) (w y) (own p) Q.halo i)
    · unfold c Utopia.tag
      rw [← show X.B=radiusB s from congr_arg _ hX]; exact hT
    filter_upwards [hu.patch] with y hy; unfold row; rw [show worldZ (vary X (V y)) R.beta (w y)=u y from hu.moving y]
    exact (plastic (X:=vary X (V y)) hy hu.pulse).reeled (hX.symm ▸ hQ.room) W Q.table (own p) Q.halo (hX.symm ▸ H.laws.intake) i _
  obtain ⟨i,hi⟩:=i
  obtain ⟨u,rfl⟩:= hlog i hi; let i : Head S:=Sum.inr (Sum.inr (Sum.inl u))
  have hD (i:Head S) (hi:i∈p) : 0≤r*a i := (he i hi).pos
  have hr:0 < r:=zero_lt_one.trans_le Ξ.active
  apply ((he _ hi).trim).climb _ le_rfl
  have hα:0≤Q.relative:=by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  have hL : c i ≤ Q.goal L s:= Ξ.uses.atom hα Q.usable.le (.inr (.inl u)) (exChart ..)
  have hM' : r*a i≤ r*(2*ℓ):= by
    apply le_trans (single_le_sum (f:=fun i=> r*a i) hD hi)
    rw [← mul_sum]; apply mul_le_mul_of_nonneg_left _ hr.le
    unfold a; rw [show X.B=radiusB s from congr_arg _ hX]
    exact (Silica.Utopia.worthy p ht).trans (mul_le_mul_of_nonneg_left hm (by norm_num))
  refine le_trans (mul_le_mul hL (pow_le_pow_left₀ (add_nonneg zero_le_one (hD i hi)) (by linarith only [hM']) j) (pow_nonneg (add_nonneg zero_le_one (hD i hi)) _) ((Ξ.tagged i).trans hL)) hρ
omit hV hv hX hk he hP
include hΘ
-- The exponent is real logMoment, not a symbolic head weight. For bar evaluation
-- the common manifest/coarse field receipt sees e = exp(y) - 1. This also
-- holds on the auxiliary Haar and Air arguments at the center, even if a
-- profile is at its boundary. Used to identify *all* power moments relative
-- to that (fixed beta) step. No analyticity of profile values imported.
theorem vertex_value {X : Coat T F}
    (hX':X.x=s) (hk':X.width=o.K) (he':X.χ=χ)(hM:X.manifest) (hP':Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hVV : 0 ≤ v) (hp : 2≤ρ)(i:LogIndex c f)(hi:Sum.inr (Sum.inr (Sum.inl i))∈ p)(z:Air f G) (d:ℕ):
    let u:=worldZ X R.beta z; let y:=Polar.logMoment X o.a R Q.table u (X.input u) z i
    let e:=row p R Q.table W o.a Q.halo X z (.inr (.inr (.inl i)))
    e = Real.exp y-1 ∧ |e|≤2/3 ∧ e * keep (d+1) e=y^(d+1)/(d+1).factorial:=by
  intro u y e
  let w (_:ℝ):=X.V
  have hw : Mode w 0 j v:= ⟨hVV,fun i=> a_oneB G _ hVV⟩
  have hE := vertex (x:=(0:ℝ)) h hX' hk' he' hw rfl p hlog ht hP' hm hρ hM z ⟨_,hi⟩
  have hT : |e| ≤ 2/3:=by
    have hy := hE.bound; unfold w at hy
    rw [home X hΘ.conduit z H.laws.intake.positive,show vary X X.V=X from rfl] at hy
    apply hy.trans; apply le_trans (b:=1/2) (by rw [one_div]; exact inv_anti₀ (by norm_num) hp) (by norm_num)
  exact ⟨rfl,hT,open_keep rfl hT _⟩
end brush
end YM.ConnectedActivityE6.Blaze.Thermal1020
