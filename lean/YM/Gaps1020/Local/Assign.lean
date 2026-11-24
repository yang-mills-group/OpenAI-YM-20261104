import YM.Gaps1020.Local.ThermalPower
/-!
# Exponent Taylor orders under the shared conditional integral

Reassembly of the exp-power moments holds as an identity of germs on
`Healthy`. Off masked domain our choice will define the residual by exact
subtraction, so need no integrability claims about the extensions there.
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

abbrev Assign (p:Molecule S)(M:ℕ):= ↑p → Fin (M+2)
def assignment (p:Molecule S){M:ℕ}(A:Assign p M):MulData p:=fun i=> YM.GapsLocal.ExpShares.share M (A i).val
def degree (p:Molecule S){M:ℕ}(A:Assign p M):ℕ:= ∑ i,(A i).val

section integrator
variable (p:Molecule S){Ξ:Utopia H j v d r C' χ}
    (h:HasClutch Ξ A) (hΘ:Oboe H j v B k A b Ξ) (hX:X.x=s) (hk:X.width=o.K) (he:X.χ=χ) (hV:Mode V x j v) (hv: V x=X.V)

lemma assembleVertex (X:Coat T F)(M:ℕ)(z:Air f G) (R:Rep G f) :
    ∑ i:Assign p M, weighted p (assignment p i) R Ñ W a l X z = Polar.floating X a R W Ñ z (own p) l p := by
  unfold weighted; rw [← Finset.mul_sum]; nth_rw 2 [← mul_one (floating X a R W Ñ z (own p) l p)]
  congr 1
  exact Eq.trans (Fintype.prod_sum (f:=fun i (q:Fin (M+2))=> YM.GapsLocal.ExpShares.share M q (row p R Ñ W a l X z (i:↥p)))).symm (by simp only [YM.GapsLocal.ExpShares.shares_literal,Finset.prod_const_one])
include hΘ hX hk he hV hv
lemma barsTogether (hM : X.manifest)(M:ℕ) :
    let I:=podium S G (H.unionP p) (radiusB s)
    (fun i=> ∑ q:Assign p M, weightedBars p (assignment p q) I (vary X (V i)) R Q.table W o.a Q.halo) =ᶠ[𝓝 x]
       fun i=> bars I (vary X (V i)) p R Q.table W o.a Q.halo := by
  intro I; have hh:= hΘ.flow F X hX he hk hM E V x hv hV
  let g q v:=weightedRhythm (edgesM S (H.unionP p) (radiusB s)) X (V v) A Q.table p (assignment p (q:Assign p M)) R W o.a Q.halo
  have ht q:= unfoldBars H hX hM hk hh hΘ.conduit hΘ.mode p (assignment p (q:Assign p M)) (fun _=> share_contDiff ..)
  have hZ (q:Assign p M) : ∀ᶠ v in 𝓝 x, Integrable (g q v) ((F.order G).prod X.dice):= (multiplied H hX hM hk hh hΘ.conduit hΘ.mode p (assignment p q) (fun _=> share_contDiff ..) (edgesM S (H.unionP p) (radiusB s))).2
  filter_upwards [eventually_all.mpr ht, eventually_all.mpr hZ,chutes H hX hM hk hh hΘ.conduit hΘ.mode p] with v hT hz hy
  rw [Finset.sum_congr rfl (fun q _=> hT q), hy, ← MeasureTheory.integral_finsetSum _ (fun q _=> hz q)]; apply integral_congr_ae; filter_upwards with y
  unfold g; unfold weightedRhythm rhythm recoil weightedRecoil; rw [← Finset.mul_sum]; rw [assembleVertex]
variable (hF:(roster p).flags=∅)(hP:Healthy (Pressure.temp s) (H.unionP p) X.V)
include hF hP
lemma fringeTogether (M:ℕ) :
    (fun i=>∑ q:Assign p M, weightedFringe (vary X (V i)) p (assignment p q) R Q.table W o.a Q.halo)=ᶠ[𝓝 x] fun i=> fringe (vary X (V i)) W o.a p R Q.table Q.halo := by
  let g i:=(planted X p).taggedL i
  have hh (i:S.Choices):= barsTogether p hΘ (X:=g i) hX hk he hV hv (show (g i).manifest from planted_valid X p) M
  filter_upwards [eventually_all.mpr hh,eventually_all.mpr (fun q:Assign p M=> weightedRainbow p (assignment p q) hΘ hX hk he hF hP hV hv),rainbow p hΘ hX hk he hF hP hV hv] with i hi ha hA
  rw [hA,Finset.sum_congr rfl (fun t _=>ha t)]; unfold weightedShelter shelter; rw [show (vary X (V i)).B=radiusB s from congr_arg _ hX]; split
  next =>
    unfold weightedSeat seating Pond.likely; dsimp only; rw [← Finset.mul_sum, Finset.sum_comm]; apply congr_arg
    apply Finset.sum_congr rfl; intro j hj
    let P k:= preps (vary X k) (roster p)
    have ha q : weightedBars p (assignment p (q:Assign p M)) (podium S G (H.unionP p) (radiusB s)) ((P (V i)).taggedL j) R Q.table W o.a Q.halo=_ := (weightedSpices p (assignment p q) H X hX (V i) (V i) (fun _ _ _=>rfl) hP hF j).symm
    rw [show ground R T _ (radiusB s) p=H.unionP p from rfl,Finset.sum_congr rfl fun q _=>ha q, hi j]; exact spices p H X hX (V i) (V i) (fun _ _ _=>rfl) hP hF j
  next => simp
omit hF -- bars again

variable (hlog : HeadsAreLog p)(ht:troupe T R Q.halo (radiusB s) p)
    (hD:Ac.Spark H.supportP p)(hm:H.shapeW p ≤ ℓ) (hρ: charge Q L s r j ℓ ≤ ρ⁻¹) (hp:2 ≤ ρ)
    (π:Assign p M)

def ratesheet (p:Molecule S) {M:ℕ} (π:Assign p M)(j:ℕ)(ρ:ℝ):= (∏ i:↥p,overhead j M*(ρ⁻¹)^((π i).val-1)) * (1+(1+p.card:ℝ))^j
include h hlog ht hm hD hρ hp
lemma tentsPower (hM : X.manifest) :
    Brush j (ratesheet p π j ρ * (B*Ξ.meant p k)) 1
       (fun y:E=> weightedBars p (assignment p π) (podium S G (H.unionP p) (radiusB s)) (vary X (V y)) R Q.table W o.a Q.halo) x:= by
  have hZ:=hΘ.flow F X hX he hk hM E V x hv hV
  let I:=edgesM S (H.unionP p) (radiusB s); let t:=ratesheet p π j ρ; have hT:0≤t:= by unfold t ratesheet; exact mul_nonneg (Finset.prod_nonneg (fun i _=> mul_nonneg (zero_le_one.trans (overhead_bound j M)) (by positivity))) (by positivity)
  obtain ⟨f,hf,hB,hY⟩:= hΘ.delta.tents E F X V x p he hM hX hk (hX.symm ▸ hP) ht hD hV hv
  let Y u i:= weightedRhythm I X (V u) A Q.table p (assignment p π) R W o.a Q.halo i
  have he' : ∀ i, Brush j (t*f i) 1 (fun u:E=> Y u i) x:= by
    intro y
    have ht k:= vertex (X:=X.wrapY y.1) h hX hk he hV hv p hlog ht hP hm hρ hM y.2 k
    let F i v:= row p R Q.table W o.a Q.halo (vary (X.wrapY y.1) (V v)) (course (X.wrapY y.1) A R.beta y.2 (V v)) (i:↥ p)
    let f' (i:↥ p) := overhead j M*ρ⁻¹^((π i).val-1)
    have hv i : Brush j (f' i) 1 (fun v:E=> assignment p π i (F i v)) x:= brush_share hp (π i) (ht i)
    unfold Y; simp_rw [absorb]
    apply (((hY y).paints (Brush.all_prod (univ:Finset (↥p)) _ _ _ (fun i _=> hv i))).trim).climb _ le_rfl
    unfold t ratesheet; simp [f']; ring_nf; rfl
  -- no unattested assumptions on neighborhood summability
  apply (((multiplied H hX hM hk hZ hΘ.conduit hΘ.mode p (assignment p π) (fun _=>share_contDiff ..) I).1.buds (fun i=>t*f i) (hf.const_mul t) zero_le_one ?_ (Filter.Eventually.of_forall he'))).shimmy (unfoldBars H hX hM hk hZ hΘ.conduit hΘ.mode p (assignment p π) (fun _=>share_contDiff ..))
  rw [MeasureTheory.integral_const_mul]; exact mul_le_mul_of_nonneg_left hB hT
include hF
lemma fringePower : Brush j (ratesheet p π j ρ * (B*Ξ.meant p k)) 1
    (fun i:E=> weightedFringe (vary X (V i)) p (assignment p π) R Q.table W o.a Q.halo) x := by
  apply Brush.shimmy _ (weightedRainbow p (assignment p π) hΘ hX hk he hF hP hV hv)
  unfold weightedShelter; simp_rw [show ∀ y,(vary X y).B=radiusB s from fun y=> congr_arg _ hX,if_pos (show Ac.Spark (areas R T Q.halo (radiusB s)) p ∧ troupe T R Q.halo (radiusB s) p from ⟨hD,ht⟩)]
  let P t:= preps (vary X (V t)) (roster p)
  let A i v:= weightedBars p (assignment p π) (podium S G (H.unionP p) (radiusB s)) ((P v).taggedL i) R Q.table W o.a Q.halo
  apply Captain.avgBrush A; intro i
  let X' := (planted X p).taggedL i
  exact (tentsPower (X:=X') p h hΘ hX hk he hV hv hP hlog ht hD hm hρ hp π (planted_valid X p)).shimmy (Eventually.of_forall fun j=> (weightedSpices p _ H X hX (V j) (V j) (fun _ _ _=>rfl) hP hF _).symm)
end integrator
end YM.ConnectedActivityE6.Blaze.Thermal1020
