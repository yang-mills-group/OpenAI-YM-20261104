import YM.FVA2.Generator.Rhythm
/-!
# Determine the diagonal of the position scale response at order one

Hypothesis `P` is the actual `actMark` formula on the position correlations.
Test using the order-one analysis of those same (`Y`,`K`) Wilson fields!
In particular, use a common `Shade.Cut` satisfying `Granted` and sufficiently
small to get the indicated `By` limit (`explicit_limit`). Then use the
diagonal of `going` there (at those spacings and tending to zero from
`Penny.firstFare`), and conclude the asserted diagonal must vanish. See `Qgau`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Prose
open Function Set Filter XSpace XSpace.Trace XSpace.Normalize XSpace.Cirrus XSpace.Structure1 XSpace.Future
open Maxwell FVA2.Scale FVA2.Scale.Level FVA2.Scale.Facets Reg.Point Reg.Token FVA2.Scale.Equator Penny
open scoped Topology BigOperators Classical
-- convergence to explicitly given set of finite prices at input. Generalization of TiltRank's proof.
private lemma medium_limit {I:Type} [Fintype I] {ι:Type} {L:Filter ι} {E: Type} [AddCommGroup E][Module ℝ E][FiniteDimensional ℝ E]
    (b:I→ E)(p:I→Module.Dual ℝ E) (U:∀ x:E,(∑ i,p i x • b i)=x) (s:ι→ I→ Module.Dual ℝ E)(T:ι→ E) (x:E) (H:∀ v i,Tendsto (fun j=> s j i v) L (𝓝 (p i v))) (hx:∀ i,Tendsto (fun j=> s j i (T j)) L (𝓝 (p i x))): By ℝ L T x:=by
    let F:= Fin (Module.finrank ℝ E)→ℝ; let e: E ≃ₗ[ℝ] F:=(Module.finBasis ℝ _).equivFun; let W (p:I→Module.Dual ℝ E)(i:I): F→L[ℝ] ℝ:= LinearMap.toContinuousLinearMap (p i ∘ₗ e.symm.toLinearMap); let Fm(p:I→Module.Dual ℝ E): F→L[ℝ] F:= ∑ i,(W p i).smulRight (e (b i))
    have ht(p:I→Module.Dual ℝ E)(x:E): Fm p (e x)=e (∑ i,p i x • b i):=by simp [Fm,W]
    have he : ∀ i,Tendsto (fun j=> W (s j) i) L (𝓝 (W p i)):=by
       let B:=Module.finBasis ℝ F; let y(k):= (B.coord k).toContinuousLinearMap; have h(f:F→L[ℝ]ℝ): f=∑ k, (f (B k)) • y k:= by
          ext1 x; conv_lhs=> rw [← B.sum_repr x,map_sum]; skip
          rw [_root_.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul, _root_.smul_apply]; exact mul_comm ..
       intro i; rw [h (W p i)]; conv => arg 1; ext j; rw [h (W (s j) i)]
       apply tendsto_finsetSum; intro k _; apply Tendsto.smul_const; exact H (e.symm (B k)) i
    have hp : Tendsto (fun j=> Fm (s j)) L (𝓝 1):=by
       have h0:Fm p=1:=by
          ext1 x; obtain ⟨t,rfl⟩:=e.surjective x; rw [ht,U];rfl
       rw [← h0]; apply tendsto_finsetSum; intro i _; exact (ContinuousLinearMap.smulRightL ℝ F F|>.flip (e (b i))).continuous.continuousAt.tendsto.comp (he i)
    let M:= Fm ∘ s; have hj:Tendsto (fun j=> M j (e (T j))) L (𝓝 (e x)):= by simp_rw [M,Function.comp_apply,ht,map_sum,map_smul]; nth_rw 1 [ ← U x ]; rw [map_sum]; simp_rw [map_smul]; exact tendsto_finsetSum _ fun i _=> (hx i).smul_const _
    have hj0 : (1:F→L[ℝ]F).IsInvertible:=⟨ContinuousLinearEquiv.refl ℝ _,rfl⟩; have hm : Tendsto (fun i=> (M i).inverse) L (𝓝 1):=by
       rw [← show (1:F→L[ℝ]F).inverse = 1 from ContinuousLinearMap.inverse_equiv (.refl ℝ F)]
       exact ((hj0.contDiffAt_map_inverse (n:=1)).continuousAt).tendsto.comp hp
    have he': Tendsto (fun j=> e (T j)) L (𝓝 (e x)):=by
       have h: Tendsto (fun j=> (M j).inverse (M j (e (T j)))) L (𝓝 (e x)):= (Continuous.clm_apply continuous_fst continuous_snd).continuousAt (x:=((1:F→L[ℝ]F),e x))|>.tendsto.comp (hm.prodMk_nhds hj); apply h.congr'
       filter_upwards [hp.eventually (Units.isOpen.mem_nhds (show IsUnit (1:F→L[ℝ]F) from isUnit_one))] with i hi
       have he:= ContinuousLinearMap.isUnit_iff_bijective.mp hi; have hz : (M i).IsInvertible:=⟨ContinuousLinearEquiv.ofBijective (M i) (LinearMap.ker_eq_bot.mpr he.1) (LinearMap.range_eq_top.mpr he.2),rfl⟩; exact hz.inverse_apply_eq.mpr rfl
    intro D; have h:= (D ∘ₗ e.symm.toLinearMap).continuous_of_finiteDimensional.continuousAt.tendsto.comp he'; simpa [Function.comp_def] using h
open Photo
variable {G:Gauge}{n d:ℕ}(g:G.Simple)
structure Sign (G:Gauge)(d:ℕ) where
    n:ℕ
    x: FVA2.Scale.Stage n
    fields : Tags G d n
    real : ℂ→ₗ[ℝ] ℝ
section axes
def row (u:Tags G d n)(v:Point G d n): Module.Dual ℂ (FieldEnd G d):= { toFun F:=lot v F u, map_add' := by intros; rw [map_add];rfl, map_smul' :=by intros; rw [map_smul];rfl }
def staples (p:Sign G d)(v:Point G d p.n): Module.Dual ℝ ( Normalize.Change G d ):= p.real ∘ₗ ( (row p.fields v).restrictScalars ℝ ) ∘ₗ ( Normalize.Change G d ).subtype
abbrev penance (p:Sign G d):= staples p (iris p.x)
private lemma meter_r (v: Stage n)(u:Tags G d n): row u (iris v) = Manifest.response v u:= by ext1 F; exact lots ..
include g
private lemma obtain_sign (d:ℕ): ∃ (v: Finset (Sign G d))(b:v→Normalize.Change G d), ∀ x:(Normalize.Change G d),(∑ i:v,penance i.val x • b i)=x:=by
    obtain ⟨v,b,H⟩:=bought (penance (G:=G) (d:=d)) (fun y hy=> by
       apply Subtype.ext; refine Manifest.sure g y.val y.property (fun n t p=>?_); rw [ ← meter_r ]; apply Complex.ext; exact hy ⟨n,t,p,Complex.reLm⟩; exact hy ⟨n,t,p,Complex.imLm⟩ )
    exact ⟨v,b,fun x=> (H x).symm⟩
end axes
open PowerSeries
variable (Y:Initialize G)
section position
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open Position Position.Axes Arrival MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors Dframe
variable {V: XSpace.Normalize.Store G} (K: Rose.Pick V) (ξ:ℝ) -- at ℝ all
variable (X:Way G d)(q:Cn)(p:Guard G d)
variable (C:Measure.Aim Y K d X)(Q:Tangent q)(B:Base p)(P:actMark p (scaling ξ X) = couple q X)
private lemma take1 (v: Stage n)(t:Tags G d n)(Q:Tangent q): couple q X n v 1 t=X n v 1 t:= by
    let w:=X n v; obtain he:= congr_arg ( PowerSeries.coeff (R:=ℂ) 1 ) ( Reg.Point.moves w t Q.start ); rw [ Reg.Choice.stating_one _ _ Q.start, Q.lead,mul_one ] at he; simp_rw [Reg.Point.story,coeff_mk] at he; exact he
include C B Q P g
omit B Q P g in
private lemma oil : StarGround X:= fun n p=> by ext1 v; exact tendsto_nhds_unique ( C _ p _ v ) ( Rose.conjures0 Y K d v _ p.property )
omit B P C g Q in -- via notices, universal
include Y in
lemma draping (v:Stage n)(p:Tags G d n): iris (posing ξ v) (Penny.Wrt ξ d p) = iris v p:= by
    refine tendsto_nhds_unique ((notices Y d (Wrt ξ d p) _ (posing ξ v).property).comp (Extent.knocks ξ v.val)) ?_ ; exact ( notices Y d p _ v.property ).congr (fun i=> ( Penny.moves ξ Y p i ).symm ) -- Y not included
omit B P Q g in
private lemma drawing : StarGround (scaling ξ X):= fun n p=> by ext1 v; rw [scale_at,oil Y K X C _ _ ]; exact draping Y ξ _ v
lemma lettering (v:Stage n)(u:Tags G d n): checked1 Y V d v.val u-checked1 Y V d (posing ξ v).val (Wrt ξ d u)=lot (scene v.val d) (coeff 1 p) u:= by
    have he:= Manifest.exhibits (scaling ξ X) p 1 ( drawing Y K ξ X C ) one_ne_zero Base.one (fun j hj=>by rw [ show j=0 by omega,B.zero, Base.one.zero ]) v u; rw [ P,take1 _ q v u Q,acts_h, scale_at, show coeff 1 (R:= FieldEnd G d) 1=0 from by simp, sub_zero (coeff 1 p), ← meter_r ] at he; have hY(v:Stage n)(t:Tags G d n): X n v 1 t=checked1 Y V d v.val t:= tendsto_nhds_unique ( C n v 1 t ) ( Rose.conjures1 Y K d g t _ v.property ); rw [ hY, hY ] at he; exact he
-- force the limit explicitly before projecting to diagonal
variable (c:Shade.Cut)(hc:Granted V d c)
def residual (d:ℕ)(p:Guard G d)(B:Base p)(V:Store G) : Normalize.Change G d:=
    let f:= fallFee Y V d c
    (⟨coeff 1 p,B.high _ one_ne_zero⟩: Normalize.Change G d ) + acted d ξ f - f
include hc
private lemma ancestry (t:Stage n)(f:Tags G d n)(h:t.val∈Photo.Good c n)(he:(posing ξ t).val∈Good c n) : Tendsto (fun i: Cirrus.Sample n=> row f (live Y d i 0) (going Y c d ξ i.F.spacing).val) (Gate t.val) (𝓝 (row f (iris t) (residual Y ξ c d p B V).val )):= by
    let L:= fallFee Y V d c; let X':=(Extent.reaches (n:=n) ξ); obtain hp:=( maturation d f _ (structures Y d c) t.val h ).sub ((maturation d (Wrt ξ d f) _ (structures Y d c) (posing ξ t).val he).comp (Extent.knocks ξ t.val) ); have ht:= lettering g Y K ξ X q p C Q B P t f; rw [independent Y V d c hc _ h,independent Y V d c hc _ he, calibrate,calibrate ] at ht; change orderBasic Y d c t.val f+lot (iris t) L.val f - (_+lot (iris (posing ξ t)) L.val (Wrt ξ d f))=lot (iris t) _ f at ht; rw [lotW ξ _ _ (draping Y ξ t)] at ht
    let A:= row f (iris t); have he(A₀ B₀ l l' v:ℂ)(h:A₀+l-(B₀+l')=v) : A₀-B₀= v+l'-l:=by linear_combination h
    have hh : orderBasic Y d c t.val f-orderBasic Y d c (posing ξ t).val (Wrt ξ d f) = A (residual Y ξ c d p B V).val := by apply Eq.trans (he _ _ _ _ _ ht); change _=A (coeff 1 p + turner ξ L.val - L.val); rw [ map_sub A, map_add A ]; rfl
    rw [show row f _ (residual Y ξ c d p B V).val=A _ from rfl,← hh]; refine hp.congr (fun i=>?_); exact bon ξ Y c d i f
omit hc in
set_option maxRecDepth 5000 in
set_option maxHeartbeats 800000 in
lemma explicit_limit (ρ:ℝ)(hρ:0<ρ): ∃ c:Shade.Cut, c.rOut<ρ ∧ Granted V d c ∧ By ℝ Front (fun m=> going Y c d ξ m.spacing) (residual Y ξ c d p B V):= by
    obtain ⟨y,b,u⟩:= obtain_sign g d; let D:=V.survey d; obtain ⟨r,hy,hR,hx,hX⟩:=(show ∀ᶠ a:ℝ in 𝓝[>] 0,(0<a) ∧ a<ρ ∧ (∀ i:Fin D.n, tsupport (D.scope i).t ⊆ Beyond a (D.scope i).n) ∧ ∀ i:y,i.val.x.val ∈ Beyond a i.val.n∧(posing ξ i.val.x).val∈Beyond a i.val.n from by
      have HH {n:ℕ}(t:Stage n):∀ᶠ a:ℝ in 𝓝[>] 0,t.val∈Beyond a n:= ( wishes (K:={t.val}) isCompact_singleton (singleton_subset_iff.mpr t.property) ).mono (fun _ h=> h (mem_singleton _))
      filter_upwards [ self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hρ), eventually_all.mpr (fun i:Fin D.n=> let t:= (D.scope i).t; wishes (K:=tsupport t) t.hasCompactSupport t.tsupport_subset), eventually_all.mpr (fun i:y=> (HH i.val.x).and (HH (posing ξ i.val.x))) ] with a ha hR hT hx; exact ⟨ha,hR,hT,hx⟩ ).exists
    let c:Shade.Cut:=⟨r/2,r,by positivity,half_lt_self hy⟩; refine ⟨c,hR,hx,?_⟩
    let F(m:Mesh)(i:y):= ascend i.val.x.val m; apply medium_limit b (fun i:y=> penance i.val) u (fun m i=> staples i.val (live Y d ( F m i ) 0))
    · intro v i; have hu(f): Tendsto (fun j=> live Y d j 0 f) (Gate i.val.x.val) (𝓝 (iris i.val.x f)):= notices Y d f i.val.x.val i.val.x.property
      have he : Tendsto (fun j=>row i.val.fields (live Y d j 0) v.val) (Gate i.val.x.val) (𝓝 ( row i.val.fields (iris i.val.x ) v.val )):= by unfold row; simp only [LinearMap.coe_mk,AddHom.coe_mk, lots]; exact tendsto_finsetSum Finset.univ (fun i _=> hu _)
      exact i.val.real.continuous_of_finiteDimensional.continuousAt.tendsto.comp ( he.comp ( points_at _ ) )
    intro i; exact i.val.real.continuous_of_finiteDimensional.continuousAt.tendsto.comp (( ancestry g Y K ξ X q p C Q B P c hx i.val.x i.val.fields (hX i).1 (hX i).2 ).comp ( points_at _ ))
omit hc in
lemma diary : diag (coeff 1 p)=0:= by
    obtain ⟨c,hc,H,h⟩:= explicit_limit g Y K ξ X q p C Q B P 1 zero_lt_one; let T:= residual Y ξ c d p B V; have he: diag T.val=diag (coeff 1 p):= by
       let f:= ( fallFee Y V d c ).val; change diag (coeff 1 p+turner ξ f-f)=_; rw [ _root_.map_sub (Level.diag (G:=G) (d:=d)), _root_.map_add (Level.diag (G:=G) (d:=d)), Penny.diag_version ]; exact (add_sub_cancel_right (coeff 1 p |> Level.diag) (Level.diag f) |>.trans rfl)
    have hx(f:Module.Dual ℂ (FieldEnd G d)) : f (diag (coeff 1 p))=0:=by
       obtain he':= Penny.firstFare ξ (show Tendsto Mesh.spacing Front (𝓝 0) from frontier.endpt) (Eventually.of_forall fun i:Mesh=> i.positive) Y c d f; rw [map_zero] at he'; let g:= ((f ∘ₗ (Level.diag (G:=G) (d:=d))).restrictScalars ℝ) ∘ₗ (Normalize.Change G d).subtype; rw [← he]; apply Complex.ext; exact tendsto_nhds_unique (h (Complex.reLm ∘ₗ g)) ( Complex.continuous_re.continuousAt.tendsto.comp he' ); exact tendsto_nhds_unique (h (Complex.imLm ∘ₗ g)) ( Complex.continuous_im.continuousAt.tendsto.comp he' )
    let b:= Module.finBasis ℂ (FieldEnd G d); apply b.equivFun.injective; rw [ map_zero ]; exact funext fun i=> hx ( b.coord i )
end position
end YM.FVA2.Generator.Prose

