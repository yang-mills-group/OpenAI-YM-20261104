import YM.UVExt.ProbeRhythm

/-!
## Open domination near held support probes for Angular differentiated contour

No uniformity in volume is asserted for this step. The price at the point, unlike the neighborhood used to justify the derivative, must be much sharper. Common real center q and likelihood change. -/
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2600000
noncomputable section
namespace YM.UVExt.EnergyRay.Thermal.Core
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Finset MeasureTheory Matrix Tree
open Push Push.AbsoluteSums Precision ConnectedActivityE6 Mask Coat Raw ConnectedActivityE6.Blaze Silica Vine Flux Polar
open Eider Poll Work.F03 Push.SectorMeasure Push.SectorMeasure.Oriented
open SliceRows
open scoped Topology InnerProductSpace ContDiff BigOperators Classical

variable {G:Gauge} {c f L:Side} {S: StepData c f} {T:Tube G S} {F:Tree.Forest S.ratio} {P:Teller G}
    (X:ConnectedActivityE6.Coat T F) (R:Rep G f) (q:ℝ) (Y:F.Slice G) (Z:Air f G) {E:Type}
    [NormedAddCommGroup E][NormedSpace ℝ E] (V:E→Config G c) (a:ℝ)
variable {W η μ v g σ θ δ:ℝ} {I:Finset (Bond f)} {Ñ:ChartRatio G} {l n:ℕ} {Q : YM.ConnectedActivityE6.Target G P} {x:E} {o : Target.Order G W}
variable (V₀:Set ℝ) (d : ℝ) (H :(r:ℝ) → r∈V₀ → Cash W X.x μ L Q o g T (scaled R r))
-- Here Cash's fourth parameter c is Step length? original Cash W x μ L Q etc; we use c Side in previous monolith_real inadvertently, should be L=S.patch.L not c. generalize all!
variable (hq : q∈V₀)(hs:V₀⊆Set.Ioi 0) (A : Glass P X V x n W) (hχ:X.width=o.K) (hΘ:X.manifest) (hβ:0<R.beta) (hv : Canary G a v)
local notation "Yₕ" ys:max => X.wrapY ys
local notation "Cₕ" ys:max us:max => vary (X.wrapY ys) (V us)
local notation "cashRef" => (H q hq)
local notation "Body₀" => F.Slice G × Air f G
set_option quotPrecheck false
local notation "m₀" => (F.order G).prod X.dice

set_option linter.unusedSectionVars false in
theorem meristem_complex {E F α : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace α] [FiniteDimensional ℝ E]
  [TopologicalSpace.PseudoMetrizableSpace F] {x:E} {k:ℕ} {f:E→α→F} {μ:Measure α} (hM:∀ᶠ y in 𝓝 x, StronglyMeasurable (f y))
  (p : ∃ B:α→ℝ, Integrable B μ ∧ ∀ᶠ y in 𝓝 x,∀ u, Brush k (B u) 1 (fun y=>f y u) y) : Meristem f x μ k ∧ ∀ᶠ y in 𝓝 x, Integrable (f y) μ := by
  obtain ⟨B,hF,hP⟩:=p
  constructor
  · obtain ⟨O,hS,hO,hx⟩:= _root_.mem_nhds_iff.mp (hP.and hM)
    have ht (i:E) (hi:i∈O) : (∀ v, Brush k (B v) 1 (fun t=>f t v) i) ∧ StronglyMeasurable (f i) := hS hi
    refine ⟨O,hO.mem_nhds hx,ae_of_all _ (fun _ t h=>(ht t h).1 _ |>.1),fun j hj=> ⟨B,hF,fun y hy=> ?_,ae_of_all _ fun i y hy=>?_⟩⟩
    · exact (Meristem.legs (f:=Function.swap f) hO (fun i t h=> ((ht t h).1 i).smooth) (fun i hi=> (ht i hi).2) hj hy).aestronglyMeasurable
    exact (Brush.offer.1 ((ht _ hy).1 i)).inside j hj
  filter_upwards [hP,hM] with t hp ht; exact hF.mono' ht.aestronglyMeasurable (ae_of_all _ fun i=> (hp i).bound)

def clipping (t:Body₀) u := veer X R q t.1 t.2 (V u) a
def swerve (t:Body₀) u := take X R q t.1 t.2 (V u) a
def inversion ν (t:Body₀) u := orbitC X R q t.1 t.2 (V u) a ν
def gaussField ν (t:Body₀) u := swept X R q t.1 t.2 (V u) a (scaled R ν).beta
local notation "clipper" => clipping X R q V a
local notation "inverseP" => inversion X R q V a
local notation "rawP" => gaussField X R q V a
local notation "driverP" => swerve X R q V a
local notation "clipProbe" zz "|" aa "|" vv => (rod (k:=k) (η:=η) (W:=W) (Ñ:=Ñ) (l:=l) X R q (Prod.fst aa) (Prod.snd aa) (V vv) a)
def inputHeld (t:Body₀):= (Yₕ (t.1)).input (key X R q t.1 t.2)
local notation "inputZ" => inputHeld X R q

include H in lemma realCost_propagates (p : ℝ) (hr:p∈V₀) : 0< (scaled R p).beta := (H p hr).laws.intake.positive
include H hs A hχ hv -- need hq local clean
lemma clipping_terms : Zest (driverP ∘ fun _:Body₀=> (Y,Z)) x n ∧ Zest clipper x n ∧ ∀ i, Zest (fun t u=> driverP t u i-key X R q t.1 t.2 i) x n := by
   let v(t:Body₀) i := key X R q t.1 t.2 i
   have ht i : Zest (fun z u=> driverP z u i-key X R q z.1 z.2 i) x n := by
        have he:=A.foreshadow (Y:=Prod.fst) v hv
        have he' := he.2 i|>.1
        apply he'.congr (Eventually.of_forall fun (u:E) (t:Body₀)=>?_)
        unfold swerve take steer fleece; simp [v]; rfl
   exact ⟨Zest.folds (f:=driverP ∘ (fun _:Body₀ => (Y,Z))) (x:=x) fun i=>
       (((ht i).via (fun _:Body₀=> (Y,Z))).together (Zest.still (v (Y,Z) i))).congr (Eventually.of_forall (fun y z=> sub_add_cancel _ _)),
       ((A.foreshadow (Y:=Prod.fst) v hv).1),ht⟩
include hq
lemma orbit_terms (ν : ℝ) : Zest (inverseP ν) x n ∧ Zest (rawP ν ∘ fun _ : Body₀=> (Y,Z)) x n := by
   have hh:= clipping_terms X R q Y Z V a V₀ H hs A hχ hv
   let B:= (scaled R ν).beta
   let X'(t:Body₀) := X.wrapY t.1
   let UW (t:Body₀) y:= voltage (vary (X' t) (V y))
   have hv' : Zest UW x n := A.settles (Y:=Prod.fst) (cashRef).laws.data.room
   let K : Directions G f →ₗ[ℝ] Air f G := { toFun p:= WithLp.toLp 2 (stand p), map_add' _ _:=rfl, map_smul' _ _:=rfl }
   have he {u'} (hw:Zest u' x n) := ((hw.plusminus hv').scalar (gStep B)⁻¹).replay K.toContinuousLinearMap
   exact ⟨he hh.2.1, ((((hh.1.plusminus (hv'.via fun _:Body₀=> (Y,Z))).scalar _).replay K.toContinuousLinearMap))⟩

local notation "Tᴵ" => lensS I G
local notation "center₀" t:max i:max j:max=> densityCore (I:=I) X R q (Prod.fst t) (Prod.snd t) (V i) j
local notation "eq₀" t:max tt:max j:max i:max => realProbe (I:=I) X R q (Prod.fst t) (Prod.snd t) (V i) a j
lemma quartz_cast (j l : Tᴵ) : ContDiffAt ℝ n (fun i=>Pond.circuit Tᴵ (vary X (V i)).relating j l) x := A.relate j l
include hΘ
lemma quartz_here : (Pond.circuit Tᴵ X.relating).PosDef := (((cashRef).laws.data.localP _ _ rfl hχ hΘ).sails.fullC.submatrix Subtype.val_injective)

lemma reservoir : ∀ᶠ y in 𝓝 x,∀ z : Body₀, ContDiffAt ℝ (n:WithTop ℕ∞) (fun (x:E) => center₀ z x a) y := by
   let U i := (Pond.circuit Tᴵ (vary X (V i)).relating)
   have hx : U x=Pond.circuit Tᴵ X.relating := by unfold U; rw [A.lifts]; rfl
   have ht : (U x).PosDef := hx ▸ quartz_here X R q V a V₀ H hq hs A hχ hΘ hv
   have hG i j := Blaze.jetBack (A:=U) (fun i j=>quartz_cast X R q V a V₀ H hq hs A hχ hv i j) (isUnit_iff_ne_zero.mpr ht.det_pos.ne') i j
   have hH: ∀ᶠ y in 𝓝 x, ∀ i j,ContDiffAt ℝ n (fun y=>(U y)⁻¹ i j) y := eventually_all.mpr fun i=> eventually_all.mpr fun j=> (hG i j).eventually (by simp)
   let v z u:= Pond.swim Tᴵ (course (X.wrapY (Prod.fst (z:Body₀))) a (scaled R q).beta z.snd u)
   have hp:= (A.towers (Y:=Prod.fst) Prod.snd (cashRef).laws.data.room hv I (cashRef).laws.intake.positive).2
   have ht(t:E) (z:Body₀) (j:Tᴵ) (h:Brush n 1 1 (fun _ : Unit=> (1:ℝ)) ()) := h
   filter_upwards [hH, hp.post.choose_spec.2] with y hy h z
   let bb:=gStep R.beta; let bc:=gStep (scaled R q).beta
   have he:ContDiffAt ℝ (n:WithTop ℕ∞) (v z ∘ V) y:= ((h z).smooth.add (contDiffAt_const (c:=Pond.swim Tᴵ z.snd))).congr_of_eventuallyEq (Eventually.of_forall fun y'=>(sub_add_cancel (v z (V y')) _).symm)
   let p' y:= Pond.swim Tᴵ (rawP 1 z y)
   have hh: ContDiffAt ℝ n p' y:=by
      have hp' (i:E) : p' i= (bb⁻¹*bc) • v z (V i):= by
            change Pond.swim _ (WithLp.toLp _ (stand ((gStep (scaled R 1).beta)⁻¹ • (_-voltage _))))= _
            rw [scaled_one,mul_smul]; unfold v course; dsimp only; change _=Pond.swim Tᴵ (WithLp.toLp 2 (stand (bb⁻¹ • (bc • (bc⁻¹ • (_-voltage _))))) )
            rw [smul_inv_smul₀ (show bc≠0 from (inv_pos.mpr (Real.sqrt_pos.mpr (show 0<(scaled R q).beta from (H q hq).laws.intake.positive))).ne')]; rfl
      rw [show p'=(fun i=> (bb⁻¹*bc) • v z (V i)) from funext hp']; exact ContDiffAt.smul (𝕜':=ℝ) (contDiffAt_const (c:=bb⁻¹*bc)) he
   let N(j:Tᴵ):= (EuclideanSpace.proj (𝕜:=ℝ) (ι:=↥Tᴵ) j)
   unfold densityCore; rw [(by rw [scaled_one] : R.beta=(scaled R 1).beta)]; change ContDiffAt _ _ (fun i=> - Gaussian.value (U i) (Pond.swim _ (rawP 1 z i))) y -- defeq? scaled 1 not defeq R; rewrite
   unfold Gaussian.value dotProduct; apply ContDiffAt.neg; refine (ContDiffAt.sum fun i hi=>?_).div_const _
   refine ContDiffAt.mul ((N i).contDiff.contDiffAt.comp y hh : ContDiffAt _ _ (N i ∘ p') y) ?_
   unfold mulVec dotProduct; exact ContDiffAt.sum fun j _=> (hy i j).mul ((N j).contDiff.contDiffAt.comp y hh : ContDiffAt _ _ (N j ∘ p') y)

include H hΘ hv hχ
lemma prism (j:ℝ) (hj:j∈V₀) : let m := m₀
    ∃ M:Body₀→ℝ,Integrable M m ∧ ∀ᶠ y in 𝓝 x,∀ z, Brush n (M z) 1 (fun i=> eq₀ z a j i) y := by
  intro m
  let hE:= H j hj; let N:=Tᴵ; let U i:=Pond.circuit N (vary X (V i)).relating; let B(t:Body₀):=X.wrapY t.1
  let Z:Body₀ → Air f G:=fun z=>z.2; let θ:=j/q; have hθ:0<θ:=div_pos (hs hj) (hs hq)
  let s t:=Real.sqrt θ • Z t; let z t:= Pond.swim N (s t); let K t i:= Pond.swim N (course (B t) a (scaled R j).beta (s t) (V i)); have hx: U x=Pond.circuit Tᴵ X.relating := by unfold U; rw [A.lifts]; rfl
  have ht : (U x).PosDef := hx ▸ quartz_here X R q V a V₀ H hq hs A hχ hΘ hv
  have hv' := (own_mat ((H _ hq).laws.data.localP _ _ rfl hχ hΘ).sails I)
  have hS := Control.lower_inverse hv'.relented hv'.weather.1.le hv'.fuel hv'.symmetry hv'.ground hv'.down.le hv'.initial.1
  have hU := A.towers (Y:=Prod.fst) s hE.laws.data.room hv I hE.laws.intake.positive
  -- room not intake
  obtain ⟨Q,hQ,h,h'⟩:= winglet (Z:=z) (V:=K) ht (hx.symm ▸ hS) (inv_pos.mpr hv'.fuel)
     (fun i j=> A.relate i.val j.val) hU.2
  let v z' := Q ((Real.sqrt θ:ℝ) • z')
  let M(t:Body₀):= Gaussian.tilt (Pond.circuit N X.relating) θ (Pond.swim N (Z t)); let f u:= M u * Q (z u)
  have hF : Integrable (fun z'=>Gaussian.tilt (Pond.circuit N X.relating) θ z' * v z') (sweep (U x)):=by
      apply Integrable.congr (g:=(fun z'=>_)) (Gaussian.integrable_tilt (U x) ht θ hθ (fun y=> (Q y : ℂ)) (Complex.measurable_ofReal.comp hQ) h.ofReal |>.re)
      unfold v; rw [hx]; exact ae_of_all _ fun y=>by change ((_ * _ : ℂ)).re=_; rw [←Complex.ofReal_mul]; rfl
  have hP : MeasurePreserving (fun t=> Pond.swim N (Z t)) m (sweep (U x)) := hx.symm ▸ ((Pond.orbit ((cashRef).laws.data.localP _ _ rfl hχ hΘ).sails.fullC.posSemidef N).comp (show MeasurePreserving Z m X.dice from MeasureTheory.measurePreserving_snd))
  have hm : Measurable (Gaussian.tilt (U x) θ) := by unfold Gaussian.tilt; have := Gaussian.value_cont (U x); fun_prop
  have hb: Integrable f m := hP.integrable_comp (by rw [hx] at hm; exact (hm.mul (hQ.comp (Measurable.smul (f:=fun _=>Real.sqrt θ) (g:=id) measurable_const measurable_id))).aestronglyMeasurable) |>.mpr hF
  obtain ⟨J,hJ,he⟩:= hU.1.post
  refine ⟨fun i=> (J*f i)*(1+(1+1))^n,(hb.const_mul J|>.mul_const _),?_⟩
  filter_upwards [h',he] with i hi hc z
  have hh:=(hi z).smul (M z); rw [hx,Real.norm_of_nonneg (show 0≤M z from Gaussian.tilt_nn ..)] at hh
  exact (((hc z).paints hh).trim).shimmy (Eventually.of_forall fun i'=> by dsimp [realProbe,scalp,M,K,s,B,U,Z]; change M z * (jacL _ _ _ _ _ _ * (Shield.lens₀ (U i') (K z i') / Shield.lens₀ (Pond.circuit N X.relating) (Pond.swim _ (s z)))) = _
                                                                           ring)

omit H hs A hχ hv hq hΘ
lemma product_data {E' ι : Type} {F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedCommRing F] [NormedAlgebra ℝ F] [NormOneClass F] (i:Finset ι) (f:ι→E'→F) {g r:ι→ℝ} {x:E'} (h:∀ j∈i,Brush n (g j) (r j) (f j) x) : Brush n (∏ j∈i,g j) (∑ j∈i,r j) (fun v=>∏ j∈i,f j v) x := by
    induction i using Finset.induction_on with
    | empty => simp only [Finset.prod_empty,Finset.sum_empty]; simpa only [norm_one] using (Brush.certified (E:=E') (k:=n) (x:=x) le_rfl (1:F))
    | insert a i ha hi => simp_rw [Finset.prod_insert ha,Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self _ _)).paints (hi fun j hj=> h j (mem_insert_of_mem hj))

lemma zestC {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {f g : Body₀→E'→ℂ} {x:E'} (h : Zest f x n) (h' : Zest g x n) : Zest (fun i y=>f i y*g i y) x n := by
  obtain ⟨C,hC,hZ⟩:=h.post; obtain ⟨B,hB,hM⟩:=h'.post; let c:ℝ:=(C*B)*(1+(1+1))^n
  refine ⟨c,(by unfold c; positivity),?_⟩; exact hZ.and hM|>.mono fun y hy p=> ((hy.1 p).paints (hy.2 p)).trim
lemma productsC {s : Type} [DecidableEq s] (i:Finset s) (f:s→Body₀→E→ℂ) (h : ∀ j∈i,Zest (f j) x n) : Zest (fun a y=>∏ j∈i,f j a y) x n := by
    induction i using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using! (Zest.still (A:=Body₀) (x:=x) (k:=n) (1:ℂ))
    | insert a v ha hi=> simp_rw [Finset.prod_insert ha]; exact zestC (h a (Finset.mem_insert_self _ _)) (hi fun j hj=> h j (mem_insert_of_mem hj))

include H hs A hχ hv hq hΘ hβ
variable (hÑ : LocalRatio Ñ) (hη': 0<η*X.t) (hr : 4*η*X.t < Ñ.radius) {u:ℂ} (hδ : 0<δ) (hQ : (4*(n+1):ℕ)*δ ≤ u.re) (hU':|u.im|≤δ)
local notation "J" => Fin (n+1)
variable (hk: ∀ i j : Fin (n+1),nodes u δ i j ∈ V₀)
include hÑ hk hη' hr
lemma sprout (i : Head S) (i' j':J) (k:Finset ℕ): Zest (fun t:Body₀=>perReal (Y:=Prod.fst) (k:=k) (a:=η) (W:=W) (Ñ:=Ñ) (u:=clipper) (C:=V) X l R inputZ (inverseP 1) (nodes u δ i' j') i t) x n := by
  have h := (H _ (hk i' j'))
  have ht : Zest clipper x n := (clipping_terms X R q (fun _=>1) 0 V a V₀ H hs A hχ hv).2.1
  have he := (orbit_terms X R q (fun _=>1) 0 V a V₀ H hq hs A hχ hv 1).1
  exact A.glassy (w:=fun t y=> Real.sqrt (nodes u δ i' j') • inverseP 1 t y) (Y:=fun t : Body₀=>t.1) inputZ h.laws.data.room _ ht h.laws.intake k l hη' hr hÑ i (he.scalar _)
local notation "exclude0" => (fun s:Body₀=> inputHeld X R q s)
local notation "posts" k:max i:max i':max j':max=> (sprout X R q V a V₀ H hq hs A hχ hΘ hβ hv hÑ hη' hr hk (l:=l) i i' j' k)
local notation "cp" i:max j:max => nodes u δ (n:=n) i j

include hδ hQ hk hU'
omit hδ hQ hU' H hs A hχ hv hq hΘ hβ hÑ hk hη' hr
private lemma zest_net {α : Type} {u:ℂ}{δ : ℝ} {f:J→J→ α→E→ℝ} {g : α → E → ℂ} {k:ℕ} {P : E→α→Prop} (hd:0≤deck u (δ:=δ) (n:=n)) (hp:∀ᶠ y in 𝓝 x,∀ t,P y t)
    (h : ∀ i j,Zest (f i j) x n) (he : ∀ y t (M:ℝ),P y t → 0≤M → (∀ i' j',Brush n M 1 (f i' j' t) y) → Brush n (cash u (δ:=δ) (n:=n) (fun _=>M) * (deck (δ:=δ) (n:=n) u)^k) 1 (g t) y) : Zest g x n := by
   let m q r:=(h q r).post.choose; let M:ℝ:=∑ p':J×J,m p'.1 p'.2
   let C:ℝ:=cash u (δ:=δ) (n:=n) (fun (_:ℝ)=>M)*(deck (δ:=δ) (n:=n) u)^k
   have hm q r := (h q r).post.choose_spec.1
   have ht:0≤M:= sum_nonneg (fun p _=>hm p.1 p.2)
   have ha:0≤speed n:= by unfold speed; positivity
   have hM i j':= (h i j').post.choose_spec.2
   refine ⟨C,(by unfold C cash; positivity),?_⟩
   filter_upwards [hp,eventually_all.mpr (fun i=> eventually_all.mpr (hM i))] with y hy hH z
   exact he y z M (hy z) ht fun i j=> (hH i j z).climb (single_le_sum (s:=univ) (f:=fun p':J×J=>m p'.1 p'.2) (fun p _=>hm p.1 p.2) (mem_univ (i,j))) le_rfl

include H hs A hχ hv hq hΘ hβ hÑ hk hη' hr
private lemma flasks (k:Finset ℕ) (j:Head S) (p:E) (z:Body₀) (M:ℝ) (hm : ∀ y' : Stores S, ContDiffAt ℝ n (fun t=>heatBase R (Art.drive X (V t) (Prod.fst z)) (clipper z t) (inputZ z) y') p)
        (hδ : 0<δ) (hQ : (4*(n+1):ℕ)*δ ≤ u.re) (hU':|u.im|≤δ) (hp:0≤M)
        (h:∀ (i j':J), Brush n M 1 (perReal (Y:=Prod.fst) (C:=V) (u:=clipper) (k:=k) (a:=η) (W:=W) (Ñ:=Ñ) X l R inputZ (inverseP 1) (nodes u δ i j') j z) p) :
     Brush n (cash u (δ:=δ) (n:=n) (fun _=>M) * (deck (δ:=δ) (n:=n) u)^heatTax X j) 1 (tempo (Y:=Prod.fst) X l (C:=V) (u:=clipper) (k:=k) (a:=η) (Ñ:=Ñ) (W:=W) R inputZ (inverseP 1) u j z) p := by
   exact harvest (y:=p) (Y:=Prod.fst) (V:=fun _=>M) (k:=k) X l R inputZ (inverseP 1) hβ hÑ.scale.ne' u j z hm
             hδ hQ hU' (fun _=>hp) zero_le_one (fun t j=>h t j)

include hδ hQ hU'
lemma cloudy (j : Head S) (k:Finset ℕ):Zest (fun (t:Body₀) (y:E)=>(rod (k:=k) (η:=η) (W:=W) (l:=l) (Ñ:=Ñ) X R q t.1 t.2 (V y) a j).run u) x n  := by
   have hr':0<u.re:=(by have he:=hs (hk 0 0); simp only [nodes,Fin.val_zero,Nat.cast_zero,mul_zero,sub_zero,add_zero] at he; exact he)
   have ha:0≤speed n:= by unfold speed; positivity
   let P'(y:E) (z:Body₀) := ∀ y', ContDiffAt ℝ n (fun t=>heatBase R (Art.drive X (V t) (Prod.fst z)) (clipper z t) (inputZ z) y') y
   let f' (i j':J) (t:Body₀) := perReal (Y:=Prod.fst) (k:=k) (C:=V) (a:=η) (W:=W) (Ñ:=Ñ) (u:=clipper) X l R inputZ (inverseP 1) (nodes u δ i j') j t
   let hh := (cashRef).laws.data
   have hx (j:Stores S) := (coal_prepares (Y:=Prod.fst) X R A inputZ hh.room (clipping_terms X R q (fun _=>1) 0 V a V₀ H hs A hχ hv).2.1 j).post.choose_spec.2
   let g t y := (tempo (Y:=Prod.fst) X l (C:=V) (u:=clipper) (k:=k) (a:=η) (Ñ:=Ñ) (W:=W) R inputZ (inverseP 1) u j t y)
   change Zest g x n
   refine zest_net (f:=f') (g:=g) (k:=heatTax X j) (x:=x) (P:=P') (show 0≤deck u (δ:=δ) (n:=n) from by unfold deck; positivity) ((eventually_all.mpr hx).mono fun i h z j'=> ((h j') z).smooth) (fun i₀ j₀=>posts k j i₀ j₀) fun y t M h hh ht=>?_
   exact (flasks X R q V a V₀ H hq hs A hχ hΘ hβ hv hÑ hη' hr hk k _ _ t M h hδ hQ hU' hh ht) -- likely wrong h args

local notation "clouding" k:max i:max => (cloudy X R q V a V₀ H hq hs A hχ hΘ hβ hv hÑ hη' hr hδ hQ hU' hk (l:=l) i k)
local notation "restored" t:max i:max r:max k:max => (tempo (C:=V) (u:=clipper) (k:=k) (a:=η) (W:=W) (Ñ:=Ñ) X l R inputZ (inverseP 1) r i t)
def kindled (Ñ:ChartRatio G) l W η (p:Molecule S) (r:ℂ) (t:Body₀) y:= ∏ i∈p, tempo (Y:=Prod.fst) (C:=V) (u:=clipper) (k:=Matter.own p) (a:=η) (W:=W) (Ñ:=Ñ) X l R inputZ (inverseP 1) r i t y
local notation "pyramid₀" => kindled X R q V a Ñ l W η
local notation "vas" t:max y:max r:max=> ratio X R q (Prod.fst t) (Prod.snd t) (V y) a I r
lemma rough (p : Molecule S) : Zest (pyramid₀ p u) x n := productsC p _ (fun i _=> clouding (Matter.own p) i)
local notation "mAt" t:max u:max => (cp t u)

def blending (M:J→J→ℝ) := (speed n)^n * (∑ i,(M i 0+M 0 i))
private lemma blend_integrable {μ:Measure Body₀} (M:J→J→ Body₀ →ℝ) (h : ∀ i j, Integrable (M i j) μ) : Integrable (fun z=>blending (fun i j=>M i j z)) μ := by unfold blending; exact Integrable.const_mul (integrable_finsetSum _ fun i _=> (h i 0).add (h 0 i)) _
lemma lees {z:Body₀} {M:ℝ→ℝ}{y:E}{φ:ℝ} (hφ:0≤φ) (H : ∀ (i j:J),let vθ:=nodes u δ i j; Brush n (M vθ) φ (fun y=>eq₀ z a vθ y) y)
    (ht : ContDiffAt ℝ n (fun w=> center₀ z w a) y):
   Brush n ((deck (δ:=δ) (n:=n) u)^Tᴵ.card * blending (fun t i=>M (mAt t i))) φ (fun y=>vas z y u) y := by
   let g r y:=eq₀ z a r y; let b y:=center₀ z y a
   have hG:CoalAt g y n Tᴵ.card (fun r y=>vas z y r) b := ⟨⟨fun y=> g 1 y/Real.exp (b y),fun _ _=>rfl⟩,Or.inl ht,fun r hr v=>real_ratio X R q z.1 z.2 (V v) a (hs hq) hβ I hr⟩
   have hg':= glance u hδ hQ hU' _ _ _ hφ H hG
   unfold deck blending; rw [←mul_assoc,mul_comm ((1 + speed n * δ / u.re) ^ (Tᴵ.card)) ((speed n)^n)]; exact hg'

variable (hA : 8*η* X.t≤a/2)(hVO : IsOpen V₀) (hB : Convex ℝ V₀) (hue:u.re∈V₀)
omit hδ hQ hU' H hs A hχ hv hq hΘ hβ hÑ hk hη' hr
lemma blend_ones (c:ℝ) : blending (fun (_ _:J)=>1) * c=blending (fun (_ _:J)=> c) :=by unfold blending; simp only [Finset.sum_const, nsmul_eq_mul]; ring
lemma marine {α : Type} [MeasurableSpace α] {f:J→J→ α→E→ℝ} {g : α → E → ℂ} {P' : E→α→Prop} (hd:0≤deck u (δ:=δ) (n:=n)) (hP:∀ᶠ y in 𝓝 x,∀ t,P' y t) (m:Measure α) (Q:α→E→ℂ)
    {k:ℕ} (p:Zest Q x n) (h : ∀ i j,∃ A : α → ℝ, Integrable A m ∧ ∀ᶠ y in 𝓝 x,∀ z, Brush n (A z) 1 (f i j z) y)
    (he : ∀ y t (M:ℝ),P' y t → 0≤M → (∀ i' j',Brush n M 1 (f i' j' t) y) → ∀ B:ℝ, Brush n B 1 (Q t) y → Brush n (((blending (fun (_ _:J)=>M) * (deck (δ:=δ) (n:=n) u)^k)*B)*(1+(1+1))^n) 1 (g t) y) :
    ∃ M, Integrable M m ∧ ∀ᶠ y in 𝓝 x,∀ t, Brush n (M t) 1 (g t) y := by
   let K q r:=(h q r).choose; let M (t):ℝ:=∑ p':J×J,K p'.1 p'.2 t
   let U:ℝ:=p.post.choose; let C:ℝ:=(blending (fun (_ _:J)=>1) * (deck (δ:=δ) (n:=n) u)^k*U)*(1+(1+1))^n
   have hm (q r:J) := (h q r).choose_spec.2
   have hM z := blend_ones (n:=n) (M z)
   refine ⟨(fun z=>C*M z),((integrable_finsetSum  (μ:=m) (f:=fun (p:J×J)=>K p.1 p.2) univ fun i _=>(h i.1 i.2).choose_spec.1).const_mul _),?_⟩
   filter_upwards [hP,p.post.choose_spec.2,eventually_all.mpr (fun i=> eventually_all.mpr (hm i))] with y hy hp hH z
   have ht:0≤M z:= sum_nonneg (fun p _=>(hH p.1 p.2 z).nonneg)
   have h:= he y z _ (hy z) ht (fun i j=> (hH i j z).climb (single_le_sum (s:=univ) (f:=fun p':J×J=>K p'.1 p'.2 z) (fun p _=>(hH p.1 p.2 z).nonneg) (mem_univ (i,j))) le_rfl) _ (hp z)
   exact h.climb ((by unfold C; rw [← hM z]; ring : _ = _).le) le_rfl
include hδ hQ hU' H hs A hχ hv hq hΘ hβ hÑ hk hη' hr
lemma prism_trim (D:ℝ) {z:Body₀} (y:E) (hg:∀ t i:J, Brush n D 1 (fun y=>eq₀ z a (nodes u δ t i) y) y) (hv' : ContDiffAt ℝ (n:WithTop ℕ∞) (fun y=>center₀ z y a) y) :
    Brush n ((deck (n:=n) (δ:=δ) u)^ Tᴵ.card*blending (fun (_ _:J)=>D)) 1 (fun y=>vas z y u) y := by
    have ht := fun (M:ℝ→ℝ) => lees (I:=I) (φ:=1) X R q V a V₀ H hq hs A hχ hΘ hβ hv hÑ hη' hr hδ hQ hU' hk (z:=z) (M:=M) (y:=y)
    specialize ht (fun _=>D); exact ht zero_le_one hg hv'
end YM.UVExt.EnergyRay.Thermal.Core
