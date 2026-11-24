import YM.Integration.PhysicalAffineScalarGaussianWeights
import YM.Integration.ConditionalAffineSourcePrices
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Drift
import YM.Next.FOUNDATIONS.LinkBounds
import YM.Extra.WILSON_STARTUP.Face

/-! Prices of the two original physical tail factors of the stationary square.
All row colors, input bonds and independently chosen field directions survive. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarInputPrices
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalAffineScalarCutWeights ConditionalAffineNoiseCoordinates
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- The true scalar row component is the contracted original vector path tail,
with precisely the physical slip and color, throughout the coarse field. -/
private theorem component (T : Tube G S) (x : ℝ) (i : Rows.Receipt G S) :
    (fun B : Vec G c 1 => sourceTail T x B i) =
      (- (slip • (EuclideanSpace.proj i.2 : G.Color →L[ℝ] ℝ))) ∘
        (fun B : Vec G c 1 => ConditionalAffineSourceSplit.difference T x B i.1) := by
  rcases i with ⟨a,b⟩
  rfl

/-- Curved signed row error with a charge on each independent coarse ray and
one native price independent of the period, cutoff, stage and forest. -/
theorem source (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ 0<ConditionalAffineSourcePrices.rate P L ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L →
    ∀ (_ : Forest S.ratio) (x : ℝ), 0<temp x → ∀ i : Rows.Receipt G S,
    ContDiffAt ℝ n (fun B : Vec G c 1 => sourceTail T x B i) 0 ∧
      ∀ (m : ℕ), m≤n → ∀ l : Fin m→ raw G c,
      Real.exp (δ*Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth∘l)) *
        |iteratedFDeriv ℝ m (fun B : Vec G c 1 => sourceTail T x B i) 0 (ray G c∘l)| ≤
        (|slip| * M)*Real.exp (-ConditionalAffineSourcePrices.rate P L*(till x:ℝ)) := by
  obtain ⟨δ,M,hδ,hM,hρ,hr⟩ := ConditionalAffineSourcePrices.raw G P L n
  obtain ⟨a,b,_,_,_,hp⟩ := ConditionalAffineSourcePrices.total G P L n
  refine ⟨δ,M,hδ,hM,hρ,?_⟩
  intro c f S T hP hL F x hx i
  let V := fun B : Vec G c 1 => ConditionalAffineSourceSplit.difference T x B i.1
  let Z := fun B => V ((arrange G c).symm B)
  let e := - (slip • (EuclideanSpace.proj i.2 : G.Color→L[ℝ] ℝ))
  have hV : ContDiffAt ℝ n V 0 := by
    have hZ : ContDiffAt ℝ n Z (arrange G c 0) := by simpa [Z,V] using (hp S T hP hL F x hx i.1).smooth
    have heq : V=Z∘arrange G c := by ext B; simp [Z]
    rw [heq]
    exact hZ.comp 0 (arrange G c).contDiff.contDiffAt
  have he : (fun B : Vec G c 1 => sourceTail T x B i) = e∘V := component T x i
  refine ⟨?_,?_⟩
  · rw [he]
    exact e.contDiff.contDiffAt.comp 0 hV
  intro m hm l
  let B := iteratedFDeriv ℝ m V 0 (ray G c ∘ l)
  let w := Real.exp (δ*Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth ∘ l))
  have hb : w*‖B‖ ≤ M*Real.exp (-ConditionalAffineSourcePrices.rate P L*(till x:ℝ)) := hr S T hP hL F x hx i.1 m hm l
  have hcomp : iteratedFDeriv ℝ m (fun z : Vec G c 1 => sourceTail T x z i) 0 (ray G c∘l)=e B := by
    rw [he,e.iteratedFDeriv_comp_left (hV.of_le (by exact_mod_cast hm)) le_rfl]
    rfl
  rw [hcomp]
  change w*|-(slip*(B i.2))| ≤ _
  rw [abs_neg,abs_mul]
  have hc : |B i.2| ≤ ‖B‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le B i.2
  calc w*(|slip| * |B i.2|) ≤ w*(|slip| * ‖B‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (abs_nonneg _)) (Real.exp_pos _).le
    _ = |slip| * (w*‖B‖) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hb (abs_nonneg slip)).trans_eq (by ring)

variable (T : Tube G S) (x : ℝ) (k : S.Choices)

/-- The directly transported and signed predictor arms disappear before any derivative is taken. -/
theorem direct (s : Signed) (p : Cell f) (b : G.ColorIndex) (j : raw G f) (B : Vec G c 1) :
    columnTail T x k B ((s,.inl (p,false)),b) j = 0 := by
  simp only [columnTail,Matrix.sub_apply]
  exact sub_eq_zero.mpr (ConditionalAffineRowDifference.direct T k s (shorter (till x)) all B p b j)

theorem predictor (s : Signed) (p : Bond c) (b : G.ColorIndex) (j : raw G f) (B : Vec G c 1) :
    columnTail T x k B ((s,.inr p),b) j = 0 := by
  simp only [columnTail,Matrix.sub_apply]
  exact sub_eq_zero.mpr (ConditionalAffineRowDifference.noise T k s (shorter (till x)) all B p b j)

/-- The transported row of the actual unmasked raw Jacobian, in either
weighted endpoint orientation and every independently chosen field leg. -/
theorem transported (s : Signed) (i : tile G f) (j : raw G f) (n : ℕ) {a t δ : ℝ}
    (hc : 1<c.val) (ht : 0<t) (ha : 0≤a) (hp : Sheet T.up t a) (hd : 0≤δ) (he : δ≤tier t n)
    (l : List (raw G c)) (hl : l.length≤n) :
    let w := |jet (ray G c) (fun B : Vec G c 1 => columnTail T x k B (ConditionalAffineRowDifference.row (S:=S) s i) j) l 0|
    let price := |slip| * (Real.exp (-(t/4)*(till x))*phasePrice G S.patch S.kernel n a t)
    (marks G c δ).pay l (named S s i) * ((native c).weight (wider t n) (named S s i) (home S j)*w) ≤ price ∧
    (marks G c δ).pay l (home S j) * ((native c).weight (wider t n) (home S j) (named S s i)*w) ≤ price := by
  intro w price
  have h := ConditionalAffineRowDifference.price T k s (till x) n hc ht ha hp hd he
  let D := ConditionalAffineRowDifference.difference T k s (till x)
  have hh : (fun B : Vec G c 1 => columnTail T x k B (ConditionalAffineRowDifference.row (S:=S) s i) j) =
      fun B => -(D B i j) := by
    funext B
    simp only [columnTail,Matrix.sub_apply,D,ConditionalAffineRowDifference.difference,Matrix.of_apply,neg_sub]
  have hn : jet (ray G c) (fun B : Vec G c 1 => -(D B i j)) l 0 =
      -jet (ray G c) (fun B : Vec G c 1 => D B i j) l 0 := by
    change iteratedFDeriv ℝ l.length (-(fun B : Vec G c 1 => D B i j)) 0 _ = _
    rw [iteratedFDeriv_neg_apply]
    rfl
  have hw : w=|(jet (ray G c) D l 0) i j| := by
    unfold w
    rw [hh,hn,abs_neg,FreeResolvent.TestD.entry (ray G c) l (h.smooth.of_le (by exact_mod_cast hl))]
  rw [hw]
  exact ⟨((h.bound l hl).row.entry i j),((h.bound l hl).col.entry j i)⟩

/-- The exact translated root of the transported physical arm is the anchor
of the native path bill. Oddness of the installed patch enters here. -/
theorem row_anchor (s : Signed) (i : tile G f) :
    named S s i=PhysicalAffineScalarComparison.rowRoot S (ConditionalAffineRowDifference.row (S:=S) s i) := by
  simp only [named,PhysicalAffineScalarComparison.rowRoot,ConditionalAffineRowDifference.row,Sum.elim_inl,
    affine,add_zero,S.ratio.parent_signed S.patch.odd_side]

/-- The spatially weighted column price for every real row, both endpoints,
including the zero direct and predictor arms. -/
theorem columns (i : Rows.Receipt G S) (j : raw G f) (n : ℕ) {a t δ : ℝ}
    (hc : 1<c.val) (ht : 0<t) (ha : 0≤a) (hp : Sheet T.up t a) (hd : 0≤δ) (he : δ≤tier t n)
    (l : List (raw G c)) (hl : l.length≤n) :
    let o := PhysicalAffineScalarComparison.rowRoot S i
    let w := |jet (ray G c) (fun B : Vec G c 1 => columnTail T x k B i j) l 0|
    let price := |slip| * (Real.exp (-(t/4)*(till x))*phasePrice G S.patch S.kernel n a t)
    (marks G c δ).pay l o * ((native c).weight (wider t n) o (home S j)*w) ≤ price ∧
    (marks G c δ).pay l (home S j) * ((native c).weight (wider t n) (home S j) o*w) ≤ price := by
  have hfee : 0≤|slip| * (Real.exp (-(t/4)*(till x))*phasePrice G S.patch S.kernel n a t) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (phase_nn _ _ _ ht ha))
  have hz (φ : Vec G c 1→ℝ) (hφ : ∀ b, φ b=0) : |jet (ray G c) φ l 0|=0 := by
    rw [show φ=(fun _ => 0) from funext hφ]
    by_cases h : l=[]
    · subst l; simp only [zeroth,abs_zero]
    · rw [jet_const _ _ h,abs_zero]
  rcases i with ⟨⟨s,frow|bond⟩,b⟩
  · rcases frow with ⟨⟨y,axes⟩,active⟩
    cases active with
    | false =>
      dsimp only
      rw [hz _ (direct T x k s (y,axes) b j)]
      simpa only [mul_zero,and_self] using hfee
    | true =>
      let z : tile G f := (y,plaqEquiv axes,b)
      have hh := transported T x k s z j n hc ht ha hp hd he l hl
      have hi : ConditionalAffineRowDifference.row (S:=S) s z=((s,.inl ((y,axes),true)),b) := by
        change ((s,Sum.inl ((y,plaqEquiv.symm (plaqEquiv axes)),true)),b)=_
        rw [Equiv.symm_apply_apply]
      rw [row_anchor s z,hi] at hh
      exact hh
  · dsimp only
    rw [hz _ (predictor T x k s bond b j)]
    simpa only [mul_zero,and_self] using hfee

end YM.Integration.PhysicalAffineScalarInputPrices
end

/-! Ordinary signed source in the genuine no-hole scalar weights. The fee is
first purchased in the normalized pulse and then pulled back, separately in
every coarse direction, to the manuscript's unscaled physical background. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarRetainedSource
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset AnalyticBridge.GaussianFieldAlignment
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD PhysicalAffineScalarCutResidual
open ConditionalAffineNoiseCoordinates ConditionalAffineCoarsePlaquettes
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (x : ℝ) (k : S.Choices)

/-- The genuine positive-threshold source and its purchased physical fixed-base
representative agree on one common neighbourhood for all actual signed rows. -/
theorem fixed (ht : 0<temp x) :
    (fun z : PriceCoords G c => Rows.base T x (AnalyticBridge.SectorAffine.field 1 z) k) =ᶠ[𝓝 0]
      fun z => Offset.fixedBase T x (AnalyticBridge.SectorAffine.field 1 z) k := by
  have hs (s : Signed) := ConditionalAffineSourceSplit.healthy_germ T (till x) ht
    (ConditionalAffineSourcePrices.flat_field (G:=G) (c:=c) s)
  filter_upwards [eventually_all.2 hs] with z hz
  funext i
  rcases i with ⟨s,i|j⟩
  · change _ - Pressure.zip _ (T.vision (till x) (temp x) (turn s 1 z)) i = _
    rw [hz s]
    rfl
  · change _ - Pressure.zip _ (T.vision (till x) (temp x) (turn s 1 z)) j = _
    rw [hz s]
    rfl

private theorem flags (ht : 0<temp x) : (noHole S).flags = RG.flags (temp x) (1:Config G c) := by
  ext i
  simp [noHole,RG.flags,WilsonStartup.face_one,G.chord_one,not_lt_of_ge ht.le]

/-- Genuine original stage purchase, including the native side/radius condition.
The field in this first receipt is the temperature-normalized original pulse. -/
theorem normalized (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (n : ℕ) :
    ∃ δ N : ℝ, 0<δ ∧ 0<N ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=P → Pt.Funds S T → 100*(1+radiusB x)≤c.val → 0<temp x → ∀ (_ : Forest S.ratio) (k : S.Choices),
    Parcel 0 (Wisps.down S) δ n (fun z : PriceCoords G c =>
      shortSource T x k ((arrange G c).symm (temp x • z))) (N*fiery G x P.L) := by
  obtain ⟨δ,N,hδ,hN,H⟩ := Offset.base_cost G P Pt hP n
  refine ⟨δ,N,hδ,hN,?_⟩
  filter_upwards [H] with x hx
  intro c f S T hS hT hc ht F k
  have hh := hx S T hS hT hc F (noHole S) 1 (flags (S:=S) x ht) k
  apply hh.glue
  have hcont : Continuous (fun z : PriceCoords G c => temp x • z) := (temp x • ContinuousLinearMap.id ℝ (PriceCoords G c)).continuous
  have hg := (fixed T x k ht).comp_tendsto (by simpa using hcont.tendsto 0)
  filter_upwards [hg] with z hz
  calc
    _ = tape.symm (slip • Offset.fixedBase T x (pulse x 1 z) k) :=
      congrArg (fun a : LogArray G (Slots S) => tape.symm a) (ConditionalNoHoleRows.all F x _)
    _ = _ := by
      let B := (arrange G c).symm (temp x • z)
      have hB : represent (decode B)=AnalyticBridge.SectorAffine.field 1 (temp x • z) :=
        (ConditionalAffineNoiseCoordinates.field (G:=G) (c:=c) B).symm.trans (congrArg (AnalyticBridge.SectorAffine.field (1 : Config G c))
          ((arrange G c).apply_symm_apply (temp x • z)))
      have hr : Rows.base T x (represent (decode B)) k=Offset.fixedBase T x (pulse x 1 z) k :=
        (congrArg (fun U : Config G c => Rows.base T x U k) hB).trans hz
      exact congrArg (fun a : LogArray G (Slots S) => tape.symm (slip • a)) hr.symm

/-- Native root of this very row and its Lie color. -/
theorem root (S : StepData c f) (i : Rows.Receipt G S) : Wisps.down S i=PhysicalAffineScalarComparison.rowRoot S i := by
  rcases i with ⟨⟨s,i|i⟩,b⟩ <;> rfl

/-- Undo normalization of an arbitrary list of independent directions in one
real Taylor derivative, retaining the exact cost for that derivative order. -/
private theorem unscale {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (u : E→H) (t : ℝ) (ht : t≠0) {n : ℕ}
    (h : ContDiffAt ℝ n (fun z : E => u (t • z)) 0) (v : Fin n→E) :
    iteratedFDeriv ℝ n u 0 v = (t⁻¹)^n • iteratedFDeriv ℝ n (fun z : E => u (t • z)) 0 v := by
  let L := t⁻¹ • ContinuousLinearMap.id ℝ E
  let U := fun z : E => u (t • z)
  have he : u=U ∘ L := by ext z; simp [U,L,smul_smul,ht]
  calc iteratedFDeriv ℝ n u 0 v = iteratedFDeriv ℝ n (U ∘ L) 0 v := congrArg (fun f => iteratedFDeriv ℝ n f 0 v) he
    _ = iteratedFDeriv ℝ n U 0 (fun j => t⁻¹ • v j) := by rw [Next.Foundations.jets_linear L h]; rfl
    _ = _ := by
      change (iteratedFDeriv ℝ n U 0).toMultilinearMap (fun i => t⁻¹ • v i)=
        (t⁻¹)^n • (iteratedFDeriv ℝ n U 0).toMultilinearMap v
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (iteratedFDeriv ℝ n U 0).toMultilinearMap.map_smul_univ (fun _ => t⁻¹) v

/-- The physical ordinary input in every non-normalized canonical field ray.
Its price is uniform before the period. The displayed explicit period
condition comes from the original `Offset.base_cost`. -/
theorem raw (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (n : ℕ) :
    ∃ δ N : ℝ, 0<δ ∧ 0<N ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=P → Pt.Funds S T → 100*(1+radiusB x)≤c.val → 0<temp x → ∀ (_ : Forest S.ratio)
    (k : S.Choices) (i : Rows.Receipt G S) (m : ℕ), m≤n → ∀ l : Fin m→ raw G c,
    Real.exp (δ*Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth∘l)) *
      |iteratedFDeriv ℝ m (fun B : Vec G c 1 => shortSource T x k B i) 0 (ray G c∘l)| ≤
      (temp x)⁻¹^m * (N*fiery G x P.L) := by
  obtain ⟨δ,N,hδ,hN,H⟩ := normalized G P Pt hP n
  refine ⟨δ,N,hδ,hN,?_⟩
  filter_upwards [H] with x hx
  intro c f S T hS hT hc ht F k i m hm l
  let U := fun z : PriceCoords G c => shortSource T x k ((arrange G c).symm z) i
  let l' := (index G c).symm ∘ l
  let v := Push.Uniform.bolt ∘ l'
  let t := temp x
  have hh := hx S T hS hT hc ht F k i
  have hf : ContDiffAt ℝ m (fun z : PriceCoords G c => U (t • z)) 0 := hh.smooth.of_le (by exact_mod_cast hm)
  have hs := unscale U t ht.ne' hf v
  have hp := hh.bound (List.ofFn l') (by simpa using hm)
  rw [Stars.pays,Stars.list_result,root] at hp
  have hU : (fun B : Vec G c 1 => shortSource T x k B i)=U∘arrange G c := by ext; simp [U]
  rw [hU,ConditionalAffineNoiseCoordinates.directions,hs,smul_eq_mul,abs_mul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) _)]
  calc _ = t⁻¹^m * (Real.exp (δ*Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth∘l))*
      |iteratedFDeriv ℝ m (fun z : PriceCoords G c => U (t • z)) 0 v|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (pow_nonneg (inv_nonneg.mpr ht.le) _)

/-- The independently prescribed uncut source equals the ordinary retained
physical row minus the true signed cutoff tail, for every background. -/
theorem full_decomposition (B : Vec G c 1) : PhysicalAffineScalarUncut.offset T k B =
    shortSource T x k B - PhysicalAffineScalarCutWeights.sourceTail T x B := by
  have hp : sourceRoutes T x k B=PhysicalAffineScalarCutWeights.sourceTail T x B := by
    apply tape.injective
    funext i
    rw [source_read,PhysicalAffineScalarCutWeights.sourceTail,tape.apply_symm_apply,
      ←ConditionalAffineSourceSplit.original T x k B i]
    abel
  rw [←hp,sourceRoutes]
  abel

private theorem regular {δ C : ℝ} {n : ℕ} (ht : 0<temp x) (i : Rows.Receipt G S)
    (H : Parcel 0 (Wisps.down S) δ n (fun z : PriceCoords G c =>
      shortSource T x k ((arrange G c).symm (temp x • z))) C) :
    ContDiffAt ℝ n (fun B : Vec G c 1 => shortSource T x k B i) 0 := by
  let e := (temp x)⁻¹ • (arrange G c).toContinuousLinearMap
  let U := fun z : PriceCoords G c => shortSource T x k ((arrange G c).symm (temp x • z)) i
  have h : (fun B : Vec G c 1 => shortSource T x k B i)=U∘e := by
    ext B
    simp [U,e,smul_smul,ht.ne']
  rw [h]
  exact (by simpa [U] using (H i).smooth : ContDiffAt ℝ n U (e 0)).comp 0 e.contDiff.contDiffAt

/-- True full ordinary signed offset, with native root charge on every coarse
leg. Both constants precede all stages and periods. The small second term
comes from the actual uncut-minus-cut source on this same physical stage. -/
theorem full (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (n : ℕ) :
    ∃ δ N M : ℝ, 0<δ ∧ 0<N ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
    100*(1+radiusB x)≤c.val → 0<temp x → ∀ (_ : Forest S.ratio) (k : S.Choices) (i : Rows.Receipt G S),
    ContDiffAt ℝ n (fun B : Vec G c 1 => PhysicalAffineScalarUncut.offset T k B i) 0 ∧
    ∀ (m : ℕ), m≤n → ∀ l : Fin m→FreeResolvent.Affine.raw G c,
    Real.exp (δ*Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth∘l)) *
      |iteratedFDeriv ℝ m (fun B : Vec G c 1 => PhysicalAffineScalarUncut.offset T k B i) 0 (ray G c∘l)| ≤
      (temp x)⁻¹^m * (N*fiery G x P.L) + (|slip| * M)*Real.exp (-ConditionalAffineSourcePrices.rate Pt P.L*(till x:ℝ)) := by
  obtain ⟨d,N,hd,hN,H⟩ := raw G P Pt hP n
  obtain ⟨d',N',_,_,H'⟩ := normalized G P Pt hP n
  obtain ⟨a,M,ha,hM,_,H₀⟩ := PhysicalAffineScalarInputPrices.source G Pt P.L n
  refine ⟨min d a,N,M,lt_min hd ha,hN,hM,?_⟩
  filter_upwards [H,H'] with x hx hx'
  intro c f S T hS hT hc ht F k i
  let u := fun B : Vec G c 1 => shortSource T x k B i
  let e := fun B : Vec G c 1 => PhysicalAffineScalarCutWeights.sourceTail T x B i
  have hU := regular T x k ht i (hx' S T hS hT hc ht F k)
  have hd' := H₀ S T hT (congrArg Patch.L hS) F x ht i
  have he : (fun B : Vec G c 1 => PhysicalAffineScalarUncut.offset T k B i)=u-e :=
    funext fun B => congrFun (full_decomposition T x k B) i
  rw [he]
  refine ⟨hU.sub hd'.1,?_⟩
  intro m hm l
  let J := fun f : Vec G c 1→ℝ => iteratedFDeriv ℝ m f 0 (ray G c∘l)
  let ρ := Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth∘l)
  let w := Real.exp (min d a*ρ)
  have w₁ : w≤Real.exp (d*ρ) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_left ..) (Stars.rays_nn ..))
  have w₂ : w≤Real.exp (a*ρ) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_right ..) (Stars.rays_nn ..))
  have hu := (mul_le_mul_of_nonneg_right w₁ (abs_nonneg (J u))).trans (hx S T hS hT hc ht F k i m hm l)
  have hh := (mul_le_mul_of_nonneg_right w₂ (abs_nonneg (J e))).trans (hd'.2 m hm l)
  rw [iteratedFDeriv_sub_apply (hU.of_le (by exact_mod_cast hm)) (hd'.1.of_le (by exact_mod_cast hm))]
  change w*|J u-J e|≤_
  calc _ ≤ w*(|J u|+|J e|) := mul_le_mul_of_nonneg_left (abs_sub ..) (Real.exp_pos _).le
    _ = w*|J u|+w*|J e| := mul_add ..
    _ ≤ _ := add_le_add hu hh

end YM.Integration.PhysicalAffineScalarRetainedSource
end
