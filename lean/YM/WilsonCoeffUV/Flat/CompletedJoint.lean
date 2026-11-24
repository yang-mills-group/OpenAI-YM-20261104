import YM.Next.STATIONARY.Films.TraceDifference
import YM.WilsonCoeffUV.Flat.Hessian
/-!
# Strip for the completed *joint* flat inverse
Independent of block length. Auxiliary cosine gauges have a purpose only for
this estimate; our coefficient calculation itself uses a tree slice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Filter Function Lattice RG Laurent Exterior Bloch Metric Matrix Precision Stationary
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} {c f L : Side} {s n : ℕ→Side} {K : KernelChoices} {P : Patch}

-- No kinetic/interaction input to the flat symbol for the gauge completion.
def zeroEye (G : Gauge) (P : Patch) : Eye (Fin 0) (Acts G P) := 0

lemma zeroSpot {η : ℝ} (hp : η≤(1 : ℝ)) : Spotlight P (zeroEye G P) η (Real.exp 4) :=
    ⟨hp,Fresh.placed (0 : Phase (Fin 0) →ₗ[ℂ] Phase (Acts G P)),le_refl _,fun i => Fin.elim0 i⟩

def frozenF (G : Gauge) (P : Patch) := (CanonR (zeroEye G P) false).tab

lemma regulator_symbol (S : StepData c f) (h : S.patch.Branches S.kernel G) (t : S.Choices) :
    Jaunt (approached (repackM (unitSplit G S 0) (clothe G S)
      (postroom S t (inch S.patch.L)))) (frozenF G S.patch) 0 := by
  let V : Corn (Co c (Fin 0))→L[ℝ] Bang G c f := 0
  have he : Turns (zeroEye G S.patch) (billZ S V) := by
    refine ⟨0,fun u => ?_,fun i q _ v => ?_⟩
    · ext a; simp [billZ, axes, V]
    ext a; simp [zeroEye,tune]
  have hv := (regulator_tour S t false V he h (fun x => rfl)).tab
  unfold cardM at hv; dsimp only at hv
  rw [zero_hat S h] at hv; exact hv

def fill (S : StepData c f) (G : Gauge) (t : S.Choices) (B : Bed) :=
    let F := postroom (G:=G) S t (inch S.patch.L)
    repackM (clothe G S) (clothe G S) (frontR G S B+ Fᵀ*F)

def filled (G : Gauge) (P : Patch) (k : ℝ) (B : Bed) := forceK G P (frozenF G P) k B

lemma fill_symbol (S : StepData c f) (G : Gauge) (B : Bed) {σ Θ : ℝ} (h : S.patch.Branches S.kernel G)
    (hs : 0 < σ) (he : B.metric.strip (inch S.patch.L*σ) Θ) (t : S.Choices) :
    Jaunt (approached (fill S G t B)) (filled G S.patch S.kernel.penalty B) 0 := by
  classical
  let X := clothe G S; let V := postroom (G:=G) S t (inch S.patch.L); let R := frontR G S B
  change Jaunt (approached (repackM X X (R+Vᵀ*V))) _ _
  rw [show repackM X X (R+Vᵀ*V) = repackM X X R+repackM X X (Vᵀ*V) from rfl, prom_addition,
    repack_multiply _ (unitSplit G S 0), repack_rotate, prom_mul]
  have hg := regulator_symbol S h t
  exact (gift_turn (G:=G) (S:=S) B hs he).plus (hg.takes.hoist hg)

theorem freezing (G : Gauge) (K : KernelChoices) (J : ℕ) (v ε Θ : ℝ) (hv : 0<v) (he : 0<ε)
    (ht : 0≤Θ) : ∃ w η D:ℝ, 0<w ∧ w ≤ v ∧ 0<η ∧ η≤w ∧ 0≤D ∧
    ∀ (P : Patch), P.J=J → P.Branches K G → ∀ (p:Clip) (B:Bed) (C:ℝ),
    (∀ n, Floor B p n ε C) → B.metric.strip (inch P.L*w) Θ →
    Freezer (slabW G P.L|>.dual) (slabW G P.L) (filled G P K.penalty B) η D ∧
      Poster w (filled G P K.penalty B) := by
  obtain ⟨u,d,hu,hb,hd,hQ⟩ := amasses G
  set w := min u v; have hw : 0<w := lt_min hu hv
  have hg := min_le_left u v
  have hh : w ≤ 1 := by unfold w; linarith
  let A := tribute2 G J (Real.exp 4) d
  obtain ⟨η,C,hη,hS,hC,H⟩ := post_cert G J K ε w Θ |A| he hw hh ht (abs_nonneg _)
  refine ⟨w,η,C,hw,min_le_right ..,hη,hS,hC,?_⟩
  intro P hP hf p B D H' U
  have hz := conquer hf hw (zeroSpot hh) (hQ P.L w hg)
  have hy : Poster w (frozenF G P) := hz.covered.tab
  let n := fun i=>walent i * P.L
  let W : Armada walent n P K := ⟨fun i=>rfl⟩
  exact ⟨H P hP hf B p D (frozenF G P) _ _ W walentes U H' hy
    (fun p hx => (hz.base hx).mono (by rw [hP]; apply le_abs_self))
    (fun i => Classical.arbitrary (W.boot i).Choices) (fun i => regulator_symbol (W.boot i) hf _),
    (gift_lane B (K.penalty:ℂ) U hw).amounts (hy.reverse.forge hy)⟩

open Next.Free
variable {η σ E C : ℝ}

lemma hill_cont (i : Site L) : Continuous fun p => hill p i := by
  unfold hill pebWeight shadeK; simp_rw [slug_sq]
  unfold Exterior.q aliasAt ground axes
  fun_prop

open scoped Matrix.Norms.L2Operator in
lemma tile_cont {α : Type} [Fintype α] [DecidableEq α] (L : Side) : Continuous (altarTile L α).tile := by
  unfold altarTile contour
  have h : Continuous (plankTile L α) := continuous_iff_continuousAt.mpr fun p => continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ((tile_lit p) i j).continuousAt
  have hx (i : Co L α) : Continuous fun p => spice L α p i := by
    unfold spice; apply Continuous.inv₀; exact Complex.continuous_ofReal.comp (hill_cont _)
    intro p; exact_mod_cast (hill_pos p i.1).ne'
  exact (h.mul (continuous_pi fun i => continuous_pi fun j => by
    change Continuous fun p : Momentum => diagonal (spice L α (id p)) i j
    simp only [Matrix.diagonal_apply]; split <;> first | exact hx _ | exact continuous_const)).mul continuous_const

open scoped Matrix.Norms.L2Operator in
lemma slab_cont (L : Side) : Continuous (slabW G L).tile := by
  have ht := tile_cont (α:=Loc G 1) L
  apply continuous_pi; intro i; apply continuous_pi; intro j
  rcases i with i|i <;> rcases j with j|j <;> first
    | exact continuous_const
    | change Continuous fun p : Momentum => (altarTile L (Loc G 1)).tile p i j; exact continuous_pi_iff.mp (continuous_pi_iff.mp ht i) j

open scoped Matrix.Norms.L2Operator in
lemma tile_cash (G : Gauge) (L : Side) (η : ℝ) (he : 0<η) : ∃ M:ℝ, 0<M ∧
    ∀ p ∈ cube η, vflux ((slabW G L).tile p) ≤ M := by
  obtain ⟨x,hx⟩ := ((isCompact_closedBall (0:Momentum) (Real.pi+η+η)).image
    (show Continuous (fun p: Momentum => vflux ((slabW G L).tile p)) from Continuous.norm (slab_cont _))).bddAbove
  refine ⟨max 1 x,lt_max_of_lt_left one_pos,fun p hp => (hx ⟨p,?_,rfl⟩).trans (le_max_right ..)⟩
  rw [mem_closedBall,dist_zero_right]; apply (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => ?_)
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add (hp.2 i).le (hp.1 i).le)

lemma coupon_bound (G : Gauge) (L : Side) (hs : 0<σ) (hC : 0≤C) : ∃ A:ℝ, 0<A ∧
    ∀ (F:Momentum→CompM (ParcelG G L) (ParcelG G L)), Freezer (slabW G L|>.dual) (slabW G L) F σ C →
    ∀ p ∈ cube σ, ∀ a b, ‖(F p)⁻¹ a b‖ ≤ A := by
  let X := slabW G L
  obtain ⟨M,hM,h⟩ := tile_cash G L σ hs
  refine ⟨max 1 (M*C*M),lt_max_of_lt_left one_pos,fun F he p hp a b=>?_⟩
  let U := (F p)⁻¹
  let Y := carryM X X.dual p p U
  have hv : U = X.tile p * Y * (X.dual.tile p)⁻¹ := by
    unfold Y carryM; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (X.tile p), mul_nonsing_inv _ (X.whole _), one_mul,mul_nonsing_inv _ (X.dual.whole _),mul_one]
  have hU : vflux U ≤ M*C*M := by
    rw [hv]
    apply (flux_power ..).trans; apply mul_le_mul
    · exact (flux_power ..).trans (mul_le_mul (h p hp) (he.price p hp.1) (flux_nonneg _) hM.le)
    · rw [X.inverse_dual,back_flux]; exact h _ (cube_neg _ hp)
    · apply flux_nonneg
    positivity
  exact ((flux_tilt U a b).trans hU).trans (le_max_right ..)

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
lemma price_record {F : Momentum→CompM α α} (hσ : 0<σ) (hp : Poster σ F)
    (hh : ∀ p∈cube σ,∀ a b,‖F p a b‖ ≤ E) : (record F).strip (σ/4) (E*(2*((1+σ/4)/(σ/4)))^4) := by
  intro a b
  let f p := F p a b
  have hs : SafeCube σ E f := ⟨fun p hv => hp.shape hv.1 _ _,fun p h=>hh p h _ _⟩
  have hg : Overlaps σ f := fun p h x _ => congr_fun (congr_fun (hp.shifts (p:=p) (q:=p+reciprocal x) ⟨x,rfl⟩ (Work.F07.realStrip _ hσ h.1)).symm _) _
  obtain ⟨hx,he,-⟩ := hol_on_thickening hσ hs hg
  have hy := hx.issues he (σ/4) (σ/4) (by linarith) (by linarith) (by linarith)
  exact_mod_cast Work.F07.widthRealPart hy

omit [Fintype α] [DecidableEq α] in
lemma reads_record {F : Momentum→CompM α α} (hσ : 0<σ) (hp : Poster σ F)
    (hh : ∀ p∈cube σ,∀ a b,‖F p a b‖ ≤ E) (hn : ∀ p:Momentum, star p=p→ ∀ a b, star (F (-p) a b)= F p a b) :
    ∀ p ∈ baseCube, (record F).read p=F p := by
  intro p he; ext a b
  let f p := F p a b
  have hs : SafeCube σ E f := ⟨fun p hv => hp.shape hv.1 _ _,fun p h=>hh p h _ _⟩
  have hg : Overlaps σ f := fun p h x _ => congr_fun (congr_fun (hp.shifts (p:=p) (q:=p+reciprocal x) ⟨x,rfl⟩ (Work.F07.realStrip _ hσ h.1)).symm _) _
  exact RRead_paints hσ hs hg (fun q hx=> hn q hx.1 a b) p (base_subset_realCube hσ he)

-- Eq only on the mesh is needed
lemma matrix_one {U : Matrix (Co L α) (Co L α) ℝ} {V : Momentum→CompM α α} (h : Jaunt (approached U) V 0) {R:Row α α} (hh : R.safe) (hv : ∀ p∈baseCube, (R.read p)*V p=1) :
    R.acts L * U = 1 := by
  apply prom_inj; rw [prom_mul]
  have hx := ((Jaunt.row (m:=L) R hh).hoist h)
  have hU : approached (1:Matrix (Co L α) (Co L α) ℝ)=1 := by
    ext i j; by_cases hg : i=j <;> simp [approached,hg,Matrix.one_apply]
  rw [hU]
  apply cancel_rotation
  rw [one_mul]
  ext i ⟨p,b⟩
  have he : (fun j => rotations L α j (p,b))=tune p (Pi.single b 1) := funext fun j => coef_wave ..
  change (((approached _ * _ : CircM L α α) *ᵥ fun j => rotations L α j (p,b)) i) = rotations L α i (p,b)
  have hh := hx p _ (rolls.refl _) (Pi.single b 1)
  dsimp only at hh
  rw [hv _ (mon_mem L p), one_mulVec,add_zero] at hh
  rw [he,hh]
  exact (congr_fun he i).symm

open scoped Classical in
lemma cold_supply (G : Gauge) (K : KernelChoices) (J : ℕ) (ε Θ σ : ℝ) (hσ : 0<σ)
    (he : 0<ε) (ht : 0≤Θ) : ∃ w η:ℝ, 0<w ∧ w≤σ ∧ 0<η ∧ η ≤ w ∧
    ∀ (P : Patch), P.J=J → P.Branches K G → ∃ A>0,∀ (p:Clip) (B:Bed) (C:ℝ),
    (∀ n, Floor B p n ε C) → B.metric.strip (inch P.L*w) Θ →
    ∃ R:Row (ParcelG G P.L) (ParcelG G P.L), R.strip η A ∧
      ∀ (c f:Side) (hc:f.val=c.val*P.L.val), let S : StepData c f := ⟨P,K,hc⟩
                                              ∀ t,R.acts c*fill S G t B=1 := by
  obtain ⟨w,η,D,hw,hω,hη,hW,hD,H⟩ := freezing G K J σ ε Θ hσ he ht
  refine ⟨w,η/4,hw,hω,by positivity,by linarith,?_⟩
  intro P hP hK
  obtain ⟨A,hA,h⟩ := coupon_bound G P.L hη hD
  refine ⟨A*(2*((1+η/4)/(η/4)))^4,by positivity,?_⟩
  intro p B C hb hi
  obtain ⟨hU,hV⟩ := H P hP hK p B C hb hi
  let F := filled G P K.penalty B
  let v := fun i=> (F i)⁻¹
  have hv := h F hU
  have he : Poster η v := ⟨fun y => BillD.take ((hV.skinny hW).shape y) (hU.period _ y),fun he q=> congr_arg (·⁻¹) ((hV.skinny hW).shifts he q)⟩
  let R := record v
  have he' : R.strip _ _ := price_record hη he hv
  refine ⟨R,he',?_⟩
  intro c f hc S t
  convert! matrix_one (fill_symbol S G B hK hw hi t) (R.rights _ _ he' (by positivity)) ?_ using 2
  · congr!
  intro x hx
  have hh (x : Momentum) (h : star x=x) : ∀ i j, star (v (-x) i j)=v x i j := by
    let m i := walent i * P.L
    let W : Armada walent m P K := ⟨fun i=>rfl⟩
    have he (i) := fill_symbol (W.boot i) G B hK hw hi (Classical.arbitrary _)
    have hy : (F (-x))ᵀ=(F x)ᴴ := judge walentes he hV hw h
    have hk := congr_arg (·⁻¹) hy
    rw [← transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv] at hk
    intro i j
    have hg : v (-x) i j = star (v x i j) := congr_fun (congr_fun hk j) i
    rw [hg, star_star]
  rw [show R.read x=v x from reads_record hη he hv hh x hx]; exact Matrix.nonsing_inv_mul _ (hU.period _ (Work.F07.realStrip _ hη hx.1))
end YM.WilsonCoeffUV
