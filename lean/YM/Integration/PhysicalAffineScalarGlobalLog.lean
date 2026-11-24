import YM.Integration.PhysicalAffineScalarSpectralRoot
import YM.Integration.ConditionalCovarianceRoots
import YM.Integration.PhysicalAffineScalarCutResidual
import YM.Integration.ConditionalAffineForcing

/-! Spatial-window and full-path cutoff of the *actual normalized root
half-log*. Each root sum has just the residue, bond and color multiplicity
of its own physical block. The normalized signed/quiet scalar reference is
kept in the flat-minus-curved convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarWindowPrice
open Function Filter Set Lattice Wilson RG Precision Exterior Tree Matrix Bloch
open Pressure Pressure.Stores Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment AnalyticBridge.RelativeLogdet FreeResolvent FreeResolvent.Affine
open FreeResolvent.TestD PhysicalNext.Repeat.Greenbelt
open ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "Slot" => Co S.patch.L (PAC G 1)
local notation "Coarse" => FreeResolvent.Vec G c 1

def key (D : StepData c f) (o : Site c) (j : Co D.patch.L (PAC G 1)) : raw G f :=
  (splitCo D.ratio (PAC G 1)).symm (o,j)

theorem home_key (o : Site c) (j : Slot) : home S (key S o j)=o := by
  let E := splitCo S.ratio (PAC G 1)
  have h : home (G:=G) (r:=1) S=Prod.fst ∘ E := funext fun i => by simp only [home,E,Function.comp_apply,split_co]
  rw [h]
  change (E (E.symm (o,j))).1 = o
  rw [Equiv.apply_symm_apply]

theorem collect_root (o : Site c) (w : raw G f → ℝ) :
    (∑ i : raw G f, if home S i=o then w i else 0) = ∑ j : Slot, w (key S o j) := by
  let E := splitCo S.ratio (PAC G 1)
  rw [←E.symm.sum_comp (fun i : raw G f => if home S i=o then w i else 0),Fintype.sum_prod_type]
  change (∑ a : Site c, ∑ j : Slot, if home S (key S a j)=o then w (key S a j) else 0) = _
  rw [Finset.sum_eq_single o]
  · simp [home_key]
  · intro a _ hne; simp [home_key,hne]
  · simp

/-- Each fine-key window is coupled to its own original forest and actual
radius. The flat term uses the identical window at zero coarse field. -/
def window (T : Tube G S) (B L : ℕ) (r : Reserve S) (k : S.Choices) (o : Site c) (x : Coarse) :=
  let P := ConditionalCovarianceShutter.columns G S B
  let W := whole S (allot r) k T.high T.up (shorter L)
  ∑ j : Slot, (letterBase P (W 0) (key S o j) - letterBase P (W x) (key S o j))/2

def difference (T : Tube G S) (B L : ℕ) (r : Reserve S) (k : S.Choices) (o : Site c) (x : Coarse) :=
  PhysicalAffineScalarSpectralRoot.halfLog T k (allot r) o x - window T B L r k o x

theorem charged (T : Tube G S) (B L : ℕ) (r : Reserve S) (k : S.Choices) (o : Site c) :
    difference T B L r k o = fun x =>
      ∑ j : Slot, ConditionalCovarianceLogarithm.paired B L r k T.high T.up (key S o j) x := by
  funext x
  unfold difference PhysicalAffineScalarSpectralRoot.halfLog window
  let df := fun i : raw G f =>
    (logKernel (whole S (allot r) k T.high T.up all 0) i i -
      logKernel (whole S (allot r) k T.high T.up all x) i i)/2
  change (∑ i : raw G f, if home S i=o then df i else 0) - _ = _
  rw [collect_root (S:=S) o df,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [df,ConditionalCovarianceLogarithm.paired,ConditionalCovarianceLogarithm.rooted]
  ring

theorem flat (T : Tube G S) (B L : ℕ) (r : Reserve S) (k : S.Choices) (o : Site c) :
    difference T B L r k o 0=0 := by simp [charged,ConditionalCovarianceLogarithm.flat]

private lemma uniform_sum {ι : Type} [Fintype ι] {p C : ℝ} (hp : 0≤p) (a : ι → ℝ)
    (ha : ∀ i, p * |a i| ≤ C) : p*|∑ i, a i| ≤ (Fintype.card ι:ℝ)*C := by
  calc _ ≤ p * ∑ i, |a i| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hp
       _ = ∑ i, p*|a i| := Finset.mul_sum ..
       _ ≤ ∑ _ : ι, C := Finset.sum_le_sum fun i _ => ha i
       _ = _ := by simp

/-- The derivative of the whole physical half-log error held at a single
translation, on independent signed color directions and a one-block switch.
The bound involves just the constant number of raw keys in a block and the
original exponential spatial-window and path-cut prices. -/
theorem original (T : Tube G S) (k : S.Choices) {σ A : ℝ} {n : ℕ} (hs : 0<σ)
    (ha : 0≤A) (hW : Sheet T.up σ A) (he : Bid.Larger (G:=G) S)
    (B L : ℕ) (r s : Reserve S) (o v : Site c) (h : ∀ w, w≠v → r w=s w)
    (l : List (raw G c)) (hl : l.length<n) (hz : l≠[]) :
    let d := width G S.patch S.kernel T.high n A σ
    let M := windowPrice G S.patch S.kernel T.high n A σ 0 B + diminish G S.patch S.kernel T.high n L A σ 0
    let P := (marks G c d).pay l o
    let K := fun t => jet (ray G c) (difference T B L t k o) l 0
    P*|K r| ≤ (Fintype.card Slot:ℝ)*(M/2) ∧
      (native c).weight d o v * P * |K s-K r| ≤ (Fintype.card Slot:ℝ)*(M/2) := by
  intro d M P K
  let H := fun t j => ConditionalCovarianceLogarithm.paired B L t k T.high T.up (key S o j)
  have hk (t : Reserve S) : K t = ∑ j : Slot, jet (ray G c) (H t j) l 0 := by
    change jet (ray G c) (difference T B L t k o) l 0 = _
    rw [charged,jet_sum]
    intro j _
    exact (ConditionalCovarianceLogarithm.paired_smooth (n:=n) hs ha hW he t B L (key S o j)).of_le (by exact_mod_cast hl.le)
  have hM (j : Slot) := ConditionalCovarianceLogarithm.one_tag (t:=k) (p:=T.high) hs ha hW he B L r s v h (key S o j) l hl hz
  have hp : 0≤P := ((marks G c d).pay_pos l o).le
  constructor
  · rw [hk]
    apply uniform_sum hp
    intro j
    simpa only [H,home_key] using (hM j).1
  · rw [hk,hk,←Finset.sum_sub_distrib]
    apply uniform_sum (mul_nonneg ((native c).weight_nn d o v) hp)
    intro j
    simpa only [H,home_key] using (hM j).2
end YM.Integration.PhysicalAffineScalarWindowPrice
end

/-! The stored global nonlinear paired half-log on arbitrary true forests.
The auxiliary principal window is exhausted on the finite original torus. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarGlobalLog
open Function Filter Set Lattice Wilson RG RG.Shoot Precision Exterior Tree Matrix Bloch
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment AnalyticBridge.RelativeLogdet FreeResolvent FreeResolvent.Affine
open FreeResolvent.TestD PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open PhysicalAffineScalarSpectralRoot (log_reindex log_on log_off sum_range)
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
/-- Exact floor-to-radius conversion, valid even at the smallest native
cutoff. Its constant and exponential rate depend only on the stage. -/
theorem price_radius (α x A : ℝ) (hα : 0≤α) :
    A*Real.exp (-α*(till x:ℝ)) ≤ (|A| * Real.exp α)*Real.exp (-(α/100000)*(radiusB x:ℝ)) := by
  have hN : radiusB x≤100000*(till x+1) := by unfold till; omega
  have hr : (radiusB x:ℝ)≤100000*((till x:ℝ)+1) := by exact_mod_cast hN
  have he : (radiusB x:ℝ)/100000-1≤(till x:ℝ) := by linarith
  have hx : Real.exp (-α*(till x:ℝ))≤Real.exp α*Real.exp (-(α/100000)*(radiusB x:ℝ)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc -α*(till x:ℝ) ≤ -α*((radiusB x:ℝ)/100000-1) := mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hα)
         _ = _ := by ring
  exact ((mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left hx (abs_nonneg A))).trans_eq (mul_assoc ..).symm

/-- Cap the retained decay rate to keep the floor loss a universal
constant, leaving a linear polynomial in the preassigned scalar tariff. -/
theorem price_radius_polynomial (α x fee : ℝ) (hα : 0≤α) :
    fee*Real.exp (-α*(till x:ℝ))≤(|fee| * Real.exp 1)*Real.exp (-(min α 1/100000)*(radiusB x:ℝ)) := by
  let κ := min α 1
  have hκ : 0≤κ := le_min hα zero_le_one
  have he : Real.exp (-α*(till x:ℝ))≤Real.exp (-κ*(till x:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left α 1)) (Nat.cast_nonneg _))
  have h₁ : fee*Real.exp (-α*(till x:ℝ))≤|fee| * Real.exp (-κ*(till x:ℝ)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self fee) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left he (abs_nonneg fee))
  have h₂ := price_radius κ x |fee| hκ
  rw [abs_abs] at h₂
  exact (h₁.trans h₂).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (min_le_right α 1)) (abs_nonneg fee)) (Real.exp_pos _).le)

variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "Coarse" => Vec G c 1

def cover (G : Gauge) (S : StepData c f) : ℕ := Finset.univ.sup (fun ij : raw G f × raw G f => separation (home S ij.1) (home S ij.2))

theorem covers {B : ℕ} (hB : cover G S≤B) (i : raw G f) : ConditionalCovarianceShutter.columns G S B i=Set.univ := by
  apply Set.eq_univ_of_forall; intro j
  apply (ConnectedActivityE6.Coat.frames G S B).low
  change separation (home S j) (home S i)≤B
  exact (Finset.le_sup (s:=Finset.univ) (f:=fun ij : raw G f × raw G f => separation (home S ij.1) (home S ij.2))
    (Finset.mem_univ (j,i))).trans hB

theorem complete {α : Type} [Fintype α] [DecidableEq α] (W : α→Set α) (h : ∀ i, W i=Set.univ)
    (A : Matrix α α ℝ) (i : α) : letterBase W A i=logKernel A i i := by
  have hw : W=fun _ => Set.univ := funext h
  subst W
  rw [base_log (fun _ => Set.mem_univ _) A i]
  let e : {j : α // j ∈ (Set.univ : Set α)} ≃ α := Equiv.Set.univ α
  let z : {j : α // j ∈ (Set.univ : Set α)} := ⟨i,Set.mem_univ i⟩
  have hz : e z=i := rfl
  have hm : Schur.principal A (Set.univ : Set α) = A.submatrix e e := rfl
  have hd := @log_reindex α {j : α // j ∈ (Set.univ : Set α)} _
    (@Subtype.fintype α (fun j => j ∈ (Set.univ : Set α))
      (fun j => Classical.propDecidable (j ∈ (Set.univ : Set α))) ‹Fintype α›)
    _ _ e A z
  rw [hz] at hd
  rw [hm]
  exact hd

variable (T : Tube G S) (x : ℝ) (k : S.Choices) (F : Forest S.ratio)
local notation "A" => noHole S
local notation "W₀" => shots S x
local notation "V" => fun B : Coarse => represent (decode B)
local notation "keys" => Rows.In (G:=G) x A F
local notation "addr" => (Native.lineEquiv F x).symm
local notation "Qc" => fun B : Coarse => Rows.gram T x (V B) k W₀ A F
local notation "Qu" => PhysicalAffineScalarUncut.gram T x k F
local notation "short" => shorter (till x)

def global (r : Admit) (o : Site c) (B : Coarse) := ∑ i : raw G f, if home S i=o then
  (logKernel (whole S F k T.high T.up r 0) i i-logKernel (whole S F k T.high T.up r B) i i)/2 else 0

private theorem selected (r : Admit) (o : Site c) (B : Coarse) (P Q : Gaussian.Table keys)
    (hP : P=(primary S F k T.high T.up r 0).submatrix addr addr)
    (hQ : Q=(primary S F k T.high T.up r B).submatrix addr addr) (hp : P.PosDef) (hq : Q.PosDef) :
    PhysicalAffineScalarCutResidual.halfLog (x:=x) (F:=F) o P Q=global T k F r o B := by
  let e := (Native.lineEquiv (G:=G) F x).symm
  let f := freeTo G S F
  let M := whole S F k T.high T.up r
  let H := primary S F k T.high T.up r
  let w (i : raw G _) := if home S i=o then (logKernel (M 0) i i-logKernel (M B) i i)/2 else 0
  have pos (a : Coarse) (K : Gaussian.Table keys) (h : K=(H a).submatrix e e) (hk : K.PosDef) : (H a).PosDef := by
    rw [h] at hk
    have he : H a=((H a).submatrix e e).submatrix e.symm e.symm := by ext i j; simp
    rw [he]; exact hk.submatrix e.symm.injective
  have hon (a : Coarse) (ha : (H a).PosDef) (j) : logKernel (M a) (f j) (f j)=logKernel (H a) j j :=
    log_on f (block S k T.high T.up r a) ha j
  have hoff (a : Coarse) (ha : (H a).PosDef) (i) (hi : i∉Set.range f) : logKernel (M a) i i=0 :=
    log_off f (block S k T.high T.up r a) ha i hi
  have h₀ := pos 0 P hP hp
  have h₁ := pos B Q hQ hq
  have hw (i) (hi : i∉Set.range f) : w i=0 := by simp [w,hoff 0 h₀ i hi,hoff B h₁ i hi]
  change _=∑ i, w i
  rw [←sum_range f w hw,←e.sum_comp (fun j => w (f j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hhome : S.ratio.parent j.1.1.1.1=home S (f (e j)) := rfl
  have pdiag : logKernel P j j = logKernel (H 0) (e j) (e j) := by
    rw [hP]
    exact log_reindex e (H 0) j
  have qdiag : logKernel Q j j = logKernel (H B) (e j) (e j) := by
    rw [hQ]
    exact log_reindex e (H B) j
  simp only [pdiag,qdiag,hhome,w,hon 0 h₀,hon B h₁]

/-- The actual stored paired logarithm with its simultaneous common flat
subtraction. Both kernels now have the common original raw index set. -/
theorem original (o : Site c) {σ K Λ : ℝ} (hp : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ K Λ)
    (hQ : ∀ᶠ B : Coarse in 𝓝 0, (Qc B).PosDef ∧ (Qu B).PosDef) :
    PhysicalAffineScalarCutResidual.logGap T x k F o=ᶠ[𝓝 0] fun B => global T k F short o B-global T k F all o B := by
  have hn := affine_near A F x T k hp hT
  have h₀ := hn.self_of_nhds
  have hp₀ := hQ.self_of_nhds
  filter_upwards [hn,hQ] with B hh hpos
  unfold PhysicalAffineScalarCutResidual.logGap
  rw [selected T x k F short o B _ _ h₀ hh hp₀.1 hpos.1,
    selected T x k F all o B _ _ (PhysicalAffineScalarMetric.uncut T x k F 0)
      (PhysicalAffineScalarMetric.uncut T x k F B) hp₀.2 hpos.2]

/-- A true independent finite window covering all original keys is exactly
the stored global truncated operator, including each flat normalization. -/
theorem full_window {B : ℕ} (hB : cover G S≤B) (L : ℕ) (r : Reserve S) (o : Site c) :
    PhysicalAffineScalarWindowPrice.window T B L r k o=global T k (allot r) (shorter L) o := by
  funext b
  unfold PhysicalAffineScalarWindowPrice.window global
  rw [PhysicalAffineScalarWindowPrice.collect_root (S:=S) o]
  simp_rw [complete _ (covers hB)]

/-- Signed global cut discrepancy versus uncut on the true reserve draw. -/
theorem difference {B : ℕ} (hB : cover G S≤B) (L : ℕ) (r : Reserve S) (o : Site c) :
    PhysicalAffineScalarWindowPrice.difference T B L r k o = fun b => global T k (allot r) all o b-global T k (allot r) (shorter L) o b := by
  unfold PhysicalAffineScalarWindowPrice.difference
  rw [full_window T k hB L r o]; rfl

private theorem smooth (B L : ℕ) (r : Reserve S) (o : Site c) {σ a : ℝ} {n : ℕ}
    (hs : 0<σ) (ha : 0≤a) (hW : Sheet T.up σ a) (he : Bid.Larger (G:=G) S) :
    ContDiffAt ℝ n (PhysicalAffineScalarWindowPrice.difference T B L r k o) 0 := by
  rw [PhysicalAffineScalarWindowPrice.charged]
  exact ContDiffAt.sum fun j _ => ConditionalCovarianceLogarithm.paired_smooth hs ha hW he r B L
    (PhysicalAffineScalarWindowPrice.key S o j)

/-- Smoothness of the actual globally stored relative log with its original
flat denominator, as a consequence of the purchased physical window germ. -/
theorem regular (o : Site c) {σ a τ K Λ : ℝ} {n : ℕ} (hs : 0<σ) (ha : 0≤a)
    (hW : Sheet T.up σ a) (he : Bid.Larger (G:=G) S) (hp : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high τ K Λ) (hQ : ∀ᶠ B : Coarse in 𝓝 0, (Qc B).PosDef ∧ (Qu B).PosDef) :
    ContDiffAt ℝ n (PhysicalAffineScalarCutResidual.logGap T x k F o) 0 := by
  let r : Reserve S := fun _ => F
  let L := till x
  let B := cover G S
  have hb : cover G S≤B := le_rfl
  have hw := smooth T k B L r o (n:=n) hs ha hW he
  apply hw.neg.congr_of_eventuallyEq
  filter_upwards [original T x k F o hp hT hQ] with y hy
  change _= -PhysicalAffineScalarWindowPrice.difference T B L r k o y
  rw [difference T k hb L r o,show allot r=F from ConditionalAffineDraws.constant F,hy]
  ring

private theorem cut_at_zero {p : Clip} (n L : ℕ) (a σ : ℝ) :
    diminish G S.patch S.kernel p n L a σ 0 =
      diminish G S.patch S.kernel p n 0 a σ 0 * Real.exp (-(σ/4)*(L:ℝ)) := by
  calc
    _ = diminish G S.patch S.kernel p n 0 a σ 0 * Real.exp (-(σ/4)*(L:ℝ)) * drain 0^2 :=
      ConditionalCovarianceCutoff.cut_price (G:=G) (S:=S)
    _ = _ := by simp [drain]

private theorem window_zero {p : Clip} (q : ℕ) {σ a : ℝ} (hs : 0<σ) (ha : 0≤a) :
    Tendsto (fun N : ℕ => windowPrice G S.patch S.kernel p q a σ 0 N) atTop (𝓝 0) := by
  let d := width G S.patch S.kernel p q a σ
  let μ : ℝ := (q+1:ℕ)*d
  have hμ : 0<μ := mul_pos (by positivity) (gauged G S.patch S.kernel p q hs ha).pos
  have decay : Tendsto (fun N : ℕ => Real.exp (-μ*(N:ℝ))) atTop (𝓝 0) := by
    have H := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-μ)).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hμ))
    exact H.congr' (Eventually.of_forall fun N => by rw [←Real.exp_nat_mul]; congr 1; ring)
  have H := (tendsto_const_nhds (x:=windowPrice G S.patch S.kernel p q a σ 0 0)).mul decay
  rw [mul_zero] at H
  apply H.congr'; apply Eventually.of_forall; intro N
  change windowPrice G S.patch S.kernel p q a σ 0 0 * Real.exp (-μ*(N:ℝ)) =
    windowPrice G S.patch S.kernel p q a σ 0 (N:ℝ)
  have h : windowPrice G S.patch S.kernel p q a σ 0 (N:ℝ) =
      windowPrice G S.patch S.kernel p q a σ 0 0 * Real.exp (-(q+1:ℕ)*d*(N:ℝ)) * drain 0^2 :=
    ConditionalTreeCovarianceSums.window_price (G:=G) (S:=S)
  rw [h]
  simp only [drain,add_zero,inv_one,one_pow,mul_one]
  congr 2
  dsimp only [μ]
  push_cast
  ring

/-- All actual tree heights and orientations may differ away from the
marked site. Only the original free/trunk projections control these two
physical operators; that is enough to realize the same genuine draw. -/
theorem charged (U : Forest S.ratio) (o z : Site c) (hFU : changed S F U z)
    {σ a τ K Λ : ℝ} (hs : 0<σ) (ha : 0≤a) (hW : Sheet T.up σ a) (he : Bid.Larger (G:=G) S)
    (hp : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high τ K Λ)
    (hQ : ∀ V₀ : Forest S.ratio, ∀ᶠ B : Coarse in 𝓝 0,
      (Rows.gram T x (V B) k W₀ A V₀).PosDef ∧ (PhysicalAffineScalarUncut.gram T x k V₀ B).PosDef)
    (n : ℕ) (l : List (raw G c)) (hl : l.length≤n) :
    let d := width G S.patch S.kernel T.high (n+1) a σ
    let slots := (Fintype.card (Co S.patch.L (PAC G 1)):ℝ)
    let cutoff := diminish G S.patch S.kernel T.high (n+1) 0 a σ 0
    (marks G c d).pay l o*((native c).weight d o z*
      |jet (ray G c) (fun B => PhysicalAffineScalarCutResidual.logGap T x k U o B-
        PhysicalAffineScalarCutResidual.logGap T x k F o B) l 0|)≤
      (slots*(cutoff/2))*Real.exp (-(σ/4)*(till x:ℝ)) := by
  intro d slots cutoff
  let L := till x
  let win (N : ℕ) := windowPrice G S.patch S.kernel T.high (n+1) a σ 0 N
  let fee := diminish G S.patch S.kernel T.high (n+1) L a σ 0
  have price : fee=cutoff*Real.exp (-(σ/4)*(L:ℝ)) := cut_at_zero (G:=G) (S:=S) (n+1) L a σ
  let X := (marks G c d).pay l o*((native c).weight d o z*
      |jet (ray G c) (fun B => PhysicalAffineScalarCutResidual.logGap T x k U o B-
        PhysicalAffineScalarCutResidual.logGap T x k F o B) l 0|)
  have hi : X ≤ slots*(fee/2) := by
    by_cases hz : l=[]
    · subst l
      have hc := cut_nonneg (S:=S) (G:=G) (p:=T.high) (n:=n+1) hs ha (by norm_num : 0≤(0:ℝ)) L
      dsimp [X]; simp only [zeroth,PhysicalAffineScalarCutResidual.logGap,PhysicalAffineScalarCutResidual.halfLog,
        sub_self,zero_div,ite_self,Finset.sum_const_zero,abs_zero,mul_zero]
      exact mul_nonneg (by positivity) (div_nonneg hc (by norm_num))
    obtain ⟨r,s,hr,hF,hU⟩ := ConditionalAffineDraws.realize F U z hFU
    have hsU (q : Admit) : global T k (allot s) q o=global T k U q o := by
      unfold global; rw [ConditionalAffineDraws.whole (allot s) U hU k T.high T.up q]
    have valid (N : ℕ) (hN : cover G S≤N) : X ≤ slots*((win N+fee)/2) := by
      let diff := PhysicalAffineScalarWindowPrice.difference T N L
      have et : (fun B : Coarse => PhysicalAffineScalarCutResidual.logGap T x k U o B-
          PhysicalAffineScalarCutResidual.logGap T x k F o B)=ᶠ[𝓝 0] fun B => diff r k o B-diff s k o B := by
        filter_upwards [original T x k F o hp hT (hQ F),original T x k U o hp hT (hQ U)] with b hb hc
        change _=PhysicalAffineScalarWindowPrice.difference T N L r k o b-
          PhysicalAffineScalarWindowPrice.difference T N L s k o b
        rw [difference T k hN L r o,difference T k hN L s o,hF,hsU all,hsU (shorter L),hb,hc]
        ring
      have hw (v : Reserve S) : ContDiffAt ℝ l.length (diff v k o) 0 :=
        smooth_of_le (smooth T k N L v o (n:=n) hs ha hW he) hl
      have hj : jet (ray G c) (fun B => PhysicalAffineScalarCutResidual.logGap T x k U o B-
          PhysicalAffineScalarCutResidual.logGap T x k F o B) l 0=
          jet (ray G c) (diff r k o) l 0-jet (ray G c) (diff s k o) l 0 := by
        have h₀ : jet (ray G c) (fun B => PhysicalAffineScalarCutResidual.logGap T x k U o B-
            PhysicalAffineScalarCutResidual.logGap T x k F o B) l 0=
            jet (ray G c) (fun B => diff r k o B-diff s k o B) l 0 := by
          change iteratedFDeriv ℝ l.length _ 0 _=iteratedFDeriv ℝ l.length _ 0 _
          rw [(et.iteratedFDeriv (𝕜:=ℝ) l.length).self_of_nhds]
        exact h₀.trans (jet_sub (ray G c) l (hw r) (hw s))
      have H := (PhysicalAffineScalarWindowPrice.original T k hs ha hW he N L r s o z hr l (Nat.lt_succ_of_le hl) hz).2
      dsimp only [X]; rw [hj,abs_sub_comm,←mul_assoc,mul_comm ((marks G c d).pay l o)]
      exact H
    have limit : Tendsto win atTop (𝓝 0) := window_zero (S:=S) (p:=T.high) (n+1) hs ha
    have H : Tendsto (fun N : ℕ => slots*((win N+fee)/2)) atTop (𝓝 (slots*(fee/2))) := by
      simpa only [zero_add] using (tendsto_const_nhds (x:=slots)).mul ((limit.add_const fee).div_const 2)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds H ((eventually_ge_atTop (cover G S)).mono valid)
  calc _ ≤ slots*(fee/2) := hi
       _ = _ := by rw [price]; ring

/-- Undifferenced rooted price of the actual whole-torus relative scalar
half-log. The physical mark/tail and the flat paired convention are the
same used for one-tree charges. -/
theorem ordinary (o : Site c) {σ a τ K Λ : ℝ} (hs : 0<σ) (ha : 0≤a) (hW : Sheet T.up σ a)
    (he : Bid.Larger (G:=G) S) (hp : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high τ K Λ)
    (hQ : ∀ᶠ B : Coarse in 𝓝 0, (Qc B).PosDef ∧ (Qu B).PosDef) (n : ℕ) (l : List (raw G c)) (hl : l.length≤n) :
    let d := width G S.patch S.kernel T.high (n+1) a σ
    let slots := (Fintype.card (Co S.patch.L (PAC G 1)):ℝ)
    let cutoff := diminish G S.patch S.kernel T.high (n+1) 0 a σ 0
    (marks G c d).pay l o * |jet (ray G c) (PhysicalAffineScalarCutResidual.logGap T x k F o) l 0|≤
      (slots*(cutoff/2))*Real.exp (-(σ/4)*(till x:ℝ)) := by
  intro d slots cutoff
  let L := till x
  let r : Reserve S := fun _ => F
  let win (N : ℕ) := windowPrice G S.patch S.kernel T.high (n+1) a σ 0 N
  let fee := diminish G S.patch S.kernel T.high (n+1) L a σ 0
  let X := (marks G c d).pay l o*|jet (ray G c) (PhysicalAffineScalarCutResidual.logGap T x k F o) l 0|
  have price : fee=cutoff*Real.exp (-(σ/4)*(L:ℝ)) := cut_at_zero (G:=G) (S:=S) (n+1) L a σ
  have hi : X ≤ slots*(fee/2) := by
    by_cases hz : l=[]
    · subst l
      dsimp only [X]; simp only [zeroth,PhysicalAffineScalarCutResidual.logGap,PhysicalAffineScalarCutResidual.halfLog,
        sub_self,zero_div,ite_self,Finset.sum_const_zero,abs_zero,mul_zero]
      exact mul_nonneg (by positivity) (div_nonneg (cut_nonneg hs ha (by norm_num) L) (by norm_num))
    have valid (N : ℕ) (hN : cover G S≤N) : X ≤ slots*((win N+fee)/2) := by
      let f := PhysicalAffineScalarWindowPrice.difference T N L r k o
      have et : PhysicalAffineScalarCutResidual.logGap T x k F o=ᶠ[𝓝 0] fun B => -f B := by
        filter_upwards [original T x k F o hp hT hQ] with B hB
        change _= -PhysicalAffineScalarWindowPrice.difference T N L r k o B
        rw [difference T k hN L r o,show allot r=F from ConditionalAffineDraws.constant F,hB]; ring
      have heq : jet (ray G c) (PhysicalAffineScalarCutResidual.logGap T x k F o) l 0=
          -jet (ray G c) f l 0 := by
        have h₀ : jet (ray G c) (PhysicalAffineScalarCutResidual.logGap T x k F o) l 0=jet (ray G c) (fun B => -f B) l 0 := by
          change iteratedFDeriv ℝ l.length _ 0 _=iteratedFDeriv ℝ l.length _ 0 _
          rw [(et.iteratedFDeriv (𝕜:=ℝ) l.length).self_of_nhds]
        exact h₀.trans (jet_linear (ray G c) l (-(ContinuousLinearMap.id ℝ ℝ))
          (smooth_of_le (smooth T k N L r o (n:=n) hs ha hW he) hl))
      have H := (PhysicalAffineScalarWindowPrice.original T k hs ha hW he N L r r o o (fun _ _ => rfl) l (Nat.lt_succ_of_le hl) hz).1
      dsimp only [X]; rw [heq,abs_neg]; exact H
    have limit : Tendsto win atTop (𝓝 0) := window_zero (S:=S) (p:=T.high) (n+1) hs ha
    have H : Tendsto (fun N : ℕ => slots*((win N+fee)/2)) atTop (𝓝 (slots*(fee/2))) := by
      simpa only [zero_add] using (tendsto_const_nhds (x:=slots)).mul ((limit.add_const fee).div_const 2)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds H ((eventually_ge_atTop (cover G S)).mono valid)
  calc _ ≤ slots*(fee/2) := hi
       _ = _ := by rw [price]; ring

end YM.Integration.PhysicalAffineScalarGlobalLog
end

