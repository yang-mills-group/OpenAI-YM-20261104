import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Drift
import YM.Integration.ConditionalCovarianceCutoff
import YM.Integration.PhysicalAffineScalarUncut
import YM.Push.FREE_RESOLVENT.BlockRate

/-! The original signed affine loads, unmasked source split, and priced physical column discrepancy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineForcing
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Next.SectorChange Next.SectorChange.Rows
open Next.SectorChange.Gaussian AnalyticBridge.GaussianFieldAlignment
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD PhysicalNext.Repeat.Greenbelt
open ConditionalTreeCovarianceJets
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (k : S.Choices)
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "A" => noHole S

/-- The columns live in common raw coordinates, even when the forests use
active spaces with different keys. -/
def rawRows (q : Admit) (B : Coarse) : Matrix (Rows.Receipt G S) (raw G f) ℝ :=
  Matrix.of fun i j => tape.symm (slip • PhysicalAffineScalarJets.slope T k q B (Pi.single j (1:ℝ))) i

def load (q : Admit) (B : Coarse) (b : Prices G (Slots S)) : raw G f → ℝ :=
  (rawRows T k q B).transpose.mulVec b

def retain (F : Forest S.ratio) (i : raw G f) (b : ℝ) :=
  if i ∈ Set.range (freeTo G S F) then b else 0

def source (F : Forest S.ratio) (B : Coarse) (i : raw G f) :=
  retain F i (load T k all B (PhysicalAffineScalarUncut.offset T k B) i)

theorem insertion_single {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ↪ ι) (i : κ) : insertion e *ᵥ Pi.single i (1:ℝ) = Pi.single (e i) (1:ℝ) := by
  rw [Matrix.mulVec_single_one]
  funext z
  by_cases h : e i = z
  · subst z
    simp [insertion]
  simp [insertion,h,Ne.symm h]

/-- The restricted columns are the columns of the genuine independently
prescribed uncut no-hole affine action, on each forest's actual key. -/
theorem original_column (F : Forest S.ratio) (x : ℝ) (B : Coarse) :
    PhysicalAffineScalarUncut.columns T x k F B = (rawRows T k all B).submatrix id (address A F x) := by
  ext i j
  change tape.symm (slip • PhysicalAffineScalarJets.slope T k all B
    (launch.symm (Rows.fresh x (shots S x) A F (axisPrice j)))) i = _
  rw [axisPrice,←relative_input A F x,ContinuousLinearEquiv.symm_apply_apply,insertion_single]
  rfl

/-- Identifies the active force itself, not merely its Gram or determinant. -/
theorem original_source (F : Forest S.ratio) (x : ℝ) (B : Coarse) (i : Rows.In (G:=G) x A F) :
    source T k F B (address A F x i) = ((PhysicalAffineScalarUncut.columns T x k F B).transpose.mulVec
      (PhysicalAffineScalarUncut.offset T k B)) i := by
  have hi : address (G:=G) A F x i ∈ Set.range (freeTo G S F) := ⟨live A F x i,rfl⟩
  rw [source,retain,if_pos hi,original_column]
  rfl

/-- At a specified physical draw change, every raw forcing entry over every
other output site is exactly the same at all coarse backgrounds. -/
theorem away (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w)
    (i : raw G f) (hi : home S i ≠ v) :
    (fun B => source T k (allot s) B i) = fun B => source T k (allot r) B i := by
  funext B
  simp only [source,retain]
  simp only [suits G v (change_draw r s v h) i hi]

theorem flat (F : Forest S.ratio) (h : S.patch.Branches S.kernel G) (i : raw G f) :
    source T k F 0 i = 0 := by
  simp [source,PhysicalAffineScalarUncut.offset_zero T k h,load,retain]

theorem zero_jet (l : List (raw G c)) :
    jet (ray G c) (fun _ : Coarse => (0:ℝ)) l 0=0 := by
  by_cases h : l=[]
  · subst l
    exact zeroth (ray G c) _ _
  exact jet_const (ray G c) l h 0 0

/-- An actual forest switch has only the one unpaid forcing coordinate.
The ordinary unprojected coefficient bounds the changed tensor at that site
with no factor for the period or number of active keys. -/
theorem one_tag (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w)
    (i : raw G f) (l : List (raw G c)) :
    |jet (ray G c) (fun B => source T k (allot s) B i) l 0 -
     jet (ray G c) (fun B => source T k (allot r) B i) l 0| ≤
      if home S i = v then |jet (ray G c)
        (fun B => load T k all B (PhysicalAffineScalarUncut.offset T k B) i) l 0| else 0 := by
  by_cases hi : home S i = v
  · rw [if_pos hi]
    by_cases h₁ : i ∈ Set.range (freeTo G S (allot r)) <;>
      by_cases h₂ : i ∈ Set.range (freeTo G S (allot s)) <;>
      simp [source,retain,h₁,h₂,zero_jet]
  rw [away T k r s v h i hi,sub_self,abs_zero,if_neg hi]

end YM.Integration.ConditionalAffineForcing

namespace YM.Integration.ConditionalAffineSourceSplit
open Function Filter Set Metric Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Tube
open Pressure.Stores Next.SectorChange Next.SectorChange.Rows Gaussian
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD AnalyticBridge.GaussianFieldAlignment
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset ProjectorNext.Equivariance
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (x : ℝ) (k : S.Choices)
local notation "Coarse" => Gaussian.Vec (Raw G c)
local notation "V" => fun B : Coarse => represent (decode B)

private theorem zip_sub {ι κ : Type} [Fintype κ] (A B : ι → κ → Pressure.Pay G)
    (u v : κ → G.Color) (i : ι) :
    Pressure.zip A u i - Pressure.zip B v i =
    Pressure.zip (fun i j => A i j-B i j) u i + Pressure.zip B (u-v) i := by
  classical
  unfold Pressure.zip
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change A i j (u j) - B i j (v j) =
    (A i j (u j) - B i j (u j)) + B i j (u j-v j)
  rw [map_sub]
  abel

/-- A scalar multiplier is the original signed normalization outside both
arms of the row. The predictor has canceled identically in the noise arm. -/
def difference (B : Coarse) (i : Slots S) : G.Color :=
  let v := pull i.1 0 (V B)
  let u := shone S i.1 B
  let z := PhysicalAffineScalarUncut.plaquetteRows T.down T.low v
  let t := T.vision (till x) (temp x) v
  i.2.elim (fun h =>
    PhysicalAffineScalarUncut.plaquetteRows T.up T.high u h - T.Xf (till x) u h -
    Pressure.zip (fun h j => PhysicalAffineScalarUncut.faceStack T v h j - T.Φ (till x) v h j) z h -
    Pressure.zip (T.Φ (till x) v) (z-t) h)
    (fun h => -Pressure.zip (fun h j => PhysicalAffineScalarUncut.noiseStack T v h j-T.Φ' (till x) v h j) z h -
    Pressure.zip (T.Φ' (till x) v) (z-t) h)

theorem unit_face {n : Side} (i : Cell n) : faceValue (1:Config G n) i=1 := by
  simp [faceValue,travel,Lattice.square]

/-- The true row defect has zero constant coefficient, without a period or temperature restriction. -/
theorem flat (i : Slots S) : difference T x (0:Coarse) i=0 := by
  have ht {n : Side} (v : Site n) (l : Slot) : l.atSite (1:Config G n) v=0 := by
    rw [Work.F03.atSite_path,unit_face,G.curvature_unit,map_zero]
  have hr {n : Side} (P : PathData G) (p : Clip) (i : Twin n) : PhysicalAffineScalarUncut.plaquetteRows P p (1:Config G n) i=0 := by
    unfold PhysicalAffineScalarUncut.plaquetteRows
    split <;> simp [PathData.ell,PathData.ellTerms,ht,shoot,unit_face,G.curvature_unit]
  have hv : (V (0:Coarse))=1 := by
    change represent (decode (0:Coarse))=1
    rw [show decode (0:Coarse) = 0 from (plain G c 1).map_zero,link_one]
  have hp {n : Side} (s : Signed) : pull s 0 (1:Config G n)=1 := by
    funext i
    unfold pull Step.read
    split <;> simp
  have hf (s : Signed) : shone S s (0:Coarse)=1 := by
    rw [shone,backdrop,show represent (decode (0:Coarse))=1 from hv,replica_one,hp]
  have hz {n : Side} (P : PathData G) (p : Clip) (R d : ℕ) (y : Twin n) :
      Pressure.plotted P p R d (1:Config G n) y=0 := by
    simp [Pressure.plotted, Pressure.shorten, Pressure.shortenTerm, PathData.ellTerms, ht,
      Pressure.shoot,unit_face,G.curvature_unit]
  have hvn (y : Twin c) : T.vision (till x) (temp x) (1:Config G c) y=0 := by
    simp [Tube.vision,Pressure.thinned,Pressure.shorten,Pressure.shortenTerm,PathData.ellTerms,
      ht,Pressure.shoot,unit_face,G.curvature_unit]
  rcases i with ⟨s,z|z⟩ <;>
    simp [difference,hf,hp,hv,hr,hvn,Tube.Xf,hz,Pressure.zip]

theorem original (B : Coarse) (i : Slots S) :
    tape (PhysicalAffineScalarUncut.offset T k B) i - slip • PhysicalAffineScalarJets.offset T x k B i =
      slip • difference T x B i := by
  rcases i with ⟨s,p|b⟩
  · simp only [PhysicalAffineScalarUncut.offset,tape.apply_symm_apply,
      PhysicalAffineScalarJets.offset,difference,Sum.elim_inl,←smul_sub]
    rw [show ∀ (a b c d : G.Color), a - b - (c-d) = (a-c)-(b-d) from fun _ _ _ _ => by abel,
      Tube.Mv,zip_sub]
    abel
  · simp only [PhysicalAffineScalarUncut.offset,tape.apply_symm_apply,
      PhysicalAffineScalarJets.offset,difference,Sum.elim_inr,←smul_sub]
    rw [show ∀ (a b d : G.Color), a - b - (a-d) = -(b-d) from fun _ _ _ => by abel,
      Tube.Mw,zip_sub]
    abel

/-- On the selected no-hole material all signed coarse plaquettes are
healthy. At each actual coarse argument the original window is unthinned. -/
theorem vision (P : Teller G) (hP : P.Funds S T)
    (ht : till x+1≤radiusB x/50 ∧ ∀ k : ℕ, temp x*Real.exp (k/P.below.clip.relaxation)<2 → k+1≤radiusB x/50)
    (U : Config G c) (hU : ∀ q, toll U q≤temp x) :
    T.vision (till x) (temp x) U = T.Xn (till x) U := by
  funext j
  exact kept_vision hP ht U j.1.1 j (fun q _ => hU q) (by simp)

/-- This identity needs only contact of the chart with the unit gauge
field. Its neighborhood may vary with the physical period. -/
theorem vision_germ {ι : Type} [TopologicalSpace ι] {a : ι} (P : Teller G) (hP : P.Funds S T)
    (ht : till x+1≤radiusB x/50 ∧ ∀ k : ℕ, temp x*Real.exp (k/P.below.clip.relaxation)<2 → k+1≤radiusB x/50)
    (hx : 0<temp x) (U : ι → Config G c) (h : Tendsto U (𝓝 a) (𝓝 1)) :
    (fun z => T.vision (till x) (temp x) (U z)) =ᶠ[𝓝 a] fun z => T.Xn (till x) (U z) := by
  have H (p : Cell c) : ∀ᶠ z in 𝓝 a, toll (U z) p≤temp x := by
    have hc : Continuous (fun U₀ : Config G c => toll U₀ p) := by unfold toll; unfold faceValue; fun_prop
    have h0 : toll (1:Config G c) p<temp x := by simpa only [toll,unit_face,G.chord_one] using hx
    exact (((hc.continuousAt.tendsto).comp h).eventually (gt_mem_nhds h0)).mono fun _ hz => hz.le
  filter_upwards [eventually_all.2 H] with z hz
  exact vision T x P hP ht _ hz

/-- At the original flat germ one can enforce the positive scalar threshold
on every one of the finitely many physical plaquettes. This directly
evaluates both arms of the unmodified thinned source. -/
theorem healthy (R : ℕ) (t : ℝ) (ht : 0≤t) (U : Config G c) (hU : ∀q, toll U q≤t) :
    T.vision R t U=T.Xn R U := by
  funext j
  rcases j with ⟨p,q⟩
  have hk : PathData.kept T.low t p.1 U := fun o => (hU o).trans
    (le_mul_of_one_le_right ht (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) T.low.radius_pos.le)))
  cases q
  · change (if toll U p=0 then 1 else min 1 (t/toll U p)) • shoot T.low U p=shoot T.low U p
    by_cases hz : toll U p=0
    · rw [if_pos hz,one_smul]
    have hp : 0<toll U p := lt_of_le_of_ne (G.chord_nonneg _) (Ne.symm hz)
    rw [if_neg hz,min_eq_left ((le_div_iff₀ hp).2 (by simpa only [one_mul] using hU p)),one_smul]
  change (if PathData.kept T.low t p.1 U then _ else 0)=_
  rw [if_pos hk]
  simp [Tube.Xn,Pressure.plotted]

/-- Every original independent flat derivative can use Xn without the
coarse vision profile. The neighborhood may depend on the finite period;
the jet and its quantitative price do not pay its radius. -/
theorem healthy_germ {ι : Type} [TopologicalSpace ι] {a : ι} (R : ℕ) {t : ℝ} (ht : 0<t)
    {U : ι → Config G c} (h : Tendsto U (𝓝 a) (𝓝 1)) :
    (fun z => T.vision R t (U z)) =ᶠ[𝓝 a] fun z => T.Xn R (U z) := by
  have H (p : Cell c) : ∀ᶠ z in 𝓝 a, toll (U z) p≤t := by
    have hc : Continuous (fun U₀ : Config G c => toll U₀ p) := by unfold toll faceValue; fun_prop
    have h0 : toll (1:Config G c) p<t := by simpa only [toll,unit_face,G.chord_one] using ht
    exact (((hc.continuousAt.tendsto).comp h).eventually (gt_mem_nhds h0)).mono fun _ hz => hz.le
  filter_upwards [eventually_all.2 H] with z hz
  exact healthy T R t ht.le _ hz

end YM.Integration.ConditionalAffineSourceSplit

namespace YM.Integration.ConditionalAffineRowDifference
open Function Filter Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Tube Pressure.Stores
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Matrix
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD PhysicalNext.Repeat.Greenbelt
open ConditionalAffineForcing ConditionalTreeCovarianceJets
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (t : S.Choices)

def row (s : Signed) (i : tile G f) : Rows.Receipt G S :=
  ((s,.inl ((i.1,plaqEquiv.symm i.2.1),true)),i.2.2)

theorem physical (s : Signed) (r : Admit) (B : Vec G c 1) (i : tile G f) (j : raw G f) :
    rawRows T t r B (row (S:=S) s i) j = slip*FreeResolvent.Affine.gram S s T.up r B i j := by
  change slip*((FreeResolvent.Affine.gram S s T.up r B *ᵥ Pi.single j 1)
    (i.1,plaquette (plaqEquiv.symm i.2.1),i.2.2)) = _
  simp only [←plaq_map,Equiv.apply_symm_apply,Matrix.mulVec_single_one,Matrix.col_apply]

/-- The genuine finite aperture mask has no effect on the dependence of
the direct plaquette and coarse-noise derivative upon `Admit`. -/
theorem direct (s : Signed) (q q' : Admit) (B : Vec G c 1) (p : Cell f) (a : G.ColorIndex) (j : raw G f) :
    rawRows T t q B ((s,.inl (p,false)),a) j = rawRows T t q' B ((s,.inl (p,false)),a) j := rfl

theorem noise (s : Signed) (q q' : Admit) (B : Vec G c 1) (p : Bond c) (a : G.ColorIndex) (j : raw G f) :
    rawRows T t q B ((s,.inr p),a) j = rawRows T t q' B ((s,.inr p),a) j := rfl

def difference (s : Signed) (R : ℕ) (B : Vec G c 1) : Matrix (tile G f) (raw G f) ℝ := Matrix.of fun i j =>
  rawRows T t all B (row s i) j - rawRows T t (shorter R) B (row s i) j

/-- Both Schur orientations and every independently assigned coarse ray in
an actual full-minus-short signed affine receipt row. -/
theorem price (s : Signed) (R n : ℕ) {σ A d : ℝ} (hc : 1<c.val) (hσ : 0<σ) (hA : 0≤A)
    (hW : FreeResolvent.Affine.Sheet T.up σ A) (hd : 0≤d) (he : d≤tier σ n) :
    Bundle (ray G c) (marks G c d) (native c) (named S s) (home S) (difference T t s R) 0 n (wider σ n)
      (|slip| *(Real.exp (-(σ/4)*R)*phasePrice G S.patch S.kernel n A σ)) := by
  have hR : ∀ z, longer R z=true → R≤z.length := by
    intro z hz
    have hh : ¬z.length≤R := by simpa [longer,shorter] using hz
    exact (Nat.lt_of_not_ge hh).le
  have H := (gram_paid S hc s hσ hA hW hd he (longer R) R hR).scale slip
  apply H.glue
  filter_upwards [remaining_work S s T.up R hσ hW] with B hB
  ext i j
  simp only [difference,Matrix.of_apply,physical,Matrix.smul_apply,smul_eq_mul]
  unfold FreeResolvent.Affine.gram
  rw [hB,Matrix.add_mul,Matrix.add_apply]
  ring

def retained (F : Forest S.ratio) (s : Signed) (R : ℕ) (i : tile G f) (j : raw G f) (B : Vec G c 1) :=
  if j∈Set.range (freeTo G S F) then difference T t s R B i j else 0

/-- An original forest switch can change a projected tail only over its
own physical block. Its magnitude is bounded by the same exponentially
small true unprojected column, at every fixed order including zero. -/
theorem one_tag (s : Signed) (R : ℕ) (r q : Reserve S) (v : Site c) (h : ∀ w, w≠v → r w=q w)
    (i : tile G f) (j : raw G f) (l : List (raw G c)) :
    |jet (ray G c) (retained T t (allot q) s R i j) l 0 - jet (ray G c) (retained T t (allot r) s R i j) l 0| ≤
      if home S j=v then |jet (ray G c) (fun B => difference T t s R B i j) l 0| else 0 := by
  let D := fun B => difference T t s R B i j
  have mask (F : Forest S.ratio) : retained T t F s R i j =
      if j∈Set.range (freeTo G S F) then D else fun _ => (0:ℝ) := by
    by_cases hf : j∈Set.range (freeTo G S F) <;> funext B <;> simp [retained,D,hf]
  have zero : jet (ray G c) (fun _ : Vec G c 1 => (0:ℝ)) l 0=0 := ConditionalAffineForcing.zero_jet l
  rw [mask,mask]
  by_cases hv : home S j=v
  · rw [if_pos hv]
    by_cases hr : j∈Set.range (freeTo G S (allot r))
    · by_cases hq : j∈Set.range (freeTo G S (allot q))
      · simp only [if_pos hq,if_pos hr,sub_self,abs_zero]
        exact abs_nonneg _
      · simp only [if_neg hq,if_pos hr,zero,zero_sub,abs_neg]
        change |jet (ray G c) D l 0| ≤ |jet (ray G c) D l 0|
        exact le_rfl
    · by_cases hq : j∈Set.range (freeTo G S (allot q))
      · simp only [if_pos hq,if_neg hr,zero,sub_zero]
        change |jet (ray G c) D l 0| ≤ |jet (ray G c) D l 0|
        exact le_rfl
      · simp only [if_neg hq,if_neg hr,sub_self,abs_zero]
        exact abs_nonneg _
  rw [if_neg hv]
  have he := suits G v (change_draw r q v h) j hv
  by_cases hr : j∈Set.range (freeTo G S (allot r))
  · have hq := he.mpr hr
    simp only [if_pos hq,if_pos hr,sub_self,abs_zero,le_refl]
  have hq := he.not.mpr hr
  simp only [if_neg hq,if_neg hr,sub_self,abs_zero,le_refl]

end YM.Integration.ConditionalAffineRowDifference

/-! Actual original reserve draws realizing arbitrary forests with one changed active projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineDraws
open Function Lattice Wilson RG RG.Patch Bloch Tree Precision Exterior Matrix
open PhysicalNext.Repeat.Greenbelt FreeResolvent FreeResolvent.Affine
open scoped Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

theorem constant (F : Forest S.ratio) : allot (S:=S) (fun _ => F)=F := identityF _ _ rfl rfl

/-- Outside the changed parent only the real set of non-tree coordinates is needed.
The two purchasing draws agree as entire trees at every other site. -/
theorem realize (F U : Forest S.ratio) (o : Site c) (h : changed S F U o) :
    ∃ r s : Reserve S, (∀ z, z≠o → r z=s z) ∧ allot r=F ∧
      ∀ i : Edge (Site f), i∈(allot s).trunks ↔ i∈U.trunks := by
  let r : Reserve S := fun _ => F
  let s : Reserve S := fun z => if z=o then U else F
  refine ⟨r,s,fun z hz => by simp [r,s,hz],constant F,fun i => ?_⟩
  by_cases hi : S.ratio.parent i.1=o
  · have H := ConditionalTreeCovarianceJets.allot_trunks s (fun _ => U) i (by simp [s,hi])
    rw [constant] at H
    exact H
  · have H := ConditionalTreeCovarianceJets.allot_trunks s r i (by simp [s,r,hi])
    rw [show allot r=F from constant F] at H
    exact H.trans (h i hi)

theorem whole (F U : Forest S.ratio) (h : ∀ i : Edge (Site f), i∈F.trunks ↔ i∈U.trunks)
    (k : S.Choices) (p : Clip) (W : PathData G) (q : Admit) :
    Affine.whole S F k p W q=Affine.whole S U k p W q := by
  have ran : Set.range (freeTo G S F)=Set.range (freeTo G S U) := by
    ext ⟨x,i,j⟩
    obtain ⟨w,rfl⟩ := axisEquiv.surjective i
    erw [locate F (x,w),locate U (x,w),h (x,w)]
  funext B i j
  simp only [Affine.whole,Function.comp_apply,Shell.pad,Matrix.add_apply,Shell.slice_test,Shell.off_test,ran]
  split_ifs <;> rfl

end YM.Integration.ConditionalAffineDraws
