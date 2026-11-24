import YM.Integration.PhysicalAffineScalarUncut

/-! Full physical winding cutoff estimates and nonlinear first variations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarUncut

open Function Filter Lattice Wilson RG RG.Patch Axial Bloch Laurent Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.SectorMeasure.Presented Next.Fluctuations.Sector
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

namespace PathTail
open Set Metric Push.Uniform Push.AbsoluteSums

variable {G : Gauge} {c f : Side} {p : Clip} {σ C Λ Z : ℝ} {n : ℕ}
    {ratio : Ratio c f} (F : Forest ratio) (s : Signed) (W : PathData G)
    (i : Face (Per f)) (R d : ℕ)

def tailWeight (j : ℕ) : ℝ :=
  if (W.row i.2 j).2.length*d ≤ R then 0 else (W.row i.2 j).1

/-- With half the physical path exponent left for differentiated spatial
legs, the remaining half pays the removed length in original fine units. -/
theorem tail_budget (hd : 0<d) (hW : W.Bounds p σ C Λ) :
    SumBudget (fun j => |tailWeight W i R d j| * Real.exp ((σ/2)*(W.row i.2 j).2.length))
      (Real.exp (-(σ/2)*((R:ℝ)/d))*C) := by
  let E := Real.exp (-(σ/2)*((R:ℝ)/d))
  have hb := budget_scale (Real.exp_pos (-(σ/2)*((R:ℝ)/d))).le (hW.rows i.2)
  apply budget_mono hb (fun _ => by positivity)
  intro j
  by_cases hcut : (W.row i.2 j).2.length*d ≤ R
  · simpa only [tailWeight,if_pos hcut,abs_zero,zero_mul] using hb.1 j
  · rw [tailWeight,if_neg hcut]
    change |(W.row i.2 j).1| * Real.exp ((σ/2)*(W.row i.2 j).2.length) ≤
      E * (|(W.row i.2 j).1| * Real.exp (σ*(W.row i.2 j).2.length))
    rw [mul_left_comm E,show E=Real.exp (-(σ/2)*((R:ℝ)/d)) from rfl,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    have hlen : (R:ℝ) ≤ ((W.row i.2 j).2.length:ℝ)*(d:ℝ) := by
      exact_mod_cast (le_of_lt (lt_of_not_ge hcut))
    have hquot := (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr hlen
    nlinarith [mul_le_mul_of_nonneg_left hquot (half_pos hW.width).le]

def discarded (U : Config G f) :=
  ∑' j, tailWeight W i R d j • (W.row i.2 j).2.atSite U i.1

theorem removed (hW : W.Bounds p σ C Λ) (U : Config G f) :
    discarded W i R d U = W.ell U i - shorten W R d U i := by
  have he := (W.ell_dominated hW i).summable U
  have ht : Summable (shortenTerm W R d U i) := by
    apply (summable_norm_iff.mpr he).of_norm_bounded
    intro j
    unfold shortenTerm
    split
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  rw [discarded,PathData.ell,shorten,←he.tsum_sub ht]
  apply tsum_congr
  intro j
  by_cases h : (W.row i.2 j).2.length*d ≤ R <;>
    simp [tailWeight,shortenTerm,PathData.ellTerms,h]

/-- All coordinate tensors of an actual omitted signed row, rooted at the
physical plaquette and evaluated on the genuine joint fine/coarse chart. -/
theorem price (hd : 0<d) (hW : W.Bounds p σ C Λ) (hs : PaintSupply G n Z)
    (x : Positions (Joint F G)) (hx : x∈ball 0 1) :
    Beacon (address F G) (entryWidth n ratio.count (σ/2)) n
      (fun z => W.ell (signedFine F z s) i - shorten W R d (signedFine F z s) i)
      (affine s 0 i.1) x ((Real.exp (-(σ/2)*((R:ℝ)/d))*C)*rootsCost G Z (σ/2) n) := by
  let a := W.row i.2
  let w := tailWeight W i R d
  let M := rootsCost G Z (σ/2) n
  have ht := tail_budget W i R d hd hW
  have hm := roots_nn hs (half_pos hW.width)
  let U j := (|w j| * Real.exp ((σ/2)*(a j).2.length))*M
  have hU : SumBudget U ((Real.exp (-(σ/2)*((R:ℝ)/d))*C)*M) :=
    ⟨fun j => mul_nonneg (ht.1 j) hm,ht.2.1.mul_right M,by
      rw [show (∑' j,U j)=_ from tsum_mul_right]
      exact mul_le_mul_of_nonneg_right ht.2.2 hm⟩
  have he (j : ℕ) (z : Positions (Joint F G)) (hz : z∈ball 0 1) :=
    piece F s hs z (show ‖z‖ ≤ 1 from (show ‖z‖ < 1 by simpa using hz).le)
      i.1 (a j).2 (half_pos hW.width) (w j)
  have hwidth := width_positive (half_pos hW.width) n ratio.count
  simp_rw [←removed W i R d hW]
  refine beacon_tsum (u:=fun j z => w j • (a j).2.atSite (signedFine F z s) i.1)
    isOpen_ball (convex_ball (0:Positions (Joint F G)) 1).isPreconnected hU.2.1 hU ?_ hx ?_
  · intro j z hz
    obtain ⟨T,hT,hM⟩ := he j z hz
    exact hT.mono ((le_mul_of_one_le_right hT.nonneg (Real.one_le_exp (by positivity))).trans hM)
  intro j
  obtain ⟨T,hT,hM⟩ := he j x hx
  apply Beacon.mono _ hM
  apply Allows.beacon hT (s:=Set.univ) _ univ_mem hwidth.le
  intro u _ v _ hh
  exact congrArg (fun y : G.Color => w j • y) (slot_read F s i.1 _ le_rfl hh)

/-- Restrict the actual field sheet to the no-fluctuation coarse copy used
in the independent FIaf offset. Every color in every coarse link remains. -/
def coarseCopy (B : Gaussian.Vec (Raw G c)) : Positions (Joint F G) :=
  (paint F G).symm (decode B,0)

theorem same_field {S : StepData c f} (F : Forest S.ratio) (B : Gaussian.Vec (Raw G c)) :
    signedFine F (coarseCopy F B) s=shone S s B := by
  simp [signedFine,coarseCopy,fine,outer,shone,backdrop,lifted]

end PathTail
namespace RouteTail

private theorem same_guard {α : Sort*} {q : Prop} (d₁ d₂ : Decidable q) (yes no : α) :
    @ite α q d₁ yes no = @ite α q d₂ yes no := by
  rw [Subsingleton.elim d₁ d₂]
open Push.AbsoluteSums Set Finset
variable {G : Gauge} {n c f : Side} {S : StepData c f} {σ C L : ℝ}

private def full (U : Config G n) (a : Site n) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (z : Cover) : Pay G :=
  if keep z then rated U a (w z) (K z) else 0

private def cut (U : Config G n) (a : Site n) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (z : Cover) : Pay G :=
  if (w z).length*d ≤ R ∧ keep z then rated U a (w z) (K z) else 0

def price (σ L : ℝ) (R : ℕ) := Real.exp (σ/2 - (σ/2)*((R:ℝ)/L))

/-- Actual sum over discarded windings, retaining half of the input
exponential for root displacement and later differentiated transports. -/
theorem weighted (U : Config G n) (a : Site n) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (hs : 0≤σ) (hL : 0<L)
    (hw : ∀ z, (((w z).length*d:ℕ):ℝ) ≤ L*(1+size z))
    (hK : SumBudget (fun z => Real.exp (σ*size z)*‖K z‖) C) :
    SumBudget (fun z => Real.exp ((σ/2)*size z) *
      ‖full U a w K keep z - cut U a w K keep R d z‖) (price σ L R*C) := by
  have p := budget_scale (Real.exp_pos (σ/2-(σ/2)*((R:ℝ)/L))).le hK
  apply budget_mono p (fun _ => by positivity)
  intro z
  by_cases hcut : (w z).length*d ≤ R
  · simpa only [full,cut,hcut,true_and,sub_self,norm_zero,mul_zero] using p.1 z
  by_cases clean : keep z
  · simp only [full,cut,hcut,false_and,if_false,clean,if_true,sub_zero]
    have hR : (R:ℝ) ≤ (((w z).length*d:ℕ):ℝ) := by exact_mod_cast (le_of_lt (lt_of_not_ge hcut))
    have ht : (R:ℝ)/L ≤ 1+(size z:ℝ) := (div_le_iff₀ hL).mpr (by simpa only [mul_comm L] using hR.trans (hw z))
    rw [←mul_assoc,←Real.exp_add]
    apply mul_le_mul _ (Work.E03.norm_rated_le U a (w z) (K z)) (norm_nonneg _) (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left ht (by positivity : 0≤σ/2)]
  · simpa only [full,cut,hcut,false_and,if_false,clean,sub_zero,norm_zero,mul_zero] using p.1 z

theorem entry (U : Config G n) (a : Site n) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (hs : 0≤σ) (hL : 0<L)
    (hw : ∀ z, (((w z).length*d:ℕ):ℝ) ≤ L*(1+size z))
    (hK : SumBudget (fun z => Real.exp (σ*size z)*‖K z‖) C) :
    ‖(∑' z, full U a w K keep z) - ∑' z, cut U a w K keep R d z‖ ≤ price σ L R*C := by
  let b := full U a w K keep
  let v := cut U a w K keep R d
  have hprice := weighted U a w K keep R d hs hL hw hK
  have hdom (z : Cover) := le_mul_of_one_le_left (norm_nonneg (K z))
    (Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg (size z))))
  have hb : Summable b := hK.2.1.of_norm_bounded (fun z => by
    unfold b full
    split
    · exact (Work.E03.norm_rated_le ..).trans (hdom z)
    · rw [norm_zero]; exact hK.1 z)
  have hv : Summable v := hK.2.1.of_norm_bounded (fun z => by
    unfold v cut
    split
    · exact (Work.E03.norm_rated_le ..).trans (hdom z)
    · rw [norm_zero]; exact hK.1 z)
  have hbound (z : Cover) : ‖b z-v z‖ ≤ Real.exp ((σ/2)*size z)*‖b z-v z‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))
  have hnorm := hprice.2.1.of_nonneg_of_le (fun z => norm_nonneg (b z-v z)) hbound
  change ‖(∑' z, b z) - (∑' z, v z)‖ ≤ _
  rw [←hb.tsum_sub hv]
  exact (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hbound hprice.2.1).trans hprice.2.2)

set_option maxHeartbeats 800000 in
/-- Both the original fine residue and the full fine-scaled winding appear
in the cutoff. No finite volume cardinality is in this entry price. -/
theorem faces (T : Tube G S) (V : Config G c) (R : ℕ) (i : Twin f) (j : Twin c)
    (hs : 0≤σ) (h : T.R.mf.strip σ C) :
    ‖faceStack T V i j - T.Φ R V i j‖ ≤ price σ (5*(S.patch.L.val:ℝ)) R*C := by
  let a := mesh i
  let b := mesh j
  let r := S.ratio.residue a.1
  let K := T.R.mf (r,a.2) b.2
  let p := fun z => b.1=S.ratio.parent a.1+wrap c z
  let w := fun z => route (lift r) (S.patch.L.val • z) 1
  have hr := entry (replica S.ratio V) a.1 w K p R 1 hs
    (show 0<5*(S.patch.L.val:ℝ) by have := S.patch.L.property; positivity)
    (fun z => by
      rw [Nat.mul_one]
      have hk := length_face S.patch.L r z
      rw [route_size] at hk
      change ((route (lift r) (S.patch.L.val • z) 1).length:ℝ)≤_
      rw [route_size]
      exact_mod_cast hk) (h (r,a.2) b.2)
  have e₁ : faceStack T V i j=∑' z, full (replica S.ratio V) a.1 w K p z := by
    apply tsum_congr; intro z; unfold full
    exact same_guard _ _ _ _
  have e₂ : T.Φ R V i j=∑' z, cut (replica S.ratio V) a.1 w K p R 1 z := by
    apply tsum_congr; intro z; unfold casted cut
    simp only [Nat.mul_one]
    exact same_guard _ _ _ _
  rw [e₁,e₂]
  exact hr

set_option maxHeartbeats 800000 in
/-- The noise row uses the original coarse unit route and multiplies its
length by the actual block side, exactly as in the physical aperture. -/
theorem noises (T : Tube G S) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
    (hs : 0≤σ) (h : T.R.mn.strip σ C) :
    ‖noiseStack T V i j - T.Φ' R V i j‖ ≤ price σ (5*(S.patch.L.val:ℝ)) R*C := by
  let a := pole i
  let b := mesh j
  let K := T.R.mn a.2 b.2
  let p := fun z => b.1=a.1+wrap c z
  let w := fun z => route 0 z 1
  have hw (z : Cover) : (((w z).length*S.patch.L.val:ℕ):ℝ) ≤ (5*(S.patch.L.val:ℝ))*(1+size z) := by
    simp only [w,route_size,sub_zero,Nat.cast_mul]
    nlinarith [show 0≤(S.patch.L.val:ℝ)*(size z:ℝ) by positivity]
  have hr := entry V a.1 w K p R S.patch.L.val hs
    (show 0<5*(S.patch.L.val:ℝ) by have := S.patch.L.property; positivity) hw (h a.2 b.2)
  have e₁ : noiseStack T V i j=∑' z, full V a.1 w K p z := by
    apply tsum_congr; intro z; unfold full
    exact same_guard _ _ _ _
  have e₂ : T.Φ' R V i j=∑' z, cut V a.1 w K p R S.patch.L.val z := by
    apply tsum_congr; intro z; unfold priced cut
    exact same_guard _ _ _ _
  rw [e₁,e₂]
  exact hr

private theorem continuous_full (a : Site n) (w : Cover → Walk) (K : Cover → ℝ)
    (clean : Cover → Prop) (h : Summable (fun z => ‖K z‖)) :
    Continuous (fun U : Config G n => ∑' z, full U a w K clean z) := by
  refine continuous_tsum ?_ h ?_
  · intro z
    unfold full
    split
    · exact Push.SectorMeasure.rated_cont ..
    · exact continuous_const
  intro z U
  unfold full
  split
  · exact Work.E03.norm_rated_le ..
  · simp

private theorem full_unit (a : Site n) (w : Cover → Walk) (K : Cover → ℝ)
    (clean : Cover → Prop) (h : Summable (fun z => ‖K z‖)) :
    (∑' z, full (1:Config G n) a w K clean z) =
      Next.Fluctuations.scalar G (∑' z, if clean z then K z else 0) := by
  let L : ℝ →L[ℝ] Pay G := (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ G.Color)
  have he : Summable (fun z => if clean z then K z else (0:ℝ)) := h.of_norm_bounded (fun z => by
    split
    · exact le_rfl
    · simp)
  change _ = L (∑' z, if clean z then K z else 0)
  rw [L.map_tsum he]
  refine tsum_congr fun z => ?_
  have ht : travel (1:Config G n) a (w z)=1 := by rw [←link_one (G:=G)]; exact Push.stroll_zero ..
  by_cases hh : clean z
  · rw [full,if_pos hh,if_pos hh]
    apply ContinuousLinearMap.ext; intro v
    change K z • (G.adjoint (travel (1:Config G n) a (w z))) v=K z • v
    rw [ht,G.adjoint_one]
  · simp [full,hh]

theorem faces_continuous (T : Tube G S) (h : T.R.mf.safe) (i : Twin f) (j : Twin c) :
    Continuous (fun V : Config G c => faceStack T V i j) := by
  let a := mesh i
  let b := mesh j
  let r := S.ratio.residue a.1
  have hcopy : Continuous (replica (G:=G) S.ratio) := by
    unfold replica
    apply continuous_pi
    intro y
    split <;> fun_prop
  have hh := (continuous_full (G:=G) a.1 (fun z => route (lift r) (S.patch.L.val • z) 1)
    (T.R.mf (r,a.2) b.2) (fun z => b.1=S.ratio.parent a.1+wrap c z) (h (r,a.2) b.2)).comp hcopy
  convert hh using 1
  funext V
  apply tsum_congr
  intro z
  unfold full
  exact same_guard _ _ _ _

theorem noises_continuous (T : Tube G S) (h : T.R.mn.safe) (i : Bond c) (j : Twin c) :
    Continuous (fun V : Config G c => noiseStack T V i j) := by
  have hh := continuous_full (G:=G) (pole i).1 (fun z => route 0 z 1) (T.R.mn (pole i).2 (mesh j).2)
    (fun z => (mesh j).1=(pole i).1+wrap c z) (h (pole i).2 (mesh j).2)
  convert hh using 1
  funext V
  apply tsum_congr
  intro z
  by_cases hz : (mesh j).1=(pole i).1+wrap c z <;> simp [full,hz]

theorem faces_unit (T : Tube G S) (h : T.R.mf.safe) (i : Twin f) (j : Twin c) :
    faceStack T (1:Config G c) i j=Next.Fluctuations.flatF T i j := by
  let a := mesh i
  let b := mesh j
  let r := S.ratio.residue a.1
  simp only [faceStack,replica_one,Next.Fluctuations.flatF,installed,Matrix.submatrix_apply,split_co,id_eq,Row.acts,Matrix.of_apply]
  have hh := full_unit (G:=G) a.1 (fun z => route (lift r) (S.patch.L.val • z) 1) (T.R.mf (r,a.2) b.2)
    (fun z => b.1=S.ratio.parent a.1+wrap c z) (h (r,a.2) b.2)
  refine Eq.trans ?_ (Eq.trans hh ?_)
  · apply tsum_congr; intro z
    unfold full
    exact same_guard _ _ _ _
  · apply congrArg (Next.Fluctuations.scalar G)
    apply tsum_congr; intro z
    exact same_guard _ _ _ _

theorem noises_unit (T : Tube G S) (h : T.R.mn.safe) (i : Bond c) (j : Twin c) :
    noiseStack T (1:Config G c) i j=Next.Fluctuations.flatI T i j := by
  have hh := full_unit (G:=G) (pole i).1 (fun z => route 0 z 1) (T.R.mn (pole i).2 (mesh j).2)
    (fun z => (mesh j).1=(pole i).1+wrap c z) (h (pole i).2 (mesh j).2)
  refine Eq.trans ?_ (Eq.trans hh ?_)
  · apply tsum_congr; intro z
    by_cases hz : (mesh j).1=(pole i).1+wrap c z <;> simp [full,hz]
  · unfold Next.Fluctuations.flatI
    apply congrArg (Next.Fluctuations.scalar G)
    apply tsum_congr; intro z
    by_cases hz : (mesh j).1=(pole i).1+wrap c z
    · simp only [if_pos hz]
    · simp only [if_neg hz]

end RouteTail
namespace FirstOrder
open Next.Fluctuations AnalyticNext.ConnectedActivity.Aff Work.F03
open scoped Topology

variable {G : Gauge} {n c f : Side} {S : StepData c f}

theorem plaquette (W : PathData G) (p : Clip) {σ C Λ : ℝ} (hW : W.Bounds p σ C Λ)
    (a : LogField G n) (i : Twin n) :
    Tendsto (fun t : ℝ => t⁻¹ • plaquetteRows W p (represent (t • a)) i) (𝓝[≠] 0)
      (𝓝 (xLin p W a i)) := by
  cases hg : i.2
  · have hc := hasDerivAt_iff_tendsto_slope_zero.mp (curvature_of_hasDerivAt (face_deriv i.1 a))
    have h0 : G.curvature (faceValue (represent ((0:ℝ) • a)) i.1)=0 := by
      rw [zero_smul,show faceValue (represent (0:fieldDir G n 1)) i.1 =1 from Push.stroll_zero ..,G.curvature_unit]
    simp only [h0,sub_zero,zero_add] at hc
    simpa only [plaquetteRows,xLin,hg,Bool.false_eq_true,if_false,shoot,smul_comm (Inv.inv _)] using
      hc.const_smul (Real.sqrt p.direct)
  · simpa only [plaquetteRows,xLin,hg,if_true] using ell_limit W hW i.1 a

private theorem zip_limit {α β : Type} [Fintype β] (a : α) (K : Config G n → α → β → Pay G)
    (hc : ∀ i, Continuous (fun V => K V a i)) (v : LogField G n)
    (y : ℝ → β → G.Color) (row : β → G.Color)
    (hy : ∀ j, Tendsto (fun t : ℝ => t⁻¹ • y t j) (𝓝[≠] 0) (𝓝 (row j))) :
    Tendsto (fun t : ℝ => t⁻¹ • Pressure.zip (K (represent (t • v))) (y t) a)
      (𝓝[≠] 0) (𝓝 (Pressure.zip (K 1) row a)) := by
  have hv : Continuous (fun t : ℝ => represent (t • v)) := by
    unfold represent RG.increment collect
    fun_prop
  have hl : Tendsto (fun t : ℝ => represent (t • v)) (𝓝[≠] 0) (𝓝 1) := by
    simpa only [zero_smul,link_one] using (hv.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  simp only [Pressure.zip,Finset.smul_sum,←ContinuousLinearMap.map_smul]
  apply tendsto_finsetSum
  intro j _
  have hh := ((hc j).continuousAt (x:=1)).tendsto.comp hl
  have ev : Continuous (fun p : Pay G × G.Color => p.1 p.2) := continuous_fst.clm_apply continuous_snd
  exact ev.continuousAt.tendsto.comp (hh.prodMk_nhds (hy j))

/-- The actual signed, nonlinear, full physical row evaluated along an
arbitrary fine/coarse field pair, retaining the original mean selector. -/
def physicalRow (T : Tube G S) (k : S.Choices) (s : Signed) (a : LogField G f) (b : LogField G c)
    (i : Twin f ⊕ Bond c) (t : ℝ) : G.Color :=
  let u := represent (t • orient s a)
  let v := represent (t • orient s b)
  let y := plaquetteRows T.down T.low v
  i.elim (fun j => plaquetteRows T.up T.high u j - Pressure.zip (faceStack T v) y j)
    (fun j => Z S (S.prediction u (choice s k)) v j - Pressure.zip (noiseStack T v) y j)

/-- Complete linear response of the two input fields in an original signed row. -/
def variation (T : Tube G S) (s : Signed) (a : LogField G f) (b : LogField G c) (i : Twin f ⊕ Bond c) : G.Color :=
  let u := orient s a
  let v := orient s b
  i.elim (fun j => xLin T.high T.up u j - Fout T v j) (fun j => zLin S u v j - Qout T v j)

theorem joint_row (T : Tube G S) {P : Teller G} (hP : P.Funds S T) (k : S.Choices) (s : Signed)
    (a : LogField G f) (b : LogField G c) (i : Twin f ⊕ Bond c) :
    Tendsto (fun t : ℝ => t⁻¹ • physicalRow T k s a b i t) (𝓝[≠] 0) (𝓝 (variation T s a b i)) := by
  obtain ⟨_,_,hup,hdown⟩ := hP.feeds
  rw [← hP.high] at hup
  rw [← hP.low] at hdown
  have hf := Row.rights P.η _ hP.crosses.2.2.1 P.width.le
  have hn := Row.rights P.η _ hP.crosses.1 P.width.le
  let v := orient s b
  let u := orient s a
  have hy (j : Twin c) := plaquette T.down T.low hdown v j
  cases i with
  | inl j =>
    have hz := zip_limit j (faceStack T) (RouteTail.faces_continuous T hf j) v _ _ hy
    have ha := (plaquette T.up T.high hup u j).sub hz
    simp only [physicalRow,variation,Sum.elim_inl,smul_sub]
    have hflat : faceStack T (1:Config G c)=flatF T := funext fun a => funext fun b => RouteTail.faces_unit T hf a b
    simpa only [u,v,hflat,Fout,Limage] using ha
  | inr j =>
    have hz := zip_limit j (noiseStack T) (RouteTail.noises_continuous T hn j) v _ _ hy
    have hh := hasDerivAt_iff_tendsto_slope_zero.mp (zTest_deriv (S:=S) (Push.SectorMeasure.funds_branch hP) (choice s k) j (u,v))
    have hzero : zTest S (choice s k) j ((0:ℝ) • (u,v))=0 := by
      simp [zTest,Z,Push.settled S (Push.SectorMeasure.funds_branch hP) j (choice s k),G.curvature_unit]
    simp only [zero_add,hzero,sub_zero] at hh
    have ha := hh.sub hz
    simp only [physicalRow,variation,Sum.elim_inr,smul_sub]
    have hflat : noiseStack T (1:Config G c)=flatI T := funext fun a => funext fun b => RouteTail.noises_unit T hn a b
    simpa only [zTest,Prod.smul_fst,Prod.smul_snd,u,v,hflat,Qout,Limage] using ha

/-- Linearizing the actual uncut nonlinear row along the prescribed
relative stationary displacement gives zero at every signed face/bond,
before any summation of squares, Gaussian contraction or tree average. -/
theorem stationary_row (T : Tube G S) {P : Teller G} {A B : Bed} (hA : Alongside A B T)
    (hP : P.Funds S T) (k : S.Choices) (s : Signed) (F : Forest S.ratio) (b : LogField G c)
    (i : Twin f ⊕ Bond c) :
    Tendsto (fun t : ℝ => t⁻¹ • physicalRow T k s (station T F b) b i t) (𝓝[≠] 0) (𝓝 0) := by
  have hfit := escape T hA hP s F b
  have hz : variation T s (station T F b) b i=0 := by
    cases i with
    | inl j => exact sub_eq_zero.mpr (congrFun hfit.1 j)
    | inr j => exact sub_eq_zero.mpr (congrFun hfit.2 j)
  rw [← hz]
  exact joint_row T hP k s _ b i

def copyField (S : StepData c f) (b : LogField G c) : LogField G f :=
  AnalyticNext.ConnectedActivity.Aff.form (linearCopy S.ratio (collect G b))

private theorem copy_path (s : Signed) (b : LogField G c) (t : ℝ) :
    represent (t • orient s (copyField S b)) = pull s 0 (replica S.ratio (represent (t • b))) := by
  have hlin : t • copyField S b = copyField S (t • b) := by
    unfold copyField linearCopy collect AnalyticNext.ConnectedActivity.Aff.form
    funext j
    simp only [Pi.smul_apply]
    split
    next => rw [smul_zero]
    next => rfl
  rw [←orient_linear,orient_represents,hlin]
  congr 1
  unfold copyField represent
  rw [collect_form]
  exact Precision.exp_copy ..

/-- The full uncut affine offset actually uses the replicated tangent on every
fine plaquette and original noise selector. -/
theorem offset_along (T : Tube G S) (k : S.Choices) (b : FreeResolvent.Vec G c 1)
    (t : ℝ) (i : Slots S) :
    tape (offset T k (t • b)) i = slip • physicalRow T k i.1 (copyField S (decode b)) (decode b) i.2 t := by
  have hd : decode (t • b) = t • decode b := (plain G c 1).map_smul t b
  have hf : shone S i.1 (t • b) = represent (t • orient i.1 (copyField S (decode b))) := by
    rw [copy_path,shone,backdrop,hd]
  have hc : pull i.1 0 (represent (decode (t • b))) = represent (t • orient i.1 (decode b)) := by
    rw [hd,←orient_linear,orient_represents]
  simp only [offset,tape.apply_symm_apply,physicalRow,hf,hc]

/-- The true derivative of the entire unshifted fine/noise/coarse source on
independently specified physical coarse directions. -/
theorem offset_rate (T : Tube G S) {P : Teller G} (hP : P.Funds S T) (k : S.Choices)
    (b : FreeResolvent.Vec G c 1) (i : Slots S) :
    Tendsto (fun t : ℝ => t⁻¹ • tape (offset T k (t • b)) i) (𝓝[≠] 0)
      (𝓝 (slip • variation T i.1 (copyField S (decode b)) (decode b) i.2)) := by
  simp only [offset_along,smul_comm (Inv.inv _)]
  exact (joint_row T hP k i.1 _ _ i.2).const_smul slip

end FirstOrder
end YM.Integration.PhysicalAffineScalarUncut
end
