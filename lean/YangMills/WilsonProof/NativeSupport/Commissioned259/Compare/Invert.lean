import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Runway

/-! # Gram planned in M.4. Work beforehand through all the estimates of M.2 and M.3.

We follow the reflection proof with the roles of the axes as in `FVA2/O/Read/Point`:
choose **positive** time from origin to Far (separation 1 in subtraction units) and
still reflect the Far field. (Other choice compared to example in M.4.) -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 Matrix
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale O.Score O.Enh O.Canon Dframe O.Read MS.Theater
variable {G : Gauge} {I : Type*} {n m h z : ℕ} {V : Arenas G} {B : ℝ → Frames G} {R : ℝ→PowerSeries ℂ}
    {A : Matrix (Toon G h) (Toon G h) ℂ}

abbrev console (m : ℕ) (u : Toon G h) : Tags G h m := fun _=> prism (theory u)

/-- At unconverted, *same scale at both fields*. -/
lemma gram_identity (P : O.Canon.Physical V R B) (x y : Toon G h) (t : ℝ) :
    reading V (d:=fun _=>h) (e:=fun _=>h) (fun _=>le_rfl) (fun _=>le_rfl)
      (0:Points 1) RootG 0 t (fun _ => theory y) (console 1 x) = GramP G h x y := by
  rw [read_eq, crop_apply,Finset.sum_range_succ, Finset.sum_range_zero, zero_add,pow_zero,one_mul, coeff_mk, bareRow_apply, kernel_on V ok_wall]
  rw [P.wardRank h 2 _]; unfold Equator.iris; rw [Normalize.screen]; unfold GramP
  change Wick.moment G (forest (0:Points 1) (points fun _ : Fin 1 => nail)) _ = _
  rw [lamp nail,Maxwell.Free.bond_eval]; apply congr_arg; funext i; fin_cases i <;> rfl

def numbers (Z : Sec G h) : Toon G h → ℂ := fun b=> coord b Z
def panel (D : Toon G h → (Sec G h →ₗ[ℂ] ℂ)) : Matrix (Toon G h) (Toon G h) ℂ := fun b j=> D b (theory j)
def columns (H : (Sec G h →ₗ[ℂ] Sec G h)) : Matrix (Toon G h) (Toon G h) ℂ :=
  fun b j=> coord b (H (theory j))
lemma beats (D : (Sec G h →ₗ[ℂ] ℂ)) (v : Sec G h) : D v=∑i,D (theory i)*numbers v i := by
  nth_rw 1 [ ← all_sig v ]; rw [map_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [_root_.map_smul,smul_eq_mul,mul_comm]; rfl
lemma prints (D : Toon G h → (Sec G h →ₗ[ℂ] ℂ)) (v : Sec G h) : panel D *ᵥ numbers v = fun i=> D i v :=
  funext fun i=> Eq.symm (beats _ _)
lemma issued (H : Sec G h →ₗ[ℂ] Sec G h) (v : Sec G h) : columns H *ᵥ numbers v = numbers (H v) :=
  funext fun i=> Eq.symm (beats ((coord i).comp H) v)
lemma composition (D : Toon G h → (Sec G h →ₗ[ℂ] ℂ)) (H : Sec G h →ₗ[ℂ] Sec G h) :
    panel D * columns H = panel (fun i=> (D i).comp H) := by ext i j; exact Eq.symm (beats (D i) (H (theory j)))
lemma composition' (D H : Sec G h →ₗ[ℂ] Sec G h) : columns D * columns H = columns (D.comp H) := by ext i j; exact Eq.symm (beats ((coord i).comp D) (H (theory j)))
lemma one_matrix : columns (G:=G) (h:=h) LinearMap.id = 1 := by
  ext i j; unfold columns; rw [ LinearMap.id_apply,pivotδ,Matrix.one_apply ]; simp [eq_comm]

variable {X : Filter I}
section invert
variable {T : I → ℝ} (D R : I→ Toon G h → Sec G h →ₗ[ℂ] ℂ) (F : I → (Sec G h ≃ₗ[ℂ] Sec G h))
    (tight : Tendsto (panel ∘ R) X (𝓝 (GramP G h)))
    (related : ∀ᶠ i in X, ∀ j, (D i j).comp (F i).toLinearMap = R i j)
    (routed : ∀ b c, (fun i => columns (F i).toLinearMap b c) =O[X] fun i=> T i^h)

include tight related
lemma standard : ∀ᶠ i in X, IsUnit (panel (D i)) ∧
    (panel (D i))⁻¹ = columns (F i).toLinearMap * (panel (R i))⁻¹ := by
  let Gk := GramP G h; have H := (Matrix.isUnit_iff_isUnit_det Gk).mp (positive_unit GramP_pos)
  filter_upwards [ (continuous_id.matrix_det.continuousAt.tendsto.comp tight).eventually ( eventually_ne_nhds H.ne_zero ), related ] with i hi hr
  let E:= columns (F i).toLinearMap; let E':= columns (F i).symm.toLinearMap; let A:=panel (D i); let B:=panel (R i)
  have hm : IsUnit B.det := isUnit_iff_ne_zero.mpr hi
  have hb : A * E=B := (composition _ _).trans (congr_arg panel (funext hr))
  have right : A*(E*B⁻¹) = 1 := by rw [←mul_assoc, hb, mul_nonsing_inv _ hm]
  have hv : IsUnit A.det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul ((by rw [ ← Matrix.det_mul, right, Matrix.det_one ]; exact one_ne_zero : A.det * (E*B⁻¹).det ≠ 0 )))
  refine ⟨ (Matrix.isUnit_iff_isUnit_det A).mpr hv,?_⟩
  change A⁻¹=E*B⁻¹; nth_rw 1 [← mul_one (A⁻¹),← right]; rw [← mul_assoc,nonsing_inv_mul _ hv,one_mul]
include routed
lemma inverse (b c : Toon G h) : (fun i=> (panel (D i))⁻¹ b c)=O[X] (fun i=> T i ^ h) := by
  have H := (standard D R F tight related)
  have he : IsUnit (GramP G h) := positive_unit GramP_pos
  obtain hc : ContinuousAt (Ring.inverse) (GramP G h).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (((Matrix.isUnit_iff_isUnit_det _).mp he).ne_zero)
  have V := (continuousAt_matrix_inv (GramP G h) hc).tendsto.comp tight
  have ev (b c:Toon G h) : (fun i=>(panel (R i))⁻¹ b c) =O[X] fun i=>(1:ℝ) :=
    isBigO_const_of_tendsto (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp V b) c) one_ne_zero
  have hz (i : I): (columns (F i).toLinearMap * (panel (R i))⁻¹) b c =
      ∑ j, columns (F i).toLinearMap b j * (panel (R i))⁻¹ j c := Matrix.mul_apply ..
  have hp := IsBigO.sum (s:= (Finset.univ:Finset (Toon G h))) (fun j _=> ((routed b j).mul (ev j c)).congr_right (fun i=> mul_one ((T i)^h)))
  exact hp.congr' (H.mono fun i H=> (((congr_arg (fun A:Matrix (Toon G h) (Toon G h) ℂ=>A b c) H.2).trans (hz i)).symm)) (EventuallyEq.refl ..)
end invert

section recovery
variable (D : I→ Toon G h → Sec G h →ₗ[ℂ] ℂ) {g T : I→ℝ}
    (units : ∀ᶠ i in X, IsUnit (panel (D i))) (fee : ∀ j k, (fun i=>(panel (D i))⁻¹ j k)=O[X] (fun i=> T i^h))
include units fee
lemma recovers (A : I→Sec G h) (w : I → ℝ) (hp : ∀ b, (fun i=> D i b (A i)) =O[X] w) (b : Toon G h) :
    (fun i=> coord b (A i)) =O[X] fun i=>T i^h * w i := by
  apply (IsBigO.sum (s:=Finset.univ) (fun j _=> (fee b j).mul (hp j))).congr' ?_ (EventuallyEq.refl ..)
  filter_upwards [units] with i hi
  exact congr_fun (show (panel (D i))⁻¹ *ᵥ (fun j=> D i j (A i)) = numbers (A i) from by
    rw [← prints _ (A i), Matrix.mulVec_mulVec, nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hi), one_mulVec]) b
-- helper estimate each coordinate discrepancy via $w(T)$ and `checkPrice`
lemma linked (Y YX : I→ Toon G h →ℂ) (DX : I → Toon G h → Sec G h→ₗ[ℂ] ℂ) (packet c:I→ Sec G h)
    (P:ℕ) (φ:ℝ) (hp:∀ j,(fun i=> checkPrice (Y i j) (YX i j) (D i j) (DX i j) (packet i) (c i)) =O[X] margin P h φ g T) (hT:∀ᶠ i in X,0<T i) (b:Toon G h) :
    (fun i=> coord b (packet i - c i))=O[X] fun i=> T i ^ (-φ) * (g i)^P := by
  have H (i:I) (j : Toon G h) : ‖D i j (packet i-c i)‖ ≤ checkPrice (Y i j) (YX i j) (D i j) (DX i j) (packet i) (c i) := by
    let a:=Y i j; let u:=D i j; have h : u (packet i-c i)=(a-u (c i))-(a-u (packet i)) := by rw [map_sub]; abel
    rw [show D i j (packet i-c i)=_ from h]; refine (norm_sub_le ..).trans ?_ ; unfold checkPrice a u; have ht:= opPos (D i j-DX i j); have h0:= norm_nonneg (Y i j-YX i j);
    linarith [norm_nonneg (Y i j-YX i j-(D i j-DX i j) (c i))]
  refine (recovers D units fee (fun i=>packet i-c i) (margin P h φ g T) (fun b=>?_) b).congr' (EventuallyEq.refl ..) ?_
  · exact (IsBigO.of_bound' (Eventually.of_forall fun i=> (H i b).trans_eq (Real.norm_of_nonneg (checkPos ..)).symm)).trans (hp b)
  filter_upwards [hT] with i hi; unfold margin
  rw [←mul_assoc,← Real.rpow_natCast,←Real.rpow_add hi, show (↑h : ℝ) + - ((h:ℝ)+φ)=-φ by ring ]
end recovery
end YM.FVA2.GradedFar259.Comparing
