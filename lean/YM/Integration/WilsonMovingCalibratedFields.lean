import YM.Integration.WilsonMovingCompactTransfer
import YM.OPE.Cards.Pressure

/-! Simultaneous convergence of the actual finite Wilson multilinear
evaluation at all admitted fine regulator locations, for independently
calibrated physical source labels on the same reporting subfilter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingCalibratedFields
open Function Finset Filter Set Metric MeasureTheory Lattice Wilson RG Source Extraction Word
open PhysicalNext.Repeat.Legato FullVolume
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (R : Run G) (hG : G.Simple) {n : ℕ}
    {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)

private theorem coordinate {ι : Type*} {l : Filter ι} {Z : ι → Type*}
    (valid : (i:ι) → Z i → Prop) (measured limiting : (i:ι) → Z i → ℂ)
    (w : ι → ℂ) (c : ℂ) (price : ℝ) (hl : ∀ i z,valid i z → ‖limiting i z‖ ≤ price)
    (hq : ∀ ε : ℝ,0<ε → ∀ᶠ i in l,∀ z,valid i z → dist (measured i z) (limiting i z)<ε)
    (hw : Tendsto w l (𝓝 c)) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i in l,∀ z,valid i z → ‖w i * measured i z - c * limiting i z‖ < ε := by
  let A := ‖c‖+2+|price|
  have hA : 0<A := by dsimp [A]; positivity
  let η:= ε/A
  have hη : 0<η := div_pos he hA
  have saved : (‖c‖+1+|price|)*η<ε := by
    calc _ < A*η := mul_lt_mul_of_pos_right (by dsimp [A]; linarith) hη
         _ = ε := by dsimp [η]; field_simp
  filter_upwards [hq η hη,hw.eventually (Metric.ball_mem_nhds c hη),
    hw.eventually (Metric.ball_mem_nhds c one_pos)] with i read earned one z hz
  have hc : ‖w i‖ ≤ ‖c‖+1 := by
    have h := norm_sub_norm_le (w i) c
    have h₁ : ‖w i-c‖<1 := by simpa only [mem_ball,dist_eq_norm] using one
    linarith
  have diff : ‖measured i z-limiting i z‖ ≤ η := by simpa only [dist_eq_norm] using (read z hz).le
  have coef : ‖w i-c‖≤η := by simpa only [mem_ball,dist_eq_norm] using (show dist (w i) c<η from earned).le
  calc
    _ = ‖w i*(measured i z-limiting i z)+(w i-c)*limiting i z‖ := by ring_nf
    _ ≤ ‖w i‖*‖measured i z-limiting i z‖+‖w i-c‖*‖limiting i z‖ := by
      simpa only [norm_mul] using norm_add_le (w i*(measured i z-limiting i z)) ((w i-c)*limiting i z)
    _ ≤ (‖c‖+1)*η+η*|price| := add_le_add (mul_le_mul hc diff (norm_nonneg _) (by positivity))
      (mul_le_mul coef ((hl i z hz).trans (le_abs_self _)) (norm_nonneg _) hη.le)
    _ = (‖c‖+1+|price|)*η := by ring
    _ < ε := saved

include hG F in
theorem paid {l : Filter (ℕ×ℕ)} (hl : l ≤ f.fuse) (d : Caps n) (w : (ℕ×ℕ) → R.family.book.Vector d)
    (c : R.family.book.Vector d) (hw : ∀ j,Tendsto (fun i=>w i j) l (𝓝 (c j)))
    (K : Set (Points n)) (hk : IsCompact K) (sep : K ⊆ conf n) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ i : ℕ×ℕ in l, ∀ z : Positions n, tag (R.family.S.a i.1) z ∈ K →
      dist (R.family.ensemble (N:=i.1) (p:=i.2) d (wrap _ ∘ z) (w i))
        (S.value d (tag (R.family.S.a i.1) z) c) < ε := by
  let C := R.family
  let E (i) := dial (L:=C.book) d i
  let J := (i:Fin n) → (C.book.coord (d i)).Index
  letI : Fintype J := Pi.instFintype
  let Y (j:J) i := E i (j i)
  let W (b:C.book.Vector d) (j:J) := ∏ i,(E i).repr (b i) (j i)
  have expansion (X : Moment C.book n d) (b:C.book.Vector d) :
      X b = ∑ j:J, W b j * X (Y j) := by
    have eq : b=fun i=>∑ a,(E i).repr (b i) a • E i a := funext fun i => ((E i).sum_repr _).symm
    conv_lhs => rw [eq]
    rw [MultilinearMap.map_sum]
    exact sum_congr rfl fun j _ => X.map_smul_univ (fun k=>(E k).repr (b k) (j k)) _
  let sites (i : ℕ×ℕ) (z : Positions n) := tag (C.S.a i.1) z
  let H (i : ℕ×ℕ) (z : Positions n) := C.ensemble d (wrap (C.side i.1 i.2) ∘ z)
  let V (i : ℕ×ℕ) (z : Positions n) := S.value d (sites i z)
  let η:= ε/(Fintype.card J+1 : ℝ)
  have hη : 0<η := div_pos he (by positivity)
  have each (j:J) : ∀ᶠ i : ℕ×ℕ in l,∀ z : Positions n,sites i z∈K →
      ‖W (w i) j*H i z (Y j)-W c j*V i z (Y j)‖<η := by
    let tags : Fin n→C.book.Token := fun k => ⟨d k,Y j k⟩
    obtain ⟨B,hB⟩:=hk.exists_bound_of_continuousOn ((S.smooth_read F.room.kernel.smooth tags).continuousOn.mono sep)
    apply coordinate (fun i z=>sites i z∈K) _ _ (fun i=>W (w i) j) (W c j) B
      (fun i z hz=>hB _ hz) _ _ η hη
    · intro x hx
      exact (WilsonMovingCompactTransfer.measured R hG F tags K hk sep x hx).filter_mono hl
    · exact tendsto_finsetProd _ (fun k _=> ((E k).coord (j k)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hw k))
  filter_upwards [eventually_all.mpr each] with i hi z hz
  change dist (H i z (w i)) (V i z c) < ε
  rw [dist_eq_norm,expansion (H i z) (w i),expansion (V i z) c,←sum_sub_distrib]
  calc
    _ ≤ ∑ j:J,‖W (w i) j*H i z (Y j)-W c j*V i z (Y j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j:J, η := sum_le_sum fun j _ => (hi j z hz).le
    _ = (Fintype.card J:ℝ)*η := by simp
    _ < ((Fintype.card J:ℝ)+1)*η := by nlinarith [hη]
    _ = ε := by dsimp [η]; field_simp

end YM.Integration.WilsonMovingCalibratedFields

