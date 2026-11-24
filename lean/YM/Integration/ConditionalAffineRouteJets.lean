import YM.Push.STATIONARY_UNIFORM.Scatter
import YM.Integration.PhysicalAffineScalarUncut
import YM.Push.FREE_RESOLVENT.TrackBill
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Orientation
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Drift
import YM.Push.FREE_RESOLVENT.TensorPrice

/-! Full fine-to-coarse face and noise winding variations in the original independent field chart. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
open YM.Laurent
noncomputable section

namespace YM.Integration.ConditionalAffineSeries
open Function Filter Set Metric Push.Uniform
open scoped BigOperators Classical Topology ContDiff

theorem sum_smooth {E D ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    {s : Set E} {u : ι → E→D} {C : ι→ℝ} {n : ℕ} (hs : IsOpen s) (hc : IsPreconnected s)
    (hC : Summable C) (h : ∀ i x, x∈s → Allows (n+1) (u i) x (C i)) :
    ContDiffOn ℝ n (fun x => ∑' i, u i x) s := by
  let U := fun x => ∑' i, u i x
  have H (k : ℕ) (hk : k≤n) : DifferentiableOn ℝ (iteratedFDerivWithin ℝ k U s) s := by
    intro x hx
    let F i := iteratedFDeriv ℝ k (u i)
    have he : Summable (fun i => F i x) := .of_norm_bounded hC (fun i => (h i x hx).norm_le k (by omega))
    have hd := hasFDerivAt_tsum_of_isPreconnected hC hs hc
      (fun i y hy => ((h i y hy).analytic.differentiableAt_iteratedFDeriv (m:=k) (by simp)).hasFDerivAt)
      (fun i y hy => by rw [fderiv_iteratedFDeriv]; simpa only [comp_apply,LinearIsometryEquiv.norm_map] using (h i y hy).norm_le (k+1) (by omega)) hx he hx
    have hg : iteratedFDerivWithin ℝ k U s =ᶠ[𝓝 x] fun y => ∑' i, F i y := by
      filter_upwards [hs.mem_nhds hx] with y hy
      rw [iteratedFDerivWithin_of_isOpen k hs hy]
      exact iterated_at_sum hs hc hC h hy k (by omega)
    exact (hd.congr_of_eventuallyEq hg).differentiableAt.differentiableWithinAt
  exact (contDiffOn_nat_iff_continuousOn_differentiableOn hs.uniqueDiffOn).2
    ⟨fun k hk => (H k hk).continuousOn,fun k hk => H k hk.le⟩

/-- Removing a common cutoff from an absolutely convergent series commutes
with the genuine continuous linear row evaluation. -/
theorem masked {I E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace E] [CompleteSpace M]
    (D : E→L[ℝ] M) (u : I→E) (hit keep : I→Prop)
    (hf : Summable (fun z => if hit z then u z else 0))
    (hc : Summable (fun z => if keep z ∧ hit z then u z else 0)) :
    D ((∑' z,if hit z then u z else 0)-(∑' z,if keep z ∧ hit z then u z else 0)) =
      ∑' z,if hit z ∧ ¬keep z then D (u z) else 0 := by
  rw [←hf.tsum_sub hc,D.map_tsum (hf.sub hc)]
  apply tsum_congr
  intro z
  by_cases h : hit z <;> by_cases k : keep z <;> simp [h,k]

theorem summable_mask {I E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (v : I→E) (p : I→Prop) (a : I→ℝ) (ha : Summable a) (hn : ∀ z,0≤a z)
    (h : ∀ z,‖v z‖≤a z) : Summable (fun z => if p z then v z else 0) := by
  apply ha.of_norm_bounded
  intro z; split
  · exact h z
  rw [norm_zero]; exact hn z

/-- Apply an evaluation to the full-minus-cut absolutely convergent operator series. -/
theorem evaluated {I E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace E] [CompleteSpace M]
    (D : E →L[ℝ] M) (F : I → E) (hit : I → Prop) (length : I → ℕ) (R : ℕ)
    (V W : E) (A : I → ℝ) (ha : Summable A) (hn : ∀ i, 0 ≤ A i) (hb : ∀ i, ‖F i‖ ≤ A i)
    (hv : V = ∑' i, if hit i then F i else 0)
    (hw : W = ∑' i, if length i ≤ R ∧ hit i then F i else 0) :
    D (V - W) = ∑' i, if hit i ∧ R < length i then D (F i) else 0 := by
  let full (i : I) := if hit i then F i else 0
  let cut (i : I) := if length i ≤ R ∧ hit i then F i else 0
  have hf : Summable full := ha.of_norm_bounded fun i => by
    unfold full
    split
    · exact hb i
    rw [norm_zero]; exact hn i
  have hc : Summable cut := ha.of_norm_bounded fun i => by
    unfold cut
    split
    · exact hb i
    rw [norm_zero]; exact hn i
  have hv' : V = ∑' i, full i := hv
  have hw' : W = ∑' i, cut i := hw
  rw [hv', hw', ←hf.tsum_sub hc, D.map_tsum (hf.sub hc)]
  apply tsum_congr
  intro i
  by_cases hk : length i ≤ R
  · have hl : ¬R < length i := not_lt_of_ge hk
    by_cases h : hit i <;> simp [full,cut,h,hk,hl]
  have hl : R < length i := Nat.lt_of_not_ge hk
  by_cases h : hit i <;> simp [full,cut,h,hk,hl]

end YM.Integration.ConditionalAffineSeries

namespace YM.Integration.ConditionalAffineRouteJets
open Function Filter Lattice RG Wilson Precision Tree Exterior Bloch Matrix Pressure
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD Push.AbsoluteSums
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- One transport entry between two original color labels. -/
def bead (S : StepData c f) (s : Signed) (x : Site f) (w : Walk) (q : ℝ)
    (a b : G.ColorIndex) (B : Vec G c 1) :=
  rated (shone S s B) x w q (EuclideanSpace.basisFun G.ColorIndex ℝ b) a

/-- Place this particular walk, with its original weight, in one row
position of the existing differentiated transport estimator. -/
private def singleWalk (P : PathData G) (w : Walk) (o : PlaqAxes) (q : ℝ) : PathData G :=
  { P with row := fun _ k => (if k=0 then q else 0,⟨w,o⟩) }

private def first (x : Site f) (o : PlaqAxes) (a : G.ColorIndex) : tile G f := (x,plaquette o,a)
private def last (x : Site f) (w : Walk) (o : PlaqAxes) (b : G.ColorIndex) : tile G f :=
  (wrap f (RG.Slot.offset ⟨w,o⟩)+x,plaquette o,b)

private lemma read (S : StepData c f) (s : Signed) (P : PathData G) (x : Site f) (w : Walk)
    (o : PlaqAxes) (q : ℝ) (a b : G.ColorIndex) :
    edgework S s (singleWalk P w o q) all (first x o a) (last x w o b) 0 = bead S s x w q a b := by
  funext B
  simp [edgework,singleWalk,all,first,last,element,bead,rated,PiLp.smul_apply]

/-- Independent derivative positions and the orientation-correct actual
row root. The dummy plaquette pair just names the native color matrix
entry. Its actual shared route and every charged link are unchanged. -/
theorem bead_price (P : PathData G) (s : Signed) (x : Site f) (w : Walk) (o : PlaqAxes)
    (a b : G.ColorIndex) (q ν δ : ℝ) (hν : 0<ν) (hδ : 0≤δ) (n : ℕ)
    (hd : 2*n*δ ≤ ν/2) (l : List (raw G c)) (hl : l.length≤n) :
    (marks G c δ).pay l (S.ratio.parent (affine s 0 x)) * |jet (ray G c) (bead S s x w q a b) l 0| ≤
      (|q| *Real.exp (ν*(w.length+4:ℝ)))*elbow G n (ν/4) := by
  have H := (track_entry (σ:=ν) (d:=δ) (γ:=0) S s (singleWalk P w o q) all
    (first x o a) (last x w o b) 0 n hν l hl hδ le_rfl (by simpa using hd) 0 (fun _ _ => Nat.zero_le _)).1
  rw [read S s P x w o q a b] at H
  simpa [facetReserve,singleWalk,first,named,Cost.weight,RG.Slot.length] using H

/-- A sequence of actual discarded winding terms. Its cutoff uses the
physical route length with the designated fine/coarse conversion. -/
def removed (S : StepData c f) (s : Signed) (x : Site f) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (a b : G.ColorIndex) (z : Cover) : Vec G c 1 → ℝ :=
  if keep z ∧ R < (w z).length*d then bead S s x (w z) (K z) a b else 0

def fee (G : Gauge) (n : ℕ) (σ L : ℝ) (R : ℕ) :=
  Real.exp (4*(σ/(4*L)) + 3*σ/4 - (σ/2)*((R:ℝ)/L)) * elbow G n ((σ/(4*L))/4)

/-- Sum all removed winding labels with their own exponential displacement
and every independent ordered field visit. This estimate precedes any
passage to a full winding integral or contraction with a plaquette row. -/
theorem winding (P : PathData G) (s : Signed) (x : Site f) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (o : PlaqAxes) (a b : G.ColorIndex) (n : ℕ)
    (σ L C δ : ℝ) (hσ : 0<σ) (hL : 0<L) (hd : 0<d) (hδ : 0≤δ)
    (hδ' : 2*n*δ ≤ (σ/(4*L))/2) (hR : ∀ z, (((w z).length*d : ℕ):ℝ) ≤ L*(1+(size z:ℝ)))
    (hK : SumBudget (fun z => Real.exp (σ*(size z:ℝ))*‖K z‖) C)
    (l : List (raw G c)) (hl : l.length≤n) :
    SumBudget (fun z => Real.exp ((σ/4)*(size z:ℝ)) *
      ((marks G c δ).pay l (S.ratio.parent (affine s 0 x)) *
        |jet (ray G c) (removed S s x w K keep R d a b z) l 0|)) (fee G n σ L R*C) := by
  let ν := σ/(4*L)
  have hν : 0<ν := div_pos hσ (by positivity)
  have hνL : ν*L=σ/4 := by unfold ν; field_simp
  have hz : 0≤fee G n σ L R := mul_nonneg (Real.exp_pos _).le (elbow_nn ..)
  have pay := budget_scale hz hK
  refine budget_mono pay (fun z => mul_nonneg (Real.exp_pos _).le (mul_nonneg ((marks G c δ).pay_pos ..).le (abs_nonneg _))) ?_
  intro z
  by_cases he : keep z ∧ R < (w z).length*d
  · rw [removed,if_pos he]
    have hm := bead_price (S:=S) P s x (w z) o a b (K z) ν δ hν hδ n hδ' l hl
    have hlen : ((w z).length : ℝ) ≤ (((w z).length*d:ℕ):ℝ) :=
      by exact_mod_cast Nat.le_mul_of_pos_right _ hd
    have h₁ : (R:ℝ)/L ≤ 1+(size z:ℝ) := (div_le_iff₀ hL).2 (by
      rw [mul_comm]; exact (show (R:ℝ) ≤ (((w z).length*d:ℕ):ℝ) by exact_mod_cast he.2.le).trans (hR z))
    have h₂ : ν*(w z).length ≤ (σ/4)*(1+(size z:ℝ)) := by
      calc
        _ ≤ ν*(L*(1+(size z:ℝ))) := mul_le_mul_of_nonneg_left (hlen.trans (hR z)) hν.le
        _ = _ := by rw [←mul_assoc,hνL]
    have hex : (σ/4)*(size z:ℝ) + ν*((w z).length+4:ℝ) ≤
        (4*ν + 3*σ/4 - (σ/2)*((R:ℝ)/L)) + σ*(size z:ℝ) := by
      nlinarith only [h₂,mul_le_mul_of_nonneg_left h₁ (show 0≤σ/2 by positivity)]
    have hpow : Real.exp ((σ/4)*(size z:ℝ))*Real.exp (ν*((w z).length+4:ℝ)) ≤
      Real.exp (4*ν + 3*σ/4 - (σ/2)*((R:ℝ)/L)) * Real.exp (σ*(size z:ℝ)) := by
      rw [←Real.exp_add,←Real.exp_add]; exact Real.exp_monotone hex
    calc
      _ ≤ Real.exp ((σ/4)*(size z:ℝ)) * ((|K z| *Real.exp (ν*((w z).length+4:ℝ)))*elbow G n (ν/4)) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      _ = (Real.exp ((σ/4)*(size z:ℝ))*Real.exp (ν*((w z).length+4:ℝ))) * (|K z| *elbow G n (ν/4)) := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hpow (mul_nonneg (abs_nonneg (K z)) (elbow_nn G n (ν/4)))
        refine h.trans_eq ?_
        unfold fee
        rw [Real.norm_eq_abs]
        dsimp only [ν]
        ring
  · rw [removed,if_neg he,zero_null,abs_zero,mul_zero,mul_zero]
    exact pay.1 z

private def smooth (S : StepData c f) (s : Signed) (P : PathData G) (x : Site f)
    (w : Cover → Walk) (K : Cover → ℝ) (keep : Cover → Prop) (R d : ℕ) (o : PlaqAxes)
    (a b : G.ColorIndex) (z : Cover) : Vec G c 1 → ℝ :=
  if keep z ∧ R < (w z).length*d then
    sheetEdge S s (singleWalk P (w z) o (K z)) all (first x o a) (last x (w z) o b) 0 else 0

/-- Differentiate the full discarded winding sum itself. One common germ
of regularized coarse fields works for every winding simultaneously. -/
theorem regularizes (P : PathData G) (s : Signed) (x : Site f) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (o : PlaqAxes) (a b : G.ColorIndex)
    (σ L C : ℝ) (hσ : 0<σ) (hL : 0<L) (hd : 0<d)
    (hR : ∀ z, (((w z).length*d:ℕ):ℝ) ≤ L*(1+(size z:ℝ)))
    (hK : SumBudget (fun z => Real.exp (σ*(size z:ℝ))*‖K z‖) C) (l : List (raw G c)) :
    ContDiffAt ℝ l.length (fun B => ∑' z, removed S s x w K keep R d a b z B) 0 ∧
    HasSum (fun z => jet (ray G c) (removed S s x w K keep R d a b z) l 0)
      (jet (ray G c) (fun B => ∑' z, removed S s x w K keep R d a b z B) l 0) := by
  let k := l.length
  let ν := σ/(4*L)
  have hν : 0<ν := div_pos hσ (by positivity)
  have hνL : ν*L=σ/4 := by unfold ν; field_simp
  let F := smooth S s P x w K keep R d o a b
  let K₀ (z : Cover) := (|K z| * Real.exp (ν*((w z).length+4:ℝ))) * elbow G k ν
  have hk (z : Cover) : 0≤K₀ z := mul_nonneg (by positivity) (elbow_nn ..)
  have hf (z : Cover) : Ceiling k (K₀ z) (F z) := by
    unfold F smooth
    split
    · simpa [K₀,slotPrice,singleWalk,RG.Slot.length] using
        sheetEdge_ceiling S s (singleWalk P (w z) o (K z)) all (first x o a) (last x (w z) o b) 0 k hν
    exact (Ceiling.ceiling_const (0:ℝ)).mono ((norm_zero.trans_le (hk z)))
  let M := Real.exp (4*ν+σ/4)*elbow G k ν
  have hM : 0≤M := mul_nonneg (Real.exp_pos _).le (elbow_nn ..)
  have hw : Summable K₀ := by
    apply (budget_scale hM hK).2.1.of_norm_bounded
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (hk z)]
    have hlen : ((w z).length:ℝ)≤(((w z).length*d:ℕ):ℝ) := by exact_mod_cast Nat.le_mul_of_pos_right _ hd
    have h₂ : ν*(w z).length ≤ (σ/4)*(1+(size z:ℝ)) := by
      calc
        _ ≤ ν*(L*(1+(size z:ℝ))) := mul_le_mul_of_nonneg_left (hlen.trans (hR z)) hν.le
        _ = _ := by rw [←mul_assoc,hνL]
    have hp : Real.exp (ν*((w z).length+4:ℝ)) ≤ Real.exp (4*ν+σ/4)*Real.exp (σ*(size z:ℝ)) := by
      rw [←Real.exp_add,Real.exp_le_exp]
      nlinarith only [h₂,mul_nonneg hσ.le (Nat.cast_nonneg (size z))]
    have hc := mul_le_mul_of_nonneg_left hp (abs_nonneg (K z))
    have hsc := mul_le_mul_of_nonneg_right hc (elbow_nn G k ν)
    simpa only [K₀,M,Real.norm_eq_abs,mul_comm,mul_left_comm,mul_assoc] using hsc
  have common : ∀ᶠ B : Vec G c 1 in 𝓝 0, ∀ z, F z B = removed S s x w K keep R d a b z B := by
    filter_upwards [returns (G:=G) S s] with B hB
    intro z
    by_cases hz : keep z ∧ R < (w z).length*d
    · rw [show F z B = edgework S s (singleWalk P (w z) o (K z)) all (first x o a) (last x (w z) o b) 0 B by
        simp only [F,smooth,if_pos hz,sheetEdge,edgework,hB],read,removed,if_pos hz]
    simp only [F,smooth,removed,if_neg hz]
  let f := fun B => ∑' z, F z B
  have hg (z : Cover) : ContDiff ℝ ((k:ℕ∞):ℕ∞ω) (F z) := (hf z).smooth
  let u := fun (_ : ℕ) => K₀
  have hu (j : ℕ) : (j:ℕ∞)≤(k:ℕ∞) → Summable (u j) := fun _ => hw
  have hj (j : ℕ) (z : Cover) (B : Vec G c 1) (hj : (j:ℕ∞)≤(k:ℕ∞)) :
      ‖iteratedFDeriv ℝ j (F z) B‖ ≤ u j z := (hf z).op j B (by exact_mod_cast hj)
  have hc : ContDiffAt ℝ k f 0 := (contDiff_tsum hg hu hj).contDiffAt
  refine ⟨hc.congr_of_eventuallyEq (common.mono fun _ h => (tsum_congr h).symm),?_⟩
  have hh : HasSum (fun z => iteratedFDeriv ℝ k (F z) 0) (iteratedFDeriv ℝ k f 0) := by
    rw [iteratedFDeriv_tsum_apply hg hu hj (k:=k) le_rfl 0]
    exact (Summable.of_norm_bounded hw (fun z => hj k z 0 le_rfl)).hasSum
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vec G c 1) ℝ (ray G c ∘ l.get)
  have he : HasSum (fun z => jet (ray G c) (F z) l 0) (jet (ray G c) f l 0) := A.hasSum hh
  have hind z := identical (ray G c) (common.mono fun _ h => h z) l
  have hall := identical (ray G c) (A:=f) (common.mono fun _ h => tsum_congr h) l
  simpa only [hind,hall] using he

/-- Collapse the admitted winding sum only after pricing each physical
winding. The outgoing endpoint weight can be paid from the cover distance. -/
theorem differentiates (P : PathData G) (s : Signed) (x : Site f) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (o : PlaqAxes) (a b : G.ColorIndex)
    (σ L C : ℝ) (hσ : 0<σ) (hL : 0<L) (hd : 0<d)
    (hR : ∀ z, (((w z).length*d:ℕ):ℝ) ≤ L*(1+(size z:ℝ)))
    (hK : SumBudget (fun z => Real.exp (σ*(size z:ℝ))*‖K z‖) C) (l : List (raw G c)) :
    HasSum (fun z => jet (ray G c) (removed S s x w K keep R d a b z) l 0)
      (jet (ray G c) (fun B => ∑' z, removed S s x w K keep R d a b z B) l 0) :=
  (regularizes P s x w K keep R d o a b σ L C hσ hL hd hR hK l).2

theorem summed (P : PathData G) (s : Signed) (x : Site f) (w : Cover → Walk) (K : Cover → ℝ)
    (keep : Cover → Prop) (R d : ℕ) (o : PlaqAxes) (a b : G.ColorIndex) (n : ℕ)
    (σ L C δ κ : ℝ) (hσ : 0<σ) (hL : 0<L) (hd : 0<d) (hδ : 0≤δ)
    (hδ' : 2*n*δ ≤ (σ/(4*L))/2) (hκ : 0≤κ) (hborn : ∀ z, keep z → κ ≤ Real.exp ((σ/4)*(size z:ℝ)))
    (hR : ∀ z, (((w z).length*d:ℕ):ℝ) ≤ L*(1+(size z:ℝ)))
    (hK : SumBudget (fun z => Real.exp (σ*(size z:ℝ))*‖K z‖) C)
    (l : List (raw G c)) (hl : l.length≤n) :
    (κ * (marks G c δ).pay l (S.ratio.parent (affine s 0 x))) *
      |jet (ray G c) (fun B => ∑' z, removed S s x w K keep R d a b z B) l 0| ≤ fee G n σ L R*C := by
  let M := (marks G c δ).pay l (S.ratio.parent (affine s 0 x))
  let j (z : Cover) := jet (ray G c) (removed S s x w K keep R d a b z) l 0
  have hM : 0≤M := ((marks G c δ).pay_pos ..).le
  let k (z : Cover) := Real.exp ((σ/4)*(size z:ℝ))*(M*|j z|)
  have hpay : SumBudget k (fee G n σ L R*C) :=
    winding P s x w K keep R d o a b n σ L C δ hσ hL hd hδ hδ' hR hK l hl
  have hb (z : Cover) : ‖(κ*M)*j z‖ ≤ k z := by
    by_cases hk : keep z
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg hκ hM),mul_assoc]
      exact mul_le_mul_of_nonneg_right (hborn z hk) (mul_nonneg hM (abs_nonneg _))
    have hj : j z=0 := by unfold j removed; simp [hk,zero_null]
    unfold k
    rw [hj,mul_zero,norm_zero,abs_zero,mul_zero,mul_zero]
  have hs := differentiates (S:=S) P s x w K keep R d o a b σ L C hσ hL hd hR hK l
  have hh : Summable (fun z => ‖(κ*M)*j z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hpay.2.1
  have hm := (norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum hb hpay.2.1).trans hpay.2.2)
  rw [(hs.mul_left (κ*M)).tsum_eq,Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg hκ hM)] at hm
  exact hm

private def entry (a b : G.ColorIndex) : Pay G →L[ℝ] ℝ :=
  (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) a).comp
    (ContinuousLinearMap.apply ℝ G.Color (EuclideanSpace.basisFun G.ColorIndex ℝ b))

private def faceWalk (S : StepData c f) (i : Twin f) (z : Cover) :=
  route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • z) 1
private def faceCoef (T : Tube G S) (i : Twin f) (j : Twin c) (z : Cover) :=
  T.R.mf (S.ratio.residue (mesh i).1,(mesh i).2) (mesh j).2 z
private def hits (S : StepData c f) (i : Twin f) (j : Twin c) (z : Cover) :=
  (mesh j).1=S.ratio.parent (mesh i).1+wrap c z

def faceTail (T : Tube G S) (s : Signed) (R : ℕ) (i : Twin f) (j : Twin c) (a b : G.ColorIndex)
    (B : Vec G c 1) : ℝ :=
  let V := pull s 0 (represent (decode B))
  entry a b (PhysicalAffineScalarUncut.faceStack T V i j - T.Φ R V i j)

theorem cover_distance (x : Site c) (z : Cover) : separation x (x+wrap c z) ≤ size z := by
  rw [add_comm x,separation_comm,separation,add_sub_cancel_right]
  apply Finset.sup_le
  intro a ha
  apply (Corona.lap z a).trans
  change (z a).natAbs≤∑ v : Axis,(z v).natAbs
  exact Finset.single_le_sum (f:=fun v : Axis => (z v).natAbs) (fun _ _ => Nat.zero_le _) ha

theorem same_guard {α : Sort*} {q : Prop} (d₁ d₂ : Decidable q) (yes no : α) :
    @ite α q d₁ yes no=@ite α q d₂ yes no := by rw [Subsingleton.elim d₁ d₂]

private theorem mileage (S : StepData c f) (i : Twin f) (z : Cover) :
    (((faceWalk S i z).length*1:ℕ):ℝ)≤5*(S.patch.L.val:ℝ)*(1+(size z:ℝ)) := by
  rw [Nat.mul_one]
  have h := PhysicalAffineScalarUncut.RouteTail.length_face S.patch.L (S.ratio.residue (mesh i).1) z
  rw [PhysicalAffineScalarUncut.RouteTail.route_size] at h
  unfold faceWalk
  rw [PhysicalAffineScalarUncut.RouteTail.route_size]
  exact_mod_cast h

private theorem source_series (T : Tube G S) (V : Config G c) (R : ℕ) (i : Twin f) (j : Twin c) :
    let F (z : Cover) := rated (replica S.ratio V) (mesh i).1 (faceWalk S i z) (faceCoef T i j z)
    PhysicalAffineScalarUncut.faceStack T V i j=(∑' z,if hits S i j z then F z else 0) ∧
    T.Φ R V i j=(∑' z,if (faceWalk S i z).length≤R ∧ hits S i j z then F z else 0) := by
  intro F
  constructor
  · unfold PhysicalAffineScalarUncut.faceStack
    apply tsum_congr; intro z
    exact same_guard _ _ _ _
  unfold Tube.Φ leap
  apply tsum_congr; intro z
  unfold casted
  exact same_guard _ _ _ _

theorem rated_bound {n : Side} (U : Config G n) (x : Site n) (w : Cover → Walk) (K : Cover → ℝ)
    {σ : ℝ} (hs : 0 ≤ σ) (z : Cover) :
    ‖rated U x (w z) (K z)‖ ≤ Real.exp (σ*(size z:ℝ))*‖K z‖ :=
  (Work.E03.norm_rated_le U x (w z) (K z)).trans
    (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg _))))

private theorem face_evaluation (T : Tube G S) (s : Signed) (R : ℕ) (i : Twin f) (j : Twin c)
    (a b : G.ColorIndex) (B : Vec G c 1) (z : Cover) :
    let U := replica S.ratio (pull s 0 (represent (decode B)))
    (if hits S i j z ∧ R < (faceWalk S i z).length then
      entry a b (rated U (mesh i).1 (faceWalk S i z) (faceCoef T i j z)) else 0) =
      removed S s (mesh i).1 (faceWalk S i) (faceCoef T i j) (hits S i j) R 1 a b z B := by
  intro U
  have hu : U = shone S s B :=
    AnalyticBridge.SectorAffine.Identity.top_copy (S:=S) s (represent (decode B))
  by_cases h : hits S i j z ∧ R < (faceWalk S i z).length
  · have h' : hits S i j z ∧ R < (faceWalk S i z).length * 1 := by simpa only [Nat.mul_one] using h
    rw [if_pos h, removed, if_pos h', hu]; rfl
  have h' : ¬ (hits S i j z ∧ R < (faceWalk S i z).length * 1) := by simpa only [Nat.mul_one] using h
  rw [if_neg h, removed, if_neg h']; rfl

/-- On the signed coarse log coordinate this sum is literally the true
full transported `mf` entry minus the selected physical aperture `Φ`. -/
theorem genuine_face (T : Tube G S) (s : Signed) (R : ℕ) (i : Twin f) (j : Twin c)
    (a b : G.ColorIndex) {σ C : ℝ} (hσ : 0≤σ) (h : T.R.mf.strip σ C) :
    faceTail T s R i j a b = fun B => ∑' z, removed S s (mesh i).1 (faceWalk S i)
      (faceCoef T i j) (hits S i j) R 1 a b z B := by
  funext B
  let V := pull s 0 (represent (decode B))
  let U := replica S.ratio V
  let K := faceCoef T i j
  let A (z : Cover) := Real.exp (σ*(size z:ℝ))*‖K z‖
  have pay : SumBudget A C := h (S.ratio.residue (mesh i).1, (mesh i).2) (mesh j).2
  obtain ⟨full, cut⟩ := source_series T V R i j
  change entry a b (PhysicalAffineScalarUncut.faceStack T V i j - T.Φ R V i j) = _
  have hs := ConditionalAffineSeries.evaluated (entry a b)
    (fun z => rated U (mesh i).1 (faceWalk S i z) (K z)) (hits S i j)
    (fun z => (faceWalk S i z).length) R _ _ A pay.2.1 pay.1
    (rated_bound U (mesh i).1 (faceWalk S i) K hσ) full cut
  exact hs.trans (tsum_congr (face_evaluation T s R i j a b B))

/-- The real retained phase-series entry is smooth through the specified
finite order, including order zero, on the original physical chart. -/
theorem face_regular (P : Teller G) (T : Tube G S) (hP : P.Funds S T) (s : Signed) (R : ℕ)
    (i : Twin f) (j : Twin c) (a b : G.ColorIndex) (n : ℕ) : ContDiffAt ℝ n (faceTail T s R i j a b) 0 := by
  have hK := hP.crosses.2.2.1
  let l : List (raw G c) := List.replicate n (0,coord 0,a)
  have hL : 0<5*(S.patch.L.val:ℝ) := by have h:=S.patch.L.property; positivity
  have h := (regularizes (S:=S) T.up s (mesh i).1 (faceWalk S i) (faceCoef T i j) (hits S i j) R 1 i.1.2 a b
    P.η (5*(S.patch.L.val:ℝ)) (P.C/(S.patch.L.val:ℝ)^2) P.width hL (by decide)
    (mileage S i)
    (hK _ _) l).1
  rw [genuine_face T s R i j a b P.width.le hK]
  simpa only [l,List.length_replicate] using h

/-- Actual `mf` aperture discrepancy at every fixed field derivative,
retaining its two physical positions, every Lie color, and all derivative
positions before they are summed into the affine offset. -/
theorem faces (P : Teller G) (T : Tube G S) (hP : P.Funds S T) (s : Signed) (R : ℕ)
    (i : Twin f) (j : Twin c) (a b : G.ColorIndex) (n : ℕ) (δ : ℝ) (hδ : 0≤δ)
    (hδ' : 2*n*δ ≤ (P.η/(4*(5*(S.patch.L.val:ℝ))))/2) (l : List (raw G c)) (hl : l.length≤n) :
    let L := 5*(S.patch.L.val:ℝ)
    ((native c).weight (P.η/4) (S.ratio.parent (mesh i).1) (mesh j).1 *
      (marks G c δ).pay l (S.ratio.parent (affine s 0 (mesh i).1))) *
      |jet (ray G c) (faceTail T s R i j a b) l 0| ≤ fee G n P.η L R * (P.C/(S.patch.L.val:ℝ)^2) := by
  have hc := hP.crosses.2.2.1
  rw [genuine_face T s R i j a b P.width.le hc]
  apply summed T.up s (mesh i).1 (faceWalk S i) (faceCoef T i j) (hits S i j) R 1 i.1.2 a b n
    P.η (5*(S.patch.L.val:ℝ)) (P.C/(S.patch.L.val:ℝ)^2) δ _ P.width
    (by have hL:=S.patch.L.property; positivity) (by decide) hδ hδ' (Real.exp_pos _).le
  · intro z hz
    apply Real.exp_monotone
    apply mul_le_mul_of_nonneg_left _ (div_nonneg P.width.le (by norm_num))
    rw [show (mesh j).1=S.ratio.parent (mesh i).1+wrap c z from hz]
    change (separation (S.ratio.parent (mesh i).1) (S.ratio.parent (mesh i).1+wrap c z):ℝ)≤(size z:ℝ)
    exact_mod_cast cover_distance (S.ratio.parent (mesh i).1) z
  · exact mileage S i
  · exact hc _ _
  exact hl

end YM.Integration.ConditionalAffineRouteJets

namespace YM.Integration.ConditionalAffineNoiseWinding
open Function Filter Lattice Wilson RG Precision Tree Pressure Bloch Exterior
  AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset
  FreeResolvent.TestD Push.AbsoluteSums
open Push.Uniform (bolt)
open Set Metric
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

private lemma constant (z : G.Color) (p : Site c) (n : ℕ) (δ : ℝ) :
    Point (0:PriceCoords G c) p δ n (fun _ => z) ‖z‖ := by
  refine ⟨contDiffAt_const,fun l _ => ?_⟩
  by_cases h : l=[]
  · subst l
    rw [zeroth]
    change 1 * ‖z‖ ≤ _
    rw [one_mul]
  rw [jet_const bolt l h,norm_zero,mul_zero]
  exact norm_nonneg _

def removed (T : Tube G S) (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
    (b : G.Color) (z : Cover) (B : PriceCoords G c) : G.Color :=
  let w := route 0 z 1
  if (mesh j).1 = (pole i).1 + wrap c z ∧ R < w.length*S.patch.L.val then
    T.R.mn (pole i).2 (mesh j).2 z • G.adjoint (travel (pull s 0 (field V B)) (pole i).1 w) b else 0

/-- The constants here are uniform in the side, aperture, signed
selector, and packet. The independent ordered coarse field positions
are the true price coordinates, and the input color can be any unit ball vector. -/
theorem terms (G : Gauge) (n : ℕ) (σ : ℝ) (hσ : 0<σ) :
    ∃ δ N : ℝ, 0<δ ∧ 0<N ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (C : ℝ),
      T.R.mn.strip σ C → ∀ (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
        (b : G.Color) (_ : ‖b‖≤1) (l : List (Coord G c)) (_ : l.length≤n),
      SumBudget (fun z : Cover => Real.exp ((σ/4)*(size z:ℝ)) * ((marks G c δ).pay l (s.act i.1) *
        ‖jet bolt (removed T s V R i j b z) l 0‖)) (N*Real.exp (-(σ/2)*((R:ℝ)/S.patch.L.val))*C) := by
  obtain ⟨Q,hQ,hletters⟩ := field_letters G n
  obtain ⟨δ,N,hδ,hN,H⟩ := carried G (κ:=σ/4) (by positivity) n Q 1 hQ.le zero_lt_one
  refine ⟨δ,N,hδ,hN,?_⟩
  intro c f S T C h s V R i j b hb l hl
  let U (B : PriceCoords G c) := pull s 0 (field V B)
  let W (z : Cover) := route 0 z 1
  let K (z : Cover) := T.R.mn (pole i).2 (mesh j).2 z
  let P := (marks G c δ).pay l (s.act i.1)
  let M := N*Real.exp (-(σ/2)*((R:ℝ)/S.patch.L.val))
  have hP : 0≤P := ((marks G c δ).pay_pos ..).le
  have hM : 0≤M := mul_nonneg hN.le (Real.exp_pos _).le
  have hK := h (pole i).2 (mesh j).2
  have pay := budget_scale hM hK
  refine budget_mono pay (fun _ => mul_nonneg (Real.exp_pos _).le (mul_nonneg hP (norm_nonneg _))) ?_
  intro z
  have hw : (W z).length=size z := by simp [W,PhysicalAffineScalarUncut.RouteTail.route_size]
  by_cases hk : (mesh j).1 = (pole i).1 + wrap c z ∧ R < (W z).length*S.patch.L.val
  · have he : ∀ B : PriceCoords G c, removed T s V R i j b z B = K z • G.adjoint (travel (U B) i.1 (W z)) b :=
      fun _ => if_pos hk
    have hz : Point (0:PriceCoords G c) (s.act (stop i.1 (W z))) δ n (fun _ => b) (1*1) :=
      (constant b _ n δ).mono le_rfl (by simpa using hb)
    have head := H U s.act (hletters S V s).1 1 1 zero_le_one zero_le_one le_rfl i.1 (W z)
      (fun _ => b) δ hδ.le le_rfl hz
    have bound : P * ‖jet bolt (removed T s V R i j b z) l 0‖ ≤
        |K z| *(N*Real.exp ((σ/4)*(size z:ℝ))) := by
      rw [funext he]
      simpa only [one_smul,hw,mul_one] using (head.scale (K z)).bound l hl
    have hL : 0 < (S.patch.L.val:ℝ) := by exact_mod_cast S.patch.L.property
    have hcut : (R:ℝ)/S.patch.L.val ≤ size z := (div_le_iff₀ hL).2 (by
      have ht := hk.2.le
      rw [hw] at ht
      exact_mod_cast ht)
    have hp : Real.exp ((σ/4)*(size z:ℝ)) * Real.exp ((σ/4)*(size z:ℝ)) ≤
        Real.exp (-(σ/2)*((R:ℝ)/S.patch.L.val)) * Real.exp (σ*(size z:ℝ)) := by
      rw [←Real.exp_add,←Real.exp_add,Real.exp_le_exp]
      nlinarith only [mul_le_mul_of_nonneg_left hcut (show 0≤σ/2 by positivity)]
    calc
      _ ≤ Real.exp ((σ/4)*(size z:ℝ)) * (|K z| *(N*Real.exp ((σ/4)*(size z:ℝ)))) :=
        mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le
      _ ≤ _ := by
        have HH := mul_le_mul_of_nonneg_right hp (mul_nonneg (abs_nonneg (K z)) hN.le)
        simpa only [M,K,Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using HH
  · have he : removed T s V R i j b z = 0 := funext fun _ => if_neg hk
    rw [he,FreeResolvent.Affine.zero_null,norm_zero,mul_zero,mul_zero]
    exact pay.1 z

/-- The original uncut-minus-cut noise winding function has the termwise
derivative at every independent tuple. The analytic bound on a whole
neighborhood justifies this equality before evaluating the rooted price. -/
private theorem envelope (T : Tube G S) (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
    (b : G.Color) {σ C : ℝ} (hσ : 0<σ) (hK : T.R.mn.strip σ C) (k : ℕ) :
    ∃ r : ℝ, 0<r ∧ ∃ D : Cover→ℝ, Summable D ∧ ∀ z (B : PriceCoords G c), B∈ball 0 r →
      Push.Uniform.Allows k (removed T s V R i j b z) B (D z) := by
  obtain ⟨r,Q,hr,hQ,H⟩ := coordinates G k
  obtain ⟨A,hA,HH⟩ := travel_coupon G k Q hQ.le (half_pos hσ)
  let U (B : PriceCoords G c) := pull s 0 (field V B)
  let w (z : Cover) := route 0 z 1
  let K (z : Cover) := T.R.mn (pole i).2 (mesh j).2 z
  let Z := G.colorScale⁻¹*(2^k*(2^k*A*(G.colorScale*‖b‖))*A)
  have hZ : 0≤Z := by unfold Z; have hG:=G.colorScale_pos; positivity
  let D (z : Cover) := (Real.exp (σ*(size z:ℝ))*‖K z‖)*Z
  have hD : Summable D := (hK (pole i).2 (mesh j).2).2.1.mul_right _
  have hv (B : PriceCoords G c) (hB : B∈ball 0 r) (i : Bond c) :
       Push.Uniform.Allows k (fun y => G.mat (U y i)) B Q := by
    have H' := (H B (le_of_lt (by simpa [mem_ball_zero_iff] using hB)) V).1
    unfold U
    simp_rw [ProjectorNext.Equivariance.pull_formula]
    split
    · exact (H' _).inverse (f:=fun y => field V y (ProjectorNext.Equivariance.bonds s 0 i))
    exact H' _
  have hf (z : Cover) (B : PriceCoords G c) (hB : B∈ball 0 r) :
      Push.Uniform.Allows k (removed T s V R i j b z) B (D z) := by
    have hw : (w z).length=size z := by simp [w,PhysicalAffineScalarUncut.RouteTail.route_size]
    by_cases hk : (mesh j).1=(pole i).1+wrap c z ∧ R<(w z).length*S.patch.L.val
    · have H' := Push.Uniform.travel_jets (U:=U) (hv B hB) i.1 (le_refl (w z).length)
      have ht : Push.Uniform.Allows k (fun y => G.mat (travel (U y) i.1 (w z))) B
          (A*Real.exp ((σ/2)*(size z:ℝ))) := H'.mono (by simpa only [hw] using HH (w z).length)
      have he : removed T s V R i j b z =
          fun y => K z • G.adjoint (travel (U y) i.1 (w z)) b := funext fun _ => if_pos hk
      rw [he]
      apply ((adjoint_cost (U:=fun y => travel (U y) i.1 (w z)) ht (Push.Uniform.allows_const B (le_refl ‖b‖))).smul _).mono
      have he' : Real.exp ((σ/2)*(size z:ℝ))*Real.exp ((σ/2)*(size z:ℝ)) = Real.exp (σ*(size z:ℝ)) := by
        rw [←Real.exp_add]; congr 1; ring
      unfold D Z
      rw [Real.norm_eq_abs,←he']
      apply le_of_eq
      ring
    have he : removed T s V R i j b z = 0 := funext fun _ => if_neg hk
    rw [he]
    exact Push.Uniform.allows_const B ((norm_zero.trans_le (mul_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hZ)))
  exact ⟨r,hr,D,hD,hf⟩

theorem differentiates (T : Tube G S) (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
    (b : G.Color) {σ C : ℝ} (hσ : 0<σ) (hK : T.R.mn.strip σ C) (l : List (Coord G c)) :
    HasSum (fun z => jet bolt (removed T s V R i j b z) l 0)
      (jet bolt (fun B => ∑' z, removed T s V R i j b z B) l 0) := by
  let k := l.length
  obtain ⟨r,hr,D,hD,hf⟩ := envelope T s V R i j b hσ hK k
  have h0 : (0:PriceCoords G c) ∈ ball 0 r := mem_ball_self hr
  have hs := Push.Uniform.iterated_at_sum isOpen_ball (convex_ball (0:PriceCoords G c) r).isPreconnected hD hf h0 k le_rfl
  have hsum := (Summable.of_norm_bounded hD (fun z => (hf z 0 h0).norm_le k le_rfl)).hasSum
  rw [←hs] at hsum
  let E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => PriceCoords G c) G.Color (bolt ∘ l.get)
  exact E.hasSum hsum

/-- The discarded functions really are the full `mn` transport-minus-Φ′,
with the original coarse winding and scaled cutoff, for any background. -/
private theorem source_series (T : Tube G S) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c) :
    let F (z : Cover) := rated V (pole i).1 (route 0 z 1) (T.R.mn (pole i).2 (mesh j).2 z)
    let p (z : Cover) := (mesh j).1=(pole i).1+wrap c z
    PhysicalAffineScalarUncut.noiseStack T V i j=(∑' z,if p z then F z else 0) ∧
    T.Φ' R V i j=(∑' z,if (route 0 z 1).length*S.patch.L.val≤R ∧ p z then F z else 0) := by
  intro F p
  constructor
  · unfold PhysicalAffineScalarUncut.noiseStack
    apply tsum_congr; intro z
    exact ConditionalAffineRouteJets.same_guard _ _ _ _
  unfold Tube.Φ' kick lane
  apply tsum_congr; intro z
  unfold priced
  exact ConditionalAffineRouteJets.same_guard _ _ _ _

private theorem noise_evaluation (T : Tube G S) (s : Signed) (V : Config G c) (R : ℕ)
    (i : Bond c) (j : Twin c) (b : G.Color) (B : PriceCoords G c) (z : Cover) :
    let U := pull s 0 (field V B)
    (if (mesh j).1 = (pole i).1 + wrap c z ∧ R < (route 0 z 1).length*S.patch.L.val then
      (rated U (pole i).1 (route 0 z 1) (T.R.mn (pole i).2 (mesh j).2 z)) b else 0) =
      removed T s V R i j b z B := by
  intro U
  by_cases h : (mesh j).1 = (pole i).1 + wrap c z ∧ R < (route 0 z 1).length*S.patch.L.val
  · rw [if_pos h, removed, if_pos h]; rfl
  rw [if_neg h, removed, if_neg h]

theorem genuine (T : Tube G S) (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
    (b : G.Color) {σ C : ℝ} (hσ : 0≤σ) (h : T.R.mn.strip σ C) :
    (fun B => (PhysicalAffineScalarUncut.noiseStack T (pull s 0 (field V B)) i j -
      T.Φ' R (pull s 0 (field V B)) i j) b) = fun B => ∑' z, removed T s V R i j b z B := by
  funext B
  let U := pull s 0 (field V B)
  let K (z : Cover) := T.R.mn (pole i).2 (mesh j).2 z
  let p (z : Cover) := (mesh j).1 = (pole i).1 + wrap c z
  let A (z : Cover) := Real.exp (σ*(size z:ℝ))*‖K z‖
  have pay : SumBudget A C := h (pole i).2 (mesh j).2
  let F (z : Cover) := rated U (pole i).1 (route 0 z 1) (K z)
  obtain ⟨full, cut⟩ := source_series T U R i j
  have hv : PhysicalAffineScalarUncut.noiseStack T U i j = ∑' z,
      @ite (Pay G) (p z) (Classical.propDecidable (p z)) (F z) 0 := by
    apply full.trans
    apply tsum_congr
    intro z
    exact ConditionalAffineRouteJets.same_guard _ _ _ _
  have hc : T.Φ' R U i j = ∑' z,
      @ite (Pay G) ((route 0 z 1).length*S.patch.L.val ≤ R ∧ p z)
        (@instDecidableAnd ((route 0 z 1).length*S.patch.L.val ≤ R) (p z)
          (Nat.decLe ((route 0 z 1).length*S.patch.L.val) R) (Classical.propDecidable (p z))) (F z) 0 := by
    apply cut.trans
    apply tsum_congr
    intro z
    exact ConditionalAffineRouteJets.same_guard _ _ _ _
  let E := ContinuousLinearMap.apply ℝ G.Color b
  change E (PhysicalAffineScalarUncut.noiseStack T U i j - T.Φ' R U i j) = _
  have hs := ConditionalAffineSeries.evaluated E (fun z => rated U (pole i).1 (route 0 z 1) (K z))
    p (fun z => (route 0 z 1).length*S.patch.L.val) R _ _ A pay.2.1 pay.1
    (ConditionalAffineRouteJets.rated_bound U (pole i).1 (fun z => route 0 z 1) K hσ) hv hc
  refine hs.trans (tsum_congr fun z => ?_)
  exact (ConditionalAffineRouteJets.same_guard _ _ _ _).trans (noise_evaluation T s V R i j b B z)

/-- A positive differentiability grade with both genuine noise/plaquette
positions weighted and every independent coarse derivative ray retained.
Its half-width cutoff gain is in true physical coarse path units. -/
theorem regular_score (T : Tube G S) (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
    (b : G.Color) {σ C : ℝ} (hσ : 0<σ) (hK : T.R.mn.strip σ C) (n : ℕ) :
    ContDiffAt ℝ n (fun B => (PhysicalAffineScalarUncut.noiseStack T (pull s 0 (field V B)) i j -
      T.Φ' R (pull s 0 (field V B)) i j) b) 0 := by
  obtain ⟨r,hr,D,hD,hf⟩ := envelope T s V R i j b hσ hK (n+1)
  rw [genuine T s V R i j b hσ.le hK]
  exact (ConditionalAffineSeries.sum_smooth isOpen_ball (convex_ball (0:PriceCoords G c) r).isPreconnected hD hf).contDiffAt (ball_mem_nhds _ hr)

theorem charged (G : Gauge) (n : ℕ) (σ : ℝ) (hσ : 0<σ) :
    ∃ δ N : ℝ, 0<δ ∧ 0<N ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (C : ℝ),
      T.R.mn.strip σ C → ∀ (s : Signed) (V : Config G c) (R : ℕ) (i : Bond c) (j : Twin c)
        (b : G.Color) (_ : ‖b‖≤1) (l : List (Coord G c)) (_ : l.length≤n),
      (FreeResolvent.native c).weight (σ/4) i.1 (mesh j).1 * (marks G c δ).pay l (s.act i.1) *
        ‖jet bolt (fun B => (PhysicalAffineScalarUncut.noiseStack T (pull s 0 (field V B)) i j -
          T.Φ' R (pull s 0 (field V B)) i j) b) l 0‖ ≤ N*Real.exp (-(σ/2)*((R:ℝ)/S.patch.L.val))*C := by
  obtain ⟨δ,N,hδ,hN,H⟩ := terms G n σ hσ
  refine ⟨δ,N,hδ,hN,?_⟩
  intro c f S T C h s V R i j b hb l hl
  have HH := H S T C h s V R i j b hb l hl
  let D := (FreeResolvent.native c).weight (σ/4) i.1 (mesh j).1
  let P := (marks G c δ).pay l (s.act i.1)
  let J (z : Cover) := jet bolt (removed T s V R i j b z) l 0
  have hP : 0≤P := ((marks G c δ).pay_pos ..).le
  have hDP : 0≤D*P := mul_nonneg (Real.exp_pos _).le hP
  have hz (z : Cover) : ‖(D*P) • J z‖ ≤ Real.exp ((σ/4)*(size z:ℝ)) * (P*‖J z‖) := by
    by_cases hk : (mesh j).1=(pole i).1+wrap c z
    · have he : D≤Real.exp ((σ/4)*(size z:ℝ)) := by
        apply Real.exp_monotone
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hk]
        change (separation i.1 (i.1+wrap c z):ℝ)≤(size z:ℝ)
        exact_mod_cast ConditionalAffineRouteJets.cover_distance i.1 z
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hDP,mul_assoc]
      exact mul_le_mul_of_nonneg_right he (mul_nonneg hP (norm_nonneg _))
    have ff : removed T s V R i j b z=0 := funext fun _ => if_neg (fun H => hk H.1)
    have H0 : J z=0 := by unfold J; rw [ff,FreeResolvent.Affine.zero_null]
    simp only [H0,smul_zero,norm_zero,mul_zero,le_refl]
  have hsum : Summable (fun z => ‖(D*P) • J z‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hz HH.2.1
  have hh := (norm_tsum_le_tsum_norm hsum).trans ((hsum.tsum_le_tsum hz HH.2.1).trans HH.2.2)
  have H' := differentiates T s V R i j b hσ h l
  rw [(H'.const_smul (D*P)).tsum_eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg hDP] at hh
  rw [genuine T s V R i j b hσ.le h]
  exact hh

end YM.Integration.ConditionalAffineNoiseWinding

namespace YM.Integration.ConditionalAffineNoiseCoordinates
open Function Set Lattice Wilson RG Precision Exterior Tree Pressure Pressure.Tube Next.SectorChange Next.SectorChange.Rows
open Next.SectorChange.Gaussian AnalyticBridge.SectorAffine FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open ProjectorNext.Equivariance Push.Uniform
open scoped BigOperators Classical Topology ContDiff
variable (G : Gauge) (c : Side)

def index : Coord G c ≃ raw G c where
  toFun j := (j.1.1,axisEquiv j.1.2,j.2)
  invFun i := ((i.1,axisEquiv.symm i.2.1),i.2.2)
  left_inv j := by
    rcases j with ⟨⟨x,d⟩,b⟩
    change ((x,axisEquiv.symm (axisEquiv d)),b)=((x,d),b)
    rw [axisEquiv.symm_apply_apply]
  right_inv i := by simp

def arrange : Vec G c 1 ≃L[ℝ] PriceCoords G c := LinearEquiv.toContinuousLinearEquiv
  ({ toFun := fun B j => B (index G c j)
     invFun := fun B i => B ((index G c).symm i)
     left_inv := fun B => funext fun i => by simp
     right_inv := fun B => funext fun i => by simp
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Vec G c 1 ≃ₗ[ℝ] PriceCoords G c)

theorem field (B : Vec G c 1) : AnalyticBridge.SectorAffine.field 1 (arrange G c B) = represent (decode B) := rfl

theorem arrange_apply (B : Vec G c 1) (j : Coord G c) : arrange G c B j=B (index G c j) := rfl

theorem direction (i : raw G c) : arrange G c (ray G c i) = bolt ((index G c).symm i) := by
  funext j
  rw [arrange_apply]
  by_cases h : index G c j=i
  · have he := (index G c).injective (h.trans ((index G c).apply_symm_apply i).symm)
    simp [ray,bolt,he]
  have he : j≠(index G c).symm i := fun e => h (e ▸ (index G c).apply_symm_apply i)
  simp [ray,bolt,h,he]

/-- A continuous linear equivalence transports each independently chosen
original ray. The identity holds without an extra smoothness premise. -/
theorem directions {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : PriceCoords G c → E)
    {n : ℕ} (a : Fin n → raw G c) :
    iteratedFDeriv ℝ n (F ∘ arrange G c) 0 (ray G c ∘ a) =
      iteratedFDeriv ℝ n F 0 (bolt ∘ (index G c).symm ∘ a) := by
  have h := (arrange G c).iteratedFDerivWithin_comp_right (s:=Set.univ) F uniqueDiffOn_univ
    (x:=0) (Set.mem_univ _) n
  simp only [Set.preimage_univ,iteratedFDerivWithin_univ,map_zero] at h
  rw [h,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congrArg
  funext j
  exact direction G c (a j)

/-- Original physical `mn` on exactly the raw resolvent coarse chart, with
independent rays, both rendered endpoints, and the physical cutoff length. -/
theorem physical (n : ℕ) (σ : ℝ) (hσ : 0<σ) : ∃ δ N : ℝ, 0<δ ∧ 0<N ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (C : ℝ), T.R.mn.strip σ C →
      ∀ (s : Signed) (R : ℕ) (i : Bond c) (j : Twin c) (b : G.Color) (_ : ‖b‖≤1)
        (k : ℕ) (_ : k≤n) (a : Fin k → raw G c),
      (native c).weight (σ/4) i.1 (mesh j).1 * Real.exp (δ*Stars.rays (native c) (s.act i.1) (hearth ∘ a)) *
        ‖iteratedFDeriv ℝ k (fun B => (PhysicalAffineScalarUncut.noiseStack T (pull s 0 (represent (decode B))) i j -
          T.Φ' R (pull s 0 (represent (decode B))) i j) b) 0 (ray G c ∘ a)‖ ≤
        N*Real.exp (-(σ/2)*((R:ℝ)/S.patch.L.val))*C := by
  obtain ⟨δ,N,hδ,hN,H⟩ := ConditionalAffineNoiseWinding.charged G n σ hσ
  refine ⟨δ,N,hδ,hN,?_⟩
  intro c f S T C h s R i j b hb k hk a
  let A := fun B : PriceCoords G c => (PhysicalAffineScalarUncut.noiseStack T (pull s 0 (AnalyticBridge.SectorAffine.field 1 B)) i j -
    T.Φ' R (pull s 0 (AnalyticBridge.SectorAffine.field 1 B)) i j) b
  have H' := H S T C h s (1:Config G c) R i j b hb (List.ofFn ((index G c).symm ∘ a)) (by simpa using hk)
  rw [Stars.list_result,Stars.pays] at H'
  change _ * _ * ‖iteratedFDeriv ℝ k (A ∘ arrange G c) 0 (ray G c ∘ a)‖ ≤ _
  rw [directions]
  exact H'

end YM.Integration.ConditionalAffineNoiseCoordinates
