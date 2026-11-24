import YM.Integration.PhysicalAffineScalarMetric
import YM.Integration.PhysicalAffineScalarTails
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Incident

/-! The genuine first coefficient of the complete affine residual on an original
no-hole active tree. Both its source and its response are calculated in the
original signed path and noise coordinates before projecting. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarStationary

open Function Filter Lattice Wilson RG RG.Patch Axial Bloch Laurent Precision Exterior Tree Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.SectorMeasure.Presented Next.Fluctuations Next.Fluctuations.Sector
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine
open AnalyticNext.ConnectedActivity.Aff Work.F03 PhysicalAffineScalarUncut
open PhysicalAffineScalarUncut.FirstOrder
open PhysicalAffineScalarProjection (apply_columns)
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
local notation "Coarse" => FreeResolvent.Vec G c 1
local notation "Fine" => FreeResolvent.Vec G f 1

/-- The uncut fine-only response when a genuine signed fine field varies at
fixed flat background and the original coarse field is held fixed. -/
def fineRow (T : Tube G S) (s : Signed) (a : LogField G f) (i : Twin f ⊕ Bond c) : G.Color :=
  i.elim (xLin T.high T.up (orient s a)) (zLin S (orient s a) 0)

theorem flat_slope (T : Tube G S) {P : Teller G} {A B : Bed} (hA : Alongside A B T)
    (hP : P.Funds S T) (k : S.Choices) (v : Fine) (i : Slots S) :
    PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all 0 v i = fineRow T i.1 (decode v) i.2 := by
  obtain ⟨_,_,hup,_⟩ := hP.feeds
  rw [← hP.high] at hup
  rcases i with ⟨s,p|b⟩
  · cases hp : p.2
    · simp only [PhysicalAffineScalarJets.slope,fineRow,Sum.elim_inl,xLin,hp,Bool.false_eq_true,
        if_false,response_zero,orient_pulls]
      rfl
    · have htrack : tracks S s T.up FreeResolvent.Affine.all (0:Coarse)=tensor G (A.roots.acts f) :=
        identity_track S s hup hA.inbound
      simp only [PhysicalAffineScalarJets.slope,fineRow,Sum.elim_inl,xLin,hp,if_true,
        ← Matrix.mulVec_mulVec,response_zero,orient_pulls]
      rw [htrack]
      ext j
      exact (congrFun (component_mul (A.roots.acts f) (flatten (dColor G f 1 (pulled (decode v) s))) j)
        (p.1.1,plaquette p.1.2)).trans (ellLine_mulVec A hup hA.inbound p.1 _ j).symm
  · have h := Push.SectorMeasure.funds_branch hP
    have hu := (near_whole k h).self_of_nhds
    have h0 : represent (decode (0:Coarse))=1 := by
      change represent ((plain G c 1) 0) = _
      rw [map_zero,link_one]
    have hb := block_columns k (0:Coarse) s b v h hu
    rw [h0,Flat.flat_probe s k b (launch v) h] at hb
    have hl : Flat.labels (launch v) = decode v := by
      change decode (launch.symm (launch v)) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
    rw [hl] at hb
    simp only [PhysicalAffineScalarJets.slope,fineRow,Sum.elim_inr,←hb,orient_pulls,zLin,Pi.zero_apply,zero_sub,smul_neg]
    rfl

variable (T : Tube G S) (x : ℝ) (k : S.Choices) (F : Forest S.ratio)
local notation "store" => noHole S
local notation "keys" => Active store x F × G.ColorIndex

def stationaryCoordinates (b : LogField G c) : Gaussian.Vec keys :=
  tape.symm fun j => attempt T F b j.1.1

theorem recovered (b : LogField G c) :
    fresh x (shots S x) store F (tape (stationaryCoordinates T x F b)) = attempt T F b := by
  funext e
  simp only [stationaryCoordinates,tape.apply_symm_apply,fresh]
  by_cases he : e ∈ F.trunks
  · rw [dif_neg (not_not.mpr he),attempt_root T F b e he]
  · have ha : ¬chill store x F ⟨e,he⟩ := by simp [chill,Stores.dome,Stores.place,halo_spec,noHole]
    rw [dif_pos he,dif_pos ha]

theorem linear_station (s : Signed) (b : LogField G c) :
    orient s (station T F b) = orient s (AnalyticNext.ConnectedActivity.Aff.form (attempt T F b)) + orient s (copyField S b) := by
  have hc (a : LogField G f) : AnalyticNext.ConnectedActivity.Aff.form (collect G a)=a := by
    funext i
    exact congrArg (fun j => a (i.1,j)) (axisEquiv.apply_symm_apply i.2)
  have hs : station T F b = AnalyticNext.ConnectedActivity.Aff.form (attempt T F b)+copyField S b := by
    rw [←hc (station T F b)]
    change AnalyticNext.ConnectedActivity.Aff.form (collect G (station T F b)) = AnalyticNext.ConnectedActivity.Aff.form (collect G (station T F b)-linearCopy S.ratio (collect G b)) + AnalyticNext.ConnectedActivity.Aff.form (linearCopy S.ratio (collect G b))
    funext i
    exact (sub_add_cancel _ _).symm
  rw [hs]
  unfold AnalyticNext.ConnectedActivity.Aff.orient
  rw [show collect G (AnalyticNext.ConnectedActivity.Aff.form (attempt T F b) + copyField S b) = collect G (AnalyticNext.ConnectedActivity.Aff.form (attempt T F b)) + collect G (copyField S b) from rfl,map_add]
  rfl

private lemma log_collect {n : Side} (a : LogField G n) : ConnectedActivityE6.SliceRows.toLog (collect G a)=a := by
  funext i
  obtain ⟨b,rfl⟩ := (Work.E03.poleEquiv n).surjective i
  exact ConnectedActivityE6.SliceRows.at_pole (collect G a) b

theorem row_balance {P : Teller G} {A B : Bed} (hA : Alongside A B T) (hP : P.Funds S T)
    (b : LogField G c) (s : Signed) (i : Twin f ⊕ Bond c) :
    fineRow T s (AnalyticNext.ConnectedActivity.Aff.form (attempt T F b)) i + variation T s (copyField S b) b i=0 := by
  let u := orient s (AnalyticNext.ConnectedActivity.Aff.form (attempt T F b))
  let v := orient s (copyField S b)
  have hlog : ConnectedActivityE6.SliceRows.toLog (collect G u+collect G v)=u+v := by
    change ConnectedActivityE6.SliceRows.toLog (collect G (u+v)) = _
    exact log_collect _
  have he := ConnectedActivityE6.SliceRows.linear_add T hP (collect G u) (collect G v) (orient s b) i
  simp only [ConnectedActivityE6.SliceRows.uncutField,hlog,log_collect] at he
  have hfit := escape T hA hP s F b
  rw [linear_station T F s b] at hfit
  rcases i with j|j
  · have h := congrFun hfit.1 j
    change xLin T.high T.up (u+v) j = xLin T.high T.up u j+xLin T.high T.up v j at he
    change xLin T.high T.up u j+(xLin T.high T.up v j-Fout T (orient s b) j)=0
    rw [← add_sub_assoc,← he,h,sub_self]
  · have h := congrFun hfit.2 j
    change zLin S (u+v) (orient s b) j = zLin S u 0 j+zLin S v (orient s b) j at he
    change zLin S u 0 j+(zLin S v (orient s b) j-Qout T (orient s b) j)=0
    rw [← add_sub_assoc,← he,h,sub_self]

/-- The original nonlinear full-stack source is cancelled at first order by
the actual no-hole active relative stationary tangent, entry by entry. -/
theorem corrected_rate {P : Teller G} {A B : Bed} (hA : Alongside A B T) (hP : P.Funds S T)
    (b : Coarse) :
    Tendsto (fun t : ℝ => t⁻¹ • PhysicalAffineScalarUncut.offset T k (t • b)) (𝓝[≠] 0)
      (𝓝 (-(PhysicalAffineScalarUncut.columns T x k F 0 *ᵥ stationaryCoordinates T x F (decode b)))) := by
  rw [apply_columns,recovered]
  have hcoord : decode (launch.symm (attempt T F (decode b))) = AnalyticNext.ConnectedActivity.Aff.form (attempt T F (decode b)) := rfl
  have ht : Tendsto (fun t : ℝ => t⁻¹ • tape (PhysicalAffineScalarUncut.offset T k (t • b))) (𝓝[≠] 0)
      (𝓝 (-(slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all 0 (launch.symm (attempt T F (decode b)))))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hbal := row_balance T F hA hP (decode b) i.1 i.2
    let w := fineRow T i.1 (AnalyticNext.ConnectedActivity.Aff.form (attempt T F (decode b))) i.2
    let v := variation T i.1 (copyField S (decode b)) (decode b) i.2
    have hneg : v = -w := by
      calc v = (w + v) - w := by abel
           _ = -w := by rw [show w+v=0 from hbal,zero_sub]
    have he : variation T i.1 (copyField S (decode b)) (decode b) i.2 =
        -fineRow T i.1 (AnalyticNext.ConnectedActivity.Aff.form (attempt T F (decode b))) i.2 := hneg
    have H := offset_rate T hP k b i
    rw [he,smul_neg] at H
    simpa only [Pi.smul_apply,Pi.neg_apply,flat_slope T hA hP,hcoord] using H
  let e : Prices G (Slots S) ≃L[ℝ] LogArray G (Slots S) := gaugeCount
  let a := PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all 0 (launch.symm (attempt T F (decode b)))
  have hr : Tendsto (fun t : ℝ => e.symm (t⁻¹ • e (PhysicalAffineScalarUncut.offset T k (t • b))))
      (𝓝[≠] 0) (𝓝 (e.symm (-(slip • a)))) := e.symm.continuous.continuousAt.tendsto.comp ht
  change Tendsto _ _ (𝓝 (-(e.symm (slip • a))))
  simpa only [map_smul,map_neg,ContinuousLinearEquiv.symm_apply_apply] using hr

private theorem product_continuous {X ι κ τ : Type*} [TopologicalSpace X] [Fintype κ]
    {A : X → Matrix ι κ ℝ} {B : X → Matrix κ τ ℝ} {x₀ : X}
    (hA : ContinuousAt A x₀) (hB : ContinuousAt B x₀) :
    ContinuousAt (fun x => A x*B x) x₀ := by
  change Tendsto (fun x => A x*B x) (𝓝 x₀) (𝓝 (A x₀*B x₀))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply tendsto_finsetSum
  intro k _
  exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hA) i)) k).mul
    ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hB) k)) j)

section projection
variable {σ M : ℝ} (hc : 1<c.val) (hσ : 0<σ) (hW : FreeResolvent.Affine.Sheet T.up σ M)
  (h : S.patch.Branches S.kernel G)
include hc hσ hW h

theorem continuous_columns : ContinuousAt (PhysicalAffineScalarUncut.columns T x k F) 0 := by
  apply continuousAt_pi.mpr
  rintro ⟨⟨s,i⟩,p⟩
  apply continuousAt_pi.mpr
  intro j
  let v : Fine := launch.symm (fresh x (shots S x) store F (axisPrice j))
  have hr : ContinuousAt (response S s (G:=G)) 0 :=
    (FreeResolvent.Affine.price_D S s hc 0 (γ:=1) (d:=0) zero_lt_one le_rfl zero_le_one).smooth.continuousAt
  have hq : ContinuousAt (duct S s k (G:=G)) 0 :=
    (FreeResolvent.Affine.price_Q S s k hc 0 (γ:=1) (d:=0) h zero_lt_one le_rfl zero_le_one).smooth.continuousAt
  have ht : ContinuousAt (tracks S s T.up FreeResolvent.Affine.all) 0 :=
    (tracks_smooth hσ hW S s FreeResolvent.Affine.all 0).continuousAt
  rcases i with u|b
  · cases hu : u.2
    · change ContinuousAt (fun B : Coarse => (slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B v (s,Sum.inl u)) p) 0
      simp only [PhysicalAffineScalarJets.slope,Sum.elim_inl,hu,Bool.false_eq_true,if_false,PiLp.smul_apply,smul_eq_mul]
      change ContinuousAt (fun B : Coarse => slip*(Real.sqrt T.high.direct*((response S s B *ᵥ v) (u.1.1,plaquette u.1.2,p)))) 0
      fun_prop
    · change ContinuousAt (fun B : Coarse => (slip • PhysicalAffineScalarJets.slope T k FreeResolvent.Affine.all B v (s,Sum.inl u)) p) 0
      simp only [PhysicalAffineScalarJets.slope,Sum.elim_inl,hu,if_true,PiLp.smul_apply,smul_eq_mul]
      change ContinuousAt (fun B : Coarse => slip * (((tracks S s T.up FreeResolvent.Affine.all B * response S s B) *ᵥ v) (u.1.1,plaquette u.1.2,p))) 0
      fun_prop
  · change ContinuousAt (fun B : Coarse => slip * (-(Real.sqrt S.kernel.penalty * ((duct S s k B *ᵥ v) (b.1,coord b.2,p))))) 0
    fun_prop

theorem continuous_projection (hp : (PhysicalAffineScalarUncut.gram T x k F 0).PosDef) :
    ContinuousAt (projected T x k F) 0 := by
  let D := PhysicalAffineScalarUncut.columns T x k F
  have hd : ContinuousAt D 0 := continuous_columns T x k F hc hσ hW h
  have ht : ContinuousAt (fun B => (D B).transpose) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (continuousAt_pi.mp ((continuousAt_pi.mp hd) j)) i
  have hh : ContinuousAt (fun B => (D B).transpose * D B) 0 := product_continuous ht hd
  have hi : ContinuousAt (fun B => ((D B).transpose * D B)⁻¹) 0 := by
    apply (continuousAt_matrix_inv _ ?_).comp hh
    rw [show Ring.inverse = (Inv.inv : ℝ → ℝ) from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hp.det_pos.ne'
  unfold projected PhysicalAffineScalarUncut.remaining
  exact continuousAt_const.sub (product_continuous (product_continuous hd hi) ht)
end projection

private lemma kills {α ι : Type} [Fintype α] [Fintype ι] [DecidableEq ι] (D : Matrix α ι ℝ)
    (h : (D.transpose*D).PosDef) (a : Gaussian.Vec ι) : remaining D *ᵥ (D *ᵥ a)=0 := by
  rw [Matrix.mulVec_mulVec]
  have hh : remaining D*D=0 := by
    rw [remaining,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ h.det_pos.ne'),Matrix.mul_one,sub_self]
  rw [hh,Matrix.zero_mulVec]

private lemma multiply_limit {α ι κ : Type} [Fintype ι] {l : Filter κ}
    {D : κ → Matrix α ι ℝ} {M : Matrix α ι ℝ} {v : κ → Gaussian.Vec ι} {a : Gaussian.Vec ι}
    (hM : Tendsto D l (𝓝 M)) (hv : Tendsto v l (𝓝 a)) :
    Tendsto (fun p => D p *ᵥ v p) l (𝓝 (M *ᵥ a)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_finsetSum
  intro j _
  exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp hM) i)) j).mul ((tendsto_pi_nhds.mp hv) j)

section rate
variable {P : Teller G} {A B : Bed} (hA : Alongside A B T) (hP : P.Funds S T)
  {σ M : ℝ} (hgeo : Bid.Larger (G:=G) S) (hσ : 0<σ) (hW : FreeResolvent.Affine.Sheet T.up σ M)
  (h0 : (PhysicalAffineScalarUncut.gram T x k F 0).PosDef)
include hA hP hgeo hσ hW h0

/-- The actual full affine residual at its minimizer is o(t) in any independent
coarse field direction b, on the actual signed output rows. -/
theorem residual_rate (b : Coarse) :
    Tendsto (fun t : ℝ => t⁻¹ • sourceResidual T x k F (t • b)) (𝓝[≠] 0) (𝓝 0) := by
  let D := PhysicalAffineScalarUncut.columns T x k F 0
  let v := -(D *ᵥ stationaryCoordinates T x F (decode b))
  have hy : projected T x k F 0 *ᵥ v=0 := by
    change remaining D *ᵥ (-(D *ᵥ stationaryCoordinates T x F (decode b))) = 0
    rw [Matrix.mulVec_neg,kills D h0,neg_zero]
  have ht : Tendsto (fun t : ℝ => t • b) (𝓝[≠] 0) (𝓝 0) := by
    have hline : Continuous (fun t : ℝ => t • b) := continuous_id.smul continuous_const
    simpa only [zero_smul] using (hline.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have hu := (continuous_projection T x k F hgeo.2.2 hσ hW hgeo.1 h0).tendsto.comp ht
  have hv : Tendsto (fun t : ℝ => t⁻¹ • PhysicalAffineScalarUncut.offset T k (t • b)) (𝓝[≠] 0) (𝓝 v) := by
    dsimp only [v,D]
    exact corrected_rate T x k F hA hP b
  have hprod : Tendsto (fun t : ℝ => projected T x k F (t • b) *ᵥ
      (t⁻¹ • PhysicalAffineScalarUncut.offset T k (t • b))) (𝓝[≠] 0) (𝓝 (projected T x k F 0 *ᵥ v)) :=
    multiply_limit (D:=fun t : ℝ => projected T x k F (t • b))
      (v:=fun t : ℝ => t⁻¹ • PhysicalAffineScalarUncut.offset T k (t • b)) hu hv
  have he : (fun t : ℝ => t⁻¹ • sourceResidual T x k F (t • b)) =
      fun t => projected T x k F (t • b) *ᵥ (t⁻¹ • PhysicalAffineScalarUncut.offset T k (t • b)) := by
    funext t
    rw [projected_residual,Matrix.mulVec_smul]
  rw [he]
  rw [hy] at hprod
  exact hprod

/-- Root-local quadratic order of each prescribed residual square, before
any cancellation between distinct translation roots or forests. -/
theorem rooted_square_rate (g : ℝ) (o : Site c) (b : Coarse) :
    Tendsto (fun t : ℝ => (t^2)⁻¹ * rootSquare T x k F g o (t • b)) (𝓝[≠] 0) (𝓝 0) := by
  let α := Rows.Receipt G S
  have hv := residual_rate T x k F hA hP hgeo hσ hW h0 b
  have hr (i : α) := tendsto_pi_nhds.mp hv i
  have H (i : α) : Tendsto (fun t : ℝ => (t^2)⁻¹ * (if PhysicalAffineScalarComparison.rowRoot S i=o
      then -(sourceResidual T x k F (t • b) i)^2/(2*g^2) else 0)) (𝓝[≠] 0) (𝓝 0) := by
    by_cases hroot : PhysicalAffineScalarComparison.rowRoot S i=o
    · simp only [hroot,if_true]
      have he := (((hr i).pow 2).neg.div_const (2*g^2))
      convert he using 1
      · funext t; simp only [Pi.smul_apply,smul_eq_mul,mul_pow,inv_pow]; ring
      · simp
    · simp only [hroot,if_false,mul_zero]; exact tendsto_const_nhds
  simpa only [rootSquare,Finset.mul_sum,Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun i _ => H i))

/-- The full scalar residual's mixed two-direction second difference vanishes
at each original translation root. -/
theorem mixed_rooted_square (g : ℝ) (o : Site c) (b d : Coarse) :
    Tendsto (fun t : ℝ => (t^2)⁻¹ * (rootSquare T x k F g o (t • (b+d))
      - rootSquare T x k F g o (t • b) - rootSquare T x k F g o (t • d))) (𝓝[≠] 0) (𝓝 0) := by
  have h := rooted_square_rate T x k F hA hP hgeo hσ hW h0 g o
  simpa only [mul_sub,sub_zero] using ((h (b+d)).sub (h b)).sub (h d)

/-- One genuine block change, still with both independent coarse field legs,
separate active coordinate spaces, and fixed original translation root. -/
theorem one_tree_mixed_square (q : Site c)
    (F' : {t : Forest S.ratio // FreeResolvent.Affine.changed S F t q})
    (hp : (PhysicalAffineScalarUncut.gram T x k F'.val 0).PosDef) (g : ℝ) (o : Site c) (b d : Coarse) :
    let diff := fun y => rootSquare T x k F'.val g o y - rootSquare T x k F g o y
    Tendsto (fun t : ℝ => (t^2)⁻¹ * (diff (t • (b+d)) - diff (t • b) - diff (t • d))) (𝓝[≠] 0) (𝓝 0) := by
  let h := mixed_rooted_square T x k F hA hP hgeo hσ hW h0 g o b d
  let h' := mixed_rooted_square T x k F'.val hA hP hgeo hσ hW hp g o b d
  convert h'.sub h using 1
  · ext t; dsimp only; ring
  · simp
end rate

end YM.Integration.PhysicalAffineScalarStationary
end

