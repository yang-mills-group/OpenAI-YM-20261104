import YM.WilsonCoeffUV.FieldRead.Projection
/-!
# Jet caliper. Preserves assessed color-signed law. No lower slot
producible. Diagonal uses `Place.sampled`, mixed uses transported nonlinear.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 45000
noncomputable section
namespace YM.WilsonCoeffUV.Fountain
open Filter Function Set Laurent Lattice RG Exterior Precision Next.Free Gauge Power Bloch Metric Matrix Work.F08
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l m p:ℕ}{A C s t :ℝ}

def latent (F:Glas G h l) : Fane G h l := F.compContinuousLinearMap (fun _=>(casing G h).toContinuousLinearMap)
lemma windface (u:Fin r→YForest G)(X:Fin l→Snap G h): latent (skyline h u l) X= Tensor.coeff (mite u) l 0 X:=by
   let M:= (casing G h).symm.toContinuousLinearMap
   let v:= fun i=>casing G h (X i)
   change ((l.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ l (mite u ∘ M) 0) v=_
   rw [Next.Foundations.jets_linear M ((mite_smooth u).of_le (show (l:WithTop ℕ∞)≤ω from le_top)),_root_.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply, show (fun i=>M (v i)) =X from funext fun i=>(casing G h).symm_apply_apply _]; rfl

def grain (X:Snap G h)(x:YForest G):ℝ:= sampled X (Place.seat x.1) (feather x).2 x.2.2
lemma grace (X:Snap G h)(i:YForest G): fderiv ℝ (flex i) 0 X=grain X i:=by
    let C:G.Color →L[ℝ] ℝ:= colorL i.2.2
    let L := Film.sampleIn (G:=G) (d:=h) (Place.seat i.1) (feather i).2
    have he : ContDiffAt ℝ ω logo (L 0):=by rw [map_zero]; exact logo_smooth ..
    change fderiv ℝ (C ∘ (logo ∘ L)) 0 X=_
    rw [fderiv_comp (𝕜:=ℝ) (x:=0) C.differentiableAt (he.differentiableAt (by simp)|>.comp _ L.differentiableAt),ContinuousLinearMap.fderiv,
        ContinuousLinearMap.comp_apply, fderiv_comp (𝕜:=ℝ) 0 (he.differentiableAt (by simp)) L.differentiableAt,ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,map_zero,echoing];
    change C (steady _+0)=_; rw [add_zero]; rfl

lemma inspect (u:Fin r→YForest G)(X:Snap G h): Tendsto (fun t:ℝ=> (t^r)⁻¹ • mite u (t • X)) (𝓝[>] (0:ℝ)) (𝓝 (∏ i, grain X (u i))):=by
   have he i: Tendsto (fun t:ℝ=> t⁻¹ • flex (u i) (t • X)) (𝓝[>] (0:ℝ)) (𝓝 (grain X (u i))):=by
      let f:=flex (h:=h) (u i)
      have ht:HasDerivAt (fun t:ℝ=> f (t • X)) (fderiv ℝ f 0 X) 0:= ((flex_smooth (h:=h) (u i)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0
          (show HasDerivAt (fun t:ℝ=> t•X) X 0 from by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const X) (by rw [zero_smul])
      have hv:=ht.tendsto_slope_zero_right
      rw [show fderiv ℝ f 0 X= _ from grace ..] at hv; simpa [f, flex_zero] using! hv
   refine (tendsto_finsetProd _ fun i _=>he i).congr fun x=>?_
   simp_rw [mite, smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin, inv_pow]
private lemma leading_here (u:Fin r→YForest G)(n)(X:Snap G h): ContDiffAt ℝ (↑n) (fun t:ℝ=> mite u (t • X)) 0:= by
    let L: ℝ→L[ℝ]Snap G h:=(ContinuousLinearMap.id ℝ ℝ).smulRight X
    exact (show ContDiffAt ℝ (↑n) (mite u) (L 0) from by rw [map_zero]; exact (mite_smooth _).of_le le_top).comp _ L.contDiff.contDiffAt
lemma under_k (x: Fin r→YForest G)(he:l < r): skyline h x l=0:=by
   refine Tensor.ext_diag _ _ (skyline_auth h x l) (fun _ _=>rfl) ?_; funext v
   obtain ⟨X,rfl⟩:= (casing G h).surjective v
   calc
       _= Tensor.diagonal (Tensor.coeff (mite x) l 0) X:= windface x (fun _:Fin l=>X)
       _= leading l (fun t:ℝ=>mite x (t • X)):= (leading_tensor X _ ((mite_smooth _).of_le le_top)).symm
       _=0:= leading_of_lim (leading_here x l X) 0 (falls he (inspect ..))
lemma on_k (x:Fin r→YForest G)(X:Snap G h): Tensor.diagonal (skyline h x r) (casing G h X)=∏ i, grain X (x i):= by
    calc
       _ = Tensor.diagonal (Tensor.coeff (mite x) r 0) X:= windface x (fun _:Fin r=>X)
       _ = _:= (leading_tensor X _ ((mite_smooth _).of_le le_top)).symm.trans (leading_of_lim (leading_here x r X) _ (inspect ..))
lemma arret_under (c:Volume D)(F:ChamberTen G (Vote D) r) (he:l<r): arret c F h l=0:=by simp [arret,under_k _ he]

/-! Constant colors. -/
lemma adj_pay (f:G.El)(u:G.ColorIndex)(x:G.Color): (G.adjoint f x) u=∑ j,gammaC f u j*x j:= (show _= (gammaC f *ᵥ ((coatC G).symm x)) u by rw [gammaC,LinearMap.toMatrix'_mulVec]; rfl)

lemma mural_dot (H:Hol G)(v:Fin r→ Edge Cover)(u:Fin r→G.ColorIndex)(g:G.El):
    let f (u:Fin r→G.ColorIndex):=mite (h:=h) fun i=>stone (v i) (u i)
    ((f u ∘ Film.colorIn G h g) =ᶠ[𝓝 0] fun X=> ∑ x,(∏ i,gammaC g (u i) (x i)) • f x X):=by
   intro f
   have he (i:Edge Cover)(u:G.ColorIndex): flex (stone i u) = fun X:Snap G h=> Film.lane (Place.seat i.1) i.2 X u:=by funext; unfold flex; rw [feather_at]; rfl
   filter_upwards [eventually_all.mpr fun i=>Film.light H (d:=h) g (v i)] with X hx
   change (∏ i:Fin r, flex (stone (v i) (u i)) (Film.colorIn G h g X)) =∑ x: Fin r→G.ColorIndex,(∏ i,gammaC g (u i) (x i)) • f x X
   have hu i: flex (stone (v i) (u i)) (Film.colorIn G h g X)=∑ j,gammaC g (u i) j * flex (stone (v i) j) X:= by rw [he]; dsimp only; simp_rw [he]; rw [hx i]; exact adj_pay ..
   simp_rw [hu,Fintype.prod_sum,Finset.prod_mul_distrib]; rfl
end YM.WilsonCoeffUV.Fountain
