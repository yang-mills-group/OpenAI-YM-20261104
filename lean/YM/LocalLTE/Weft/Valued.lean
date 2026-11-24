import YM.LocalLTE.Weft.Plate
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Jets
/-! Triangle valuation at finite-knob charts. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Pastel
variable {v z r W w s t y η γ B a μ: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
variable (X:Coat T F)
open Weft AnalyticBridge.VerifiedReset
-- single-array version adapted from `flat_critical`, including two distinct site systems.
private lemma invariantB (q:Directions G c→ₗ[ℝ]ℝ) (h:G.Simple)(hp:∀ t:G.El,∀ v,q (colorMove t v)=q v)(v: Directions G c): q v=0:=by
    let a i : G.Color→ₗ[ℝ] Directions G c := LinearMap.single ℝ (fun _:Edge (Site c) => G.Color) i
    have hq i x : q (a i x)=0:= LinearMap.congr_fun (StressFlux.linear_invariant h (q.comp (a i)) (by
      intro u w; apply Eq.trans _ (hp u (a i w)); refine congr_arg q ?_; funext j; change Pi.single (M:=fun _:Edge (Site c) => G.Color) i (G.adjoint u w) j=G.adjoint u (Pi.single (M:=fun _:Edge (Site c) => G.Color) i w j); by_cases he:j=i <;> simp [he,Pi.single_eq_of_ne])) x
    have he: v=∑ i,a i (v i):= by funext j; simp [a,Finset.sum_apply,Pi.single_apply];
    rw [he,map_sum]; exact sum_eq_zero fun i _=> hq i _
lemma doubleB (v:G.El) (x:ZipP G c f): let f:=(colorMove v).prodMap (colorMove v); let u:= (fun _ : Site c=>v)
    Frond.shaft S (f x)=gauge (constantGauge u S.ratio) (Frond.shaft S x):=by
    intro f u; change increment (replica _ (increment (1:Config G c) (colorMove v x.1))) (colorMove v x.2)= _; rw [exp_move, ← copied S.ratio S.patch.odd_side]
    funext i; unfold Frond.shaft increment Lattice.gauge; change G.lieExp (G.adjoint v _)*_= v*(G.lieExp (x.2 i) * _) *v⁻¹; rw [Channel.exp_adjoint]; unfold constantGauge; dsimp; group
lemma ivy_rot (h : P.Funds S T)(i: S.Choices)(p: Spot c f)(s:ℝ)(u:G.El)(x:ZipP G c f): ivy T s i p ((colorMove u).prodMap (colorMove u) x) = ivy T s i p x:=by
   obtain ⟨b,c₀,v,-⟩:= h.feeds; unfold ivy squarepot; have hp:= doubleB (S:=S) u x
   let Z:=fun _ : Site c=> u; let x':= (colorMove u|>.prodMap (colorMove u)) x; have hh: increment 1 x'.1=gauge Z (increment (1:Config G c) x.1):= exp_move ..; have hW: x'.2 = spinRow S Z x.2:= by rfl
   change loft T s (shaft S x') i (increment 1 x'.1) true p - _ = _
   apply congr_arg₂ (· - ·) ((congr_arg₂ (fun V X=> loft T s V i X true p) (show shaft S x' = gauge (constantGauge Z S.ratio) (Frond.shaft S x) from hp) hh).trans (winds Z _ _ h s p i _))
   apply sum_congr rfl fun j hj=>?_ ; change ‖freely T s (increment 1 x'.1) i j+straightened T (till s) (increment 1 x'.1) x'.2 j‖^2/2=_; rw [hh,hW,Frond.peony Z h, SliceRows.under T v,← map_add,G.norm_adjoint]
lemma criticalV (H:G.Simple) (i:S.Choices)(p:Spot c f)(s:ℝ)(h:P.Funds S T)(hp:DifferentiableAt ℝ (ivy T s i p) 0) : fderiv ℝ (ivy T s i p) 0=0:=by
   let M:=ivy T s i p; let L:=fderiv ℝ M 0; let A u : Directions G _→L[ℝ] Directions G _:=colorMove (n:=c) u
   have hu v x: L ((A v).prodMap (colorMove v) x)=L x:=by
      let a:= (A v).prodMap (colorMove (n:=f) v)
      have h: M ∘ a=M:=funext fun _=> ivy_rot h i p s v _; have hf:= fderiv_comp (f:=a) (g:=M) 0 (by simp [hp,M]) a.differentiableAt
      rw [h,a.fderiv,map_zero] at hf; exact congrFun (congr_arg DFunLike.coe hf.symm) x
   refine ContinuousLinearMap.ext fun x=>?_
   let I:=ContinuousLinearMap.inl ℝ (Directions G c) (Directions G f); let J:=ContinuousLinearMap.inr ℝ (Directions G c) (Directions G f)
   have hh:= invariantB (L ∘L I|>.toLinearMap) H (fun u x=>by have hz:= hu u (I x); simpa [I,A] using hz) x.1
   have hy:= invariantB (L ∘L J|>.toLinearMap) H (fun u x=>by have hz:= hu u (J x); simpa [J,A] using hz) x.2
   change L x=0; nth_rw 1 [show x=I x.1+J x.2 from ?_]; rw [map_add,show L (I x.1)=0 from hh, show L (J x.2)=0 from hy,add_zero] -- edit
   ext <;> simp [I,J]
private lemma all_whiteF (S : PathData G) (p : Clip) (R M) (a : Twin c) : plotted S p R M (1: Config G c) a=0 := by
  have he (n : ℕ) : shortenTerm S R M (1:Config G c) a.1 n=0 := by
    unfold shortenTerm; split
    next hv => simp [PathData.ellTerms, Work.F03.atSite_path,faceValue, SliceRows.trivial]
    exact rfl
  unfold plotted; split
  next => simp only [shorten,he,tsum_zero]
  simp [shoot,faceValue, SliceRows.trivial]
private lemma no_claim (h : P.Funds S T) (k : S.Choices) (i : Rod c f) (s : ℝ) : Scroll.freely T s 1 k i=0 := by
  unfold Scroll.freely baseStroke entryCost visual; rw [replica_one]
  have he (u : Twin c) : T.Xn (till s) (1 : Config G c) u=0 := all_whiteF ..
  rw [show S.prediction 1 k=(1:Config G c) from funext fun i=> Push.settled S (funds_branch h) i k]
  rcases i with i|i
  · simp only [Sum.elim,Tube.Xf,all_whiteF,canopyF,zip,he,map_zero,sum_const_zero,sub_zero]
  simp only [Sum.elim,canopyI,zip,Tube.Z,he,Pi.one_apply,inv_one,mul_one,G.curvature_unit,smul_zero,map_zero,sum_const_zero,sub_zero]

-- zero
lemma strain0 (h:P.Funds S T) (X:Coat T F)(v:Signed)(p:Rod c f): strain X.blank v p 0=0:=by
    have hk:dry X (0:ZipP G c f)=X.blank:=by unfold dry; simp only [Prod.fst_zero,Work.G07.at_zero_increment]; rfl
    rw [← hk, sprig X 0 (v,p) h,map_zero]; exact (congr_arg (fun V=> freely T X.x V _ p) (Work.G07.at_zero_increment _)).trans (no_claim h ..)
lemma volt0 (h : P.Funds S T): voltage (timeΛ X 0)=0:=by
    let Y:=timeΛ X (0:Disk G c); have he:Y=X.blank:=by unfold Y timeΛ Vine.pass dry; simp only [Prod.snd_zero,Work.G07.at_zero_increment]; rfl
    have hv0:bar X.blank 0=0:=by
       funext p; unfold bar; rw [if_pos (X.blank_all p.1 (spot S p.2)),strain0 h,smul_zero]; rfl
    change voltage Y=0; rw [he]; unfold voltage well leanB; rw [hv0]; simp only [show stand (0:Mention c f→ G.Color)=0 from rfl, Matrix.mulVec_zero,neg_zero]; rfl -- edit
lemma twig0 (h : P.Funds S T) (z:Air f G) : twig X z 0=0:=by
    let Y:=timeΛ X (0:Disk G c)
    have hv:voltage Y=0:=volt0 X h
    refine Prod.ext rfl ?_; change X.blank.lens (voltage Y+0 • X.atmos z)=_; rw [hv,zero_smul,add_zero,Coat.lens_zero]; rfl
-- expose voltage0 independently later
lemma shaft0 : shaft (G:=G) S 0=1:=by unfold shaft; simp [replica_one]
lemma valence₀ (h : P.Funds S T) (p : Spot c f)(s:ℝ) (i:S.Choices): ivy T s i p 0=0:=by
   unfold ivy squarepot; rw [shaft0,show (0:ZipP G c f).fst=0 from rfl,Work.G07.at_zero_increment]
   obtain ⟨b,d,he,-⟩:= h.feeds
   have hf (v : Rod c f):straightened T (till s) 1 0 v=0:=by
       rw [← turns_here]; obtain ⟨p',hv⟩:=SliceRows.linear T (till s) he 1 v 1; rw [← hv,map_zero]
   rw [show (0:ZipP G c f).snd=0 from rfl]; simp_rw [no_claim h,hf,zero_add,norm_zero]; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,sum_const_zero,sub_zero];
   let V:=(1:Config G c); let u:=(1:Config G f)
   -- evaluate
   have hs:S.prediction u i=V:=funext fun j=> Push.settled S (funds_branch h) j i
   have hX i: T.Xn (till s) V i=0:= all_whiteF ..; have hz i: T.Xf (till s) u i=0 :=all_whiteF ..;
   have he' (i:Rod c f): Scroll.effective T (till s) u V V i=0:=by
       rcases i with i|i
       · change T.Xf (till s) u i-canopyF T (till s) V i=0; unfold canopyF zip; simp_rw [hz,hX,map_zero]; simp
       change Tube.Z S V V i-canopyI T (till s) V i=0; unfold canopyI zip; simp_rw [hX,map_zero]; simp [V,Tube.Z]
   dsimp only [u,V] at hz hs he' hX
   rcases p with p|p|p|p
   · change flora T (till s) u (S.prediction u i) V p =0; simp [u,V,hs,flora,he',flaw,faceValue,SliceRows.trivial]
   · change nora T (till s) u (S.prediction u i) V p=0; simp [u,V,hs,nora,he',flaw]
   · change stormC T V p + (stormL T (till s) u (S.prediction u i) V p+stormD T (till s) V p)=0; simp [V,stormC,stormD,stormL,hX,flaw,faceValue,SliceRows.trivial]
   change stormN T (till s) V p=0; simp [V,stormN,canopyN,zip,hX]
end YM.LocalLTE.Fan
