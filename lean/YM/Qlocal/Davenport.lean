import YM.Qlocal.Committed
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Binding
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Work.F03 Work.F05
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped BigOperators Topology ENNReal Classical InnerProductSpace MatrixOrder ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side} {S:StepData c f} {k t j:ℕ}
    {V:Type} [DecidableEq V] {B:Census V}
variable (F:Forest S.ratio) (T:S.Choices) {b:Clip} {R:PathData G} {O:ChartRatio G} (W : Layout G)(U:Finset Age)
local notation "E"=> Apex c G
local notation "Z"=> Precision.Key F G
local notation "Y"=> Poll.Body Z
local notation "X"=> E × Y
local notation "I"=> ℝ × X
local notation "D"=> fieldDir G c 1
variable (K : Kernel S b R O)(w:Colors B G f) (h : Legal U W) (hv: w.vac=drawn W U f)
  {a L Λ:ℝ} (A:Before G a L S.patch.J S.kernel (j+3))(σ : fieldDir G c 1→AxisChart G F)
   (hR:R.Bounds b a L Λ) (hp:Bid.Larger (G:=G) S) (he:A.Service F b R σ)
local notation "τ"=> Uniform.tint G _
local notation "Γ'"=> weld Z
set_option quotPrecheck false
local notation "Γ"=> (Γ').trans (Uniform.tint G F.Free)
def gaugeL : I≃L[ℝ]Comparison.RG02.Bulk.Joint S (G:=G) F:= (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (slidL (G:=G) F)
local notation "Γ★"=> gaugeL (G:=G) F
lemma tinted (x:E) (y:Y): slidL (G:=G) F (x,y)= (tint G _ x,(Γ) y):= rfl
lemma pulls (z:I): (Γ★) z= (z.1,(τ) z.2.1,(Γ) z.2.2):=rfl
set_option quotPrecheck false
local notation "B₀"=> Laplace.startup F O T R b A hp hR he K.ratio
local notation "Bℓ"=> augment F W U B₀ h
local notation "θ"=> fderiv ℝ (orbit (G:=G) F σ) 0
include he
lemma same_path : σ =ᶠ[𝓝 0] K.b F := (he.is_extension (K.critical F)).symm
lemma awake (x:E) : (Γ) (θ x)= fderiv ℝ (K.b F) 0 ((τ) x):= by
 have hg:= same_path F K A σ he; let a:=tint G (Body 1 c); let T:=K.b F; let w:= Γ
 have hδ: DifferentiableAt ℝ σ (a 0):= by rw [a.map_zero]; exact ((K.critical F).2.1.differentiableAt (by simp)).congr_of_eventuallyEq hg
 rw [show orbit F σ= w.symm ∘ (σ ∘ a) from rfl, fderiv_comp _ w.symm.differentiableAt (hδ.comp _ a.differentiableAt), fderiv_comp _ hδ a.differentiableAt, a.fderiv,w.symm.fderiv, a.map_zero, hg.fderiv_eq]; exact w.apply_symm_apply _
lemma unity (x:E) (y:Y): Comparison.RG02.Bulk.translated K F ((τ) x) ((Γ') y)=(Γ★) (colorful (θ) (x,y)):= by
 rw [Comparison.RG02.Bulk.footing,pulls]; change _= ((1:ℝ),(τ) x,(Γ) (θ x+y)); rw [_root_.map_add,awake F K A σ he]; rfl
lemma accounting (x:E): liftQ (table F T R b) (θ) x = Comparison.RG02.Bulk.infrared S b R F T (K.b F) ((τ) x):= by
 let L:= slidL (G:=G) F; let g:= Comparison.RG02.Bulk.Surface S b R F T; let M:=x; change Radial.jet (g ∘ L.toContinuousLinearMap) 2 _=_; rw [← Comparison.RG02.Assembly.jet_eq]; rw [jet_continuous_right _ (((K.critical F).2.2 T).1.of_le le_top)]; exact congr_arg (fun v=>Comparison.RG02.Assembly.jet g 2 v) (Prod.ext rfl (awake F K A σ he x))
include he hv h
omit A he in
lemma geometric_known : ContDiffAt ℝ ω (Comparison.RG02.Bulk.geometric K F T w) 0:= by
 let h' := fun z:(Comparison.RG02.Bulk.Joint S (G:=G) F)=> z.1
 apply (stone_smooth K F T).add (((contDiffAt_fst.pow 2).mul (officer_known K F).smooth).add (f:=fun z => pillar (F:=F) z * officer F K z) ?_)
 unfold supplement; rw [hv]; exact (joint_receipt S F (planted W U h)).smooth
omit A he h in
lemma rough (x:I): venue F W U x= supplement S F w ((Γ★) x):= by rw [venue,supplement, hv]; unfold posed drawn; rw [Finset.sum_apply, Finset.sum_apply]; exact rfl
omit A he h hv in
lemma luminosity : ((fun z:I=>officer F K ((Γ★) z))) =ᶠ[𝓝 0] fun z=> Lapis.mist F O R z.2:= by
 have he : ∀ i:F.Free, ∀ᶠ z : I in 𝓝 0,0<O.J ((Γ) z.2.2 i):= fun i=> by
      let g (x:I):= O.J ((Γ) x.2.2 i); let p (x:I):=(Γ) x.2.2 i; let P':=Γ
      have hp:Continuous p:= by unfold p; fun_prop
      apply ((show Tendsto g (𝓝 0) (𝓝 1) from ?_).eventually (lt_mem_nhds zero_lt_one)); rw [← K.ratio.anchored]; have hi: ContinuousAt O.J 0:= (K.ratio.germ _ (Metric.mem_ball_self K.ratio.patch)).continuousAt; have ht : p 0=0:= by simp only [p,Prod.snd_zero,P'.map_zero]; rfl
      exact hi.tendsto.comp (ht ▸ (hp.tendsto 0))
 filter_upwards [Filter.eventually_all.mpr he] with x hx; rw [officer,pulls]; rw [show Real.log (∏ i, O.J (((Γ) x.2.2) i))=Lapis.sumAt F O x.2.2 from ?_]; · rfl
 exact Real.log_prod fun i (_:i∈Finset.univ)=> (hx i).ne'
include A he h hv hp hR
lemma geometric_code : (Comparison.RG02.Bulk.geometric K F T w ∘ (Γ★)) =ᶠ[𝓝 0] fun z:I=> (Bℓ).high z+ z.1^2* Lapis.mist F O R z.2:= by
 filter_upwards [luminosity F K] with z hz; change Lapis.table F T R b z.2 + (z.1^2*officer F K ((Γ★) z)+ supplement S F w ((Γ★) z))= (Lapis.table F T R b z.2+ venue F W U z) + _; rw [rough F W U w hv, ← hz]; abel
omit hv in
lemma illumination : Real.log ∘ ((Bℓ).paid)=(fun _=> Real.log (O.scale^Fintype.card F.Free))-(fun z:I=> Lapis.mist F O R z.2):= by
 funext x; change Real.log (O.scale^Fintype.card F.Free * Real.exp _) = _-_; rw [Real.log_mul (pow_ne_zero _ K.ratio.scale.ne') (Real.exp_pos _).ne', Real.log_exp]; rfl
set_option maxHeartbeats 680000 in
lemma pulse (x:E)(y:Y)(k:ℕ) : let s:= Comparison.RG02.Bulk.translated K F ((τ) x) ((Γ') y); vacuumLetter (Comparison.RG02.Bulk.geometric K F T w) s k=Floe.books F W U B₀ k (x,y):= by
 intro s; let R' : ℝ×X →ℝ:=Comparison.RG02.Bulk.geometric K F T w ∘ (Γ★); let v:=colorful (θ) (x,y); let b':=(Bℓ).high; let M (x:X):= Lapis.mist F O R x; let m:= M ∘ Prod.snd (α:=ℝ); let j : ℝ×X →ℝ:=fun x=>x.1^2*m x
 let c':= fun _:I=>Real.log (O.scale^Fintype.card F.Free); have hg:= mist_nice F O R b A hR K.ratio; have hm: ContDiffAt ℝ ω m 0:= hg.comp (f:=Prod.snd) (0:I) contDiffAt_snd
 unfold vacuumLetter; split
 next hk=> subst k; rw [Floe.books,Impulse,win0]; rfl
 next hk=>
    change _=Impulse (θ) b' ((Bℓ).paid) k (x,y); rw [Impulse,win_atn _ hk, token]; change -Comparison.RG02.Assembly.jet (Comparison.RG02.Bulk.geometric K F T w) (k+2) s=(Radial.jet (Real.log ∘ (Bℓ).paid) (k+0) v)-Radial.jet b' (k+2) v; rw [illumination F T W U K h A σ hR hp he]
    have hy : Radial.jet R' (k+2) v=Comparison.RG02.Assembly.jet (Comparison.RG02.Bulk.geometric K F T w) (k+2) s := (jet_continuous_right (Γ★).toContinuousLinearMap (i:=k+2) ((geometric_known F T W U K w h hv).of_le le_top) v).trans (congr_arg _ (unity F K A σ he x y).symm) -- σ hz shadowing.
    rw [← hy];
    have hξ:Radial.jet R' (k+2) v=Radial.jet b' (k+2) v+Radial.jet j (k+2) v:= by
        rw [← Laplace.jet_add (show ContDiffAt ℝ ω b' 0 from (Bℓ).pay.activity) (show ContDiffAt ℝ ω j 0 from ((contDiffAt_fst.pow 2).mul hm)) v]; unfold Radial.jet; rw [show iteratedFDeriv ℝ (k+2) R' 0= iteratedFDeriv ℝ (k+2) (b'+j) 0 from ((geometric_code F T W U K w h hv A σ hR hp he).iteratedFDeriv ℝ _).eq_of_nhds]
    have hb: Radial.jet j (k+2) v=Radial.jet m k v:=by
        have h:= favor_exp (M) hg 1 (v.2) (k+2) 2
        change Radial.jet j (k+2) (1,v.2)=Comparison.RG02.Assembly.jet m k v
        rw [show Radial.jet j (k+2) (1,v.2)=_ from h,if_pos (by omega : 2 ≤ k+2), one_pow,one_mul, Nat.add_sub_cancel]; symm; exact (jet_continuous_right (ContinuousLinearMap.snd ℝ ℝ (X)) (f:=M) (i:=k) (show ContDiffAt ℝ (↑k:WithTop ℕ∞) M 0 from hg.of_le le_top) v)
    rw [hξ,hb, Nat.add_zero]; change _=Radial.jet (c'-m) k v- Radial.jet b' _ v
    have hi: Radial.jet c' k v=0:=by unfold Radial.jet c'; rw [iteratedFDeriv_const_of_ne hk]; simp
    have hlo: Radial.jet (-m) k v=-Radial.jet m k v:= by simp [Radial.jet,iteratedFDeriv_neg_apply]
    rw [sub_eq_add_neg c', Laplace.jet_add (show ContDiffAt ℝ ω c' 0 from contDiffAt_const) (show ContDiffAt ℝ ω (-m) 0 from hm.neg) v, hi,hlo]; abel
end YM.Qlocal.Binding
