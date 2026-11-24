import YM.FVA2.Orbit.Vertical
/-!
 # Feynman- or Gaussian-smeared gauge conditions on inversion links

 Their gauge derivatives must be computed for the SAME rooted site
 convention, at the full field (thus not assumed to be on the slice).
 Define arbitrary analytic ones for this comparison. Linear log gauge condition is a special case.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Feyn
open Function Set Filter Finset MeasureTheory PertExtension Orb Orbit
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {n:Lattice.Side}
local notation "R"=> Root G n
local notation "V"=> Rep G n

private abbrev normal (d:V→R)(x:V):= fderiv ℝ d x ∘L (vertical x).toContinuousLinearMap

structure Scent (G:Gauge)(n:Lattice.Side) where
 d : Rep G n → Root G n
 origin : d 0=0
 analytic : ContDiffAt ℝ ω d 0
 shape : Bijective (fderiv ℝ d 0 ∘L (vertical (0:Rep G n)).toContinuousLinearMap)
namespace Scent
variable (b:Scent G n)
def valve (p:V) := normal b.d p
-- actual gauge derivative, no smearing of the root angle
lemma valve_calc : ∀ᶠ i:V in 𝓝 0, fderiv ℝ (fun y:R=> b.d (angle y i)) 0=b.valve i:= by
 filter_upwards [vertical_D (G:=G) (n:=n), b.analytic.eventually (by simp), angle_id (G:=G) (n:=n), tilted (G:=G) (n:=n)] with x hx hp hμ h₁
 change fderiv ℝ (b.d ∘ fun y:R=> angle y x) 0=_; rw [fderiv_comp 0, hx]; · rw [hμ]; rfl
 · change DifferentiableAt ℝ _ (angle (0:R) x); rw [hμ]; exact hp.differentiableAt (by simp)
 exact h₁
-- equivalence at origin.
def valve₀ : R≃L[ℝ] R:= (LinearEquiv.ofBijective (b.valve 0).toLinearMap b.shape).toContinuousLinearEquiv

def FP (x:Rep G n):ℝ:= meter b.valve₀ (b.valve x)
@[simp] lemma FP0 : b.FP 0=1:= meter_self _

lemma current : ContDiffAt ℝ ω b.FP 0:= by
 apply meter_map
 refine (b.analytic.fderiv_right (by simp)).clm_comp ?_
 let w(i:V): R →L[ℝ] V:= fderiv ℝ (uncurry (angle (G:=G) (n:=n))) (0,i) ∘L ContinuousLinearMap.inl ℝ R V
 have he : ContDiffAt ℝ ω w 0:= ( (angle_germ.fderiv_right (m:=ω) (by simp)).comp (f:=fun i:V=> ((0:R),i)) (0:V) (contDiffAt_const.prodMk contDiffAt_id) ).clm_comp contDiffAt_const
 refine he.congr_of_eventuallyEq ?_
 filter_upwards [vertical_D (G:=G) (n:=n), (tup (tendsto_const_nhds (x:=(0:R))) (tendsto_id (α:=V) (x:=𝓝 0))).eventually (angle_germ.eventually (by simp))] with x hp hx; exact hp.symm.trans ((pri (hx.differentiableAt (by simp))).symm) -- fix tendsto_id

variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (s:Screen G n E)
def groove (p:Root G n × E) : Root G n × E:= ( b.d ( s.tilt p ),p.2 )
@[simp] lemma stop : b.groove s 0=0:= by simp [groove,b.origin]
lemma warm : ContDiffAt ℝ ω (b.groove s) 0 := ((by rw [s.resting]; exact b.analytic : ContDiffAt ℝ ω b.d (s.tilt 0)).comp 0 s.smooth).prodMk contDiffAt_snd
local notation "Δ"=> Root G n × E
local notation "P"=> b.groove s
local notation "D"=> fderiv ℝ ( b.groove s )
private def signL (p:Δ):= fderiv ℝ (fun z:R=> b.d (s.tilt (z,p.2))) p.1
local notation "Λ"=> signL b s
-- eventual tangent identities
lemma sys : ∀ᶠ p:Δ in 𝓝 0, let f:= fun z:R=> b.d (s.tilt (z,p.2)); DifferentiableAt ℝ f p.1 ∧ ∀ (z:Δ),(D p z).2=z.2 ∧ D p (z.1,0)=( fderiv ℝ f p.1 z.1,0 ):= by
 filter_upwards [( b.warm s ).eventually (by simp)] with ⟨x,y⟩ hp
 let p:Δ:= (x,y); let f:=fun z:R=> P (z,y); let L:= b.d ∘ s.tilt
 have he:DifferentiableAt ℝ P p:= hp.differentiableAt (by simp)
 have hL :HasFDerivAt L _ p:= he.hasFDerivAt.fst
 have H : HasFDerivAt Prod.snd (ContinuousLinearMap.snd ℝ R E ∘L D p) p := he.hasFDerivAt.snd
 let K:= ContinuousLinearMap.inl ℝ R E
 have hh : DifferentiableAt ℝ (fun z:R=> L (z,y)) x:= hL.differentiableAt.comp (f:=fun z:R=>(z,y)) x (differentiableAt_id.prodMk (differentiableAt_const ..))
 intro g; refine ⟨hh,fun z=>⟨?_,Prod.ext ?_ ?_⟩⟩
 · exact DFunLike.congr_fun ( H.unique hasFDerivAt_snd ) z
 · -- tangent root
   let w:=z.1; have hx:= pri (E:=E) (a:=x) (b:=y) hL.differentiableAt; rw [ hL.fderiv ] at hx; exact DFunLike.congr_fun hx w
 exact DFunLike.congr_fun (H.unique hasFDerivAt_snd) (z.1,0)

private lemma group : ∀ᶠ p:Δ in 𝓝 0, b.valve ( s.tilt p )= Λ p ∘L ( fderiv ℝ (circle p.1) 0 ):= by
 have hV:= aimed s.smooth.continuousAt s.resting
 have h:= continuous_fst.tendsto (0:Δ); have hu:= (aimed s.germ.continuousAt s.origin).comp (continuous_snd.tendsto (0:Δ)); have hm: Tendsto (fun _ : Δ=> (0:R)) (𝓝 0) (𝓝 0):= tendsto_const_nhds
 filter_upwards [b.sys s, hV.eventually b.valve_calc, h.eventually right_turn,(tup h hm).eventually diff_circle, (tup h (tup hm hu)).eventually ((group_joins (n:=n) (G:=G)).eventually_nhds) ] with p hx he hg hs hσ
 let z:=p.1; let x:=p.2; let v:=s.tilt p; let f:=fun y:R=> b.d (s.tilt (y,x)); rw [← he]
 let g:= angle (n:=n) (G:=G); have ht : ( fun y:R=> b.d (angle y (s.tilt p)) ) =ᶠ[𝓝 0] f ∘ circle z:= by
    let W:=fun a:R=> (z,a,s.σ x); have hu:Tendsto W (𝓝 0) (𝓝 (z,0,s.σ x)):= (continuous_const.prodMk (continuous_id.prodMk continuous_const)).tendsto _
    filter_upwards [hu.eventually hσ] with y hy; exact congr_arg b.d hy.symm
 have hv:DifferentiableAt ℝ f (circle z 0):= ( hg.symm ▸ ( hx.1 : DifferentiableAt ℝ f z) : DifferentiableAt ℝ f (circle z 0))
 rw [ ht.fderiv_eq, fderiv_comp 0 hv hs.1, show circle z 0=z from hg]; rfl

lemma at_zero (x:R): D 0 (x,0)=( b.valve₀ x,0 ):= by
 have hx:= (b.group s).self_of_nhds; rw [s.resting] at hx
 have hm:fderiv ℝ (circle (0:R)) 0 = ContinuousLinearMap.id ℝ R:= by rw [ show fderiv ℝ (circle (0:R)) 0=_ from (show circle (0:R) =ᶠ[𝓝 0] id from left_turn).fderiv_eq (𝕜:=ℝ), fderiv_id]
 rw [Prod.fst_zero,hm,ContinuousLinearMap.comp_id] at hx; change _=(b.valve 0 x, 0); rw [hx]; exact ((b.sys s).self_of_nhds.2 (x,0)).2

variable [FiniteDimensional ℝ E]

def frameG : Δ≃L[ℝ]Δ := ( LinearEquiv.ofBijective (D 0).toLinearMap (by
    have h:Injective (D 0).toLinearMap:= LinearMap.ker_eq_bot.mp ( bot_unique ( fun p hp=> by
         have ht : D 0 p=0:= hp; have hh:p.2=0:= (( ( b.sys s ).self_of_nhds ).2 p).1.symm.trans (congr_arg Prod.snd ht); have hz:D 0 (p.1,0)=0:= Eq.trans (congr_arg (D 0) (show (p.1,0)=p from Prod.ext rfl hh.symm)) ht
         have hg: (b.valve₀) p.1= b.valve₀ 0:= Eq.trans (congr_arg Prod.fst (( b.at_zero s p.1 ).symm.trans hz)) (map_zero _).symm; exact Prod.ext ( b.valve₀.injective hg ) hh ) )
    exact ⟨ h,LinearMap.surjective_of_injective h ⟩
 ) ).toContinuousLinearEquiv
lemma whence : ∀ᶠ p:Δ in 𝓝 0, meter ( b.frameG s ) (D p)=b.FP (s.tilt p)*hair p.1:= by
 let Φ:= b.valve₀; let Ω:= b.frameG s
 filter_upwards [b.group s,(continuous_fst.tendsto (0:Δ)).eventually (gate_left («I»:=Away n)),b.sys s] with p hp hh hx
 let K:= D p ∘L Ω.symm.toContinuousLinearMap; let L:= (Λ p) ∘L Φ.symm.toContinuousLinearMap; let A:=ContinuousLinearMap.id ℝ E
 have hS(p:Δ): (Ω.symm p).2=p.2:= (((b.sys s).self_of_nhds).2 (Ω.symm p)).1.symm.trans (congr_arg Prod.snd (Ω.apply_symm_apply p))
 have hP(x:R) : Ω.symm (x,0)= (Φ.symm x,0):= Ω.injective ( Eq.trans ( Ω.apply_symm_apply _ ) ((congr_arg (fun y:R=>(y,(0:E))) (Φ.apply_symm_apply x)).symm.trans ( b.at_zero s (Φ.symm x) ).symm ))
 have hK : K.det=L.det*A.det:= upper K L A (fun r=>by change D p (Ω.symm _)=(Λ p (Φ.symm r),_); rw [hP]; exact (hx.2 (Φ.symm r,0)).2) (fun y=> (hx.2 (Ω.symm (0,y))).1.trans (hS (0,y)))
 unfold FP; rw [hp,cost_right]; change K.det= L.det*_ * _; rw [hK,show A.det=1 from map_one LinearMap.det,mul_assoc, mul_comm _ (hair p.1), hh]

end Scent
end YM.FVA2.Feyn
