import YM.X.Jet.Pale
/-!
Square real analytic map implicit solve and **jet uniqueness**, coordinate-free. Admit a small region expressed via neighbourhood filters. `ContDiff ω` analytic here.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Jet
open Function Filter Set Pert.Position
open scoped Topology ContDiff BigOperators Classical
variable {E F V : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [CompleteSpace E][CompleteSpace F]
def center (f:E×F→ F)(v:(E × F) × F) := f (v.1.1,v.2)-v.1.2
lemma center_smooth (f:E×F→F)(h:ContDiff ℝ ω f): ContDiff ℝ ω (center f):= h.comp (f:=fun v:(E×F) × F=>(v.1.1,v.2)) (by fun_prop) |>.sub (show ContDiff ℝ ω (fun v:(E×F)×F=> v.1.2) from by fun_prop)

def Submerge (x:E)(f:E×F→F):= ∀ v':F, HasDerivAt (fun t:ℝ=>f (x,t • v')) v' 0
lemma open_up (x:E)(f:E×F→F)(h:Submerge x f)(hh: ContDiff ℝ ω f) : ∃ φ:E × F→ F, Reports (center f) (x,0) 0 φ:= by
   let U:=(center f); let Z:= ((x,(0:F)),(0:F)); apply Reports.of_square (center_smooth f hh).contDiffAt
   refine ⟨ContinuousLinearEquiv.refl ℝ F,?_⟩; ext1 v; change v= fderiv ℝ U Z (0,v)
   let y(t:ℝ) := ((x,(0:F)),t • v); have hy:y 0=Z:= by unfold y Z; simp
   have hl : HasDerivAt (U ∘ y) (fderiv ℝ U Z (0,v)) 0:= by
      rw [←hy]; exact (((center_smooth f hh).differentiable (by simp) (y 0)).hasFDerivAt).comp_hasDerivAt 0 (show HasDerivAt y (0,v) 0 from (hasDerivAt_const _ _).prodMk (by simpa only [one_smul] using (hasDerivAt_id' (0:ℝ)).smul_const v))
   have H: HasDerivAt (U ∘ y) v 0 := by simpa only [U,y,center,Function.comp_def,sub_zero] using h v
   exact H.unique hl
variable {φ:E × F→ F}{f:E×F→ F} {x:E}{n:ℕ}
structure Region (φ:E × F→ F)(f:E×F→F)(x y:E)(u:F) : Prop where
   forget : φ (y,0)=u
   match_ : f (y,u)=f (x,0)
   nice : ContDiffAt ℝ ω φ (y,0)
   near : ∀ᶠ v in 𝓝 ((y,(0:F)),u), center f v=f (x,0) ↔ φ v.1=v.2
   joins : ∀ᶠ z : E×F in 𝓝 (y,0), center f (z,φ z)=f (x,0)
lemma around (R:Reports (center f) (x,0) 0 φ): ∀ᶠ y:E in 𝓝 x, Region φ f x y (φ (y,0)):= by
   let Z (y:E):=(y,(0:F)); have hz:Tendsto Z (𝓝 x) (𝓝 (x,0)):= tendsto_id.prodMk_nhds tendsto_const_nhds
   have he : center f ((x,0),0)= f (x,0):= sub_zero _
   filter_upwards [ hz.eventually (eventually_eventually_nhds.mpr R.curves), (hz.prodMk_nhds (show Tendsto (φ ∘ Z) _ (𝓝 0) from R.fixes ▸ R.diff.continuousAt.tendsto.comp hz)).eventually (eventually_eventually_nhds.mpr R.strict), hz.eventually (R.diff.eventually (by simp))] with y hy hY hw
   have ha:=hy.self_of_nhds; refine ⟨rfl, (by simpa [Z,center] using ha),hw, hY.mono fun v hv=>he ▸ hv, hy.mono fun u h=> h.trans he⟩ -- ↔ orientation near
variable (H: Reports (center f) (x,0) 0 φ) {y:E}{u:F}(R:Region φ f x y u)
-- uniqueness doesn't need x-fixed except RHS
variable (a:Word E)(f':E→F)
def pick (φ:E×F→F)(u:E) := φ (u,0)
lemma pick_nice (R:Region φ f x y u) : ContDiffAt ℝ ω (pick φ) y:= R.nice.comp (f:=fun v=>(v,0)) y (by fun_prop)
lemma region_writes (R:Region φ f x (a 0) u) (hhc:ContDiff ℝ ω f) : run f (pair a (run (pick φ) a))=just (f (x,0)):= by
   funext i; let g:=delay a i; have hh : Act i g a := Act.swell _ le_rfl; let w (t:ℝ):= (g t,pick φ (g t))
   have he : Act i (f ∘ w) (run f (pair a (run (pick φ) a))):= (hh.zipper (hh.transit (pick_nice R))).transit (show ContDiffAt ℝ ω f (pair a (run (pick φ) a) 0) from hhc.contDiffAt)
   have hw : f ∘ w =ᶠ[𝓝 0] fun _=> f (x,0):= by
     have ht : Tendsto (fun t=>(g t,(0:F))) (𝓝 0) (𝓝 (a 0,0)):= (show Tendsto g (𝓝 0) (𝓝 (a 0)) from (by rw [← hh.zero]; exact hh.nice.continuousAt.tendsto)).prodMk_nhds tendsto_const_nhds
     exact (ht.eventually R.joins).mono (fun t h=> by simpa [center,pick,w] using h)
   exact ((he.realizes hw).writes i le_rfl).symm.trans ((Act.static (n:=i) (f (x,0))).writes i le_rfl)

lemma uniqueness (R:Region φ f x (a 0) u)(hh:ContDiff ℝ ω f)(b:Word F)(hu:b 0=u)(he:Fits n (fun _=>f (x,0)) (run f (pair a b))) : ∀ i≤n, b i=run (pick φ) a i:= by
    let g:=delay a n; let k:=delay b n; have ha:Act n g a:= Act.swell _ le_rfl; have hb:Act n k b:= Act.swell _ le_rfl
    let q (t:ℝ):= f (g t,k t); let C:=f (x,(0:F)); have hq:Act n q (run f (pair a b)) := (ha.zipper hb).transit hh.contDiffAt
    let y(t:ℝ):=(g t,q t-C); let m:=pair a (just (0:F))
    have ht : Act n (fun (t:ℝ)=>q t - C) (just (0:F)):= by
       refine ⟨hq.nice.sub contDiffAt_const,fun i hi=> ?_⟩; suffices hz: someJ (fun t:ℝ=> q t-C) i=someJ (fun _ : ℝ=> (0:F)) i from hz.trans ( (show Act n _ _ from Act.static (0:F)).writes i hi) -- infer?
       have hv : iteratedDeriv i q 0=iteratedDeriv i (fun _ : ℝ=> C) 0 := (hq.actual i hi).trans (Eq.symm ((show Act n (fun _ : ℝ=> C) (run f (pair a b)) from ⟨contDiffAt_const,he⟩).actual i hi))
       unfold someJ; rw [iteratedDeriv_fun_sub (hq.nice.of_le le_top) contDiffAt_const,hv,sub_self]; by_cases hi:i=0<;>simp [iteratedDeriv_const, hi]
    have hY : Act n y m:= ha.zipper ht; let z (t:ℝ) := (g t,(0:F)); have hZ:Act n z m:= ha.zipper (Act.static _)
    have hy : y 0=(a 0,(0:F)):= hY.zero
    have ht: φ ∘ y =ᶠ[𝓝 0] k:= by
       have hb' := hY.nice.continuousAt.tendsto.prodMk_nhds hb.nice.continuousAt.tendsto; rw [hb.zero, hy,hu] at hb'
       filter_upwards [hb'.eventually R.near] with t h; exact h.mp (by change q t-(q t-C)=C; abel)
    intro i hi; have hV : ContDiffAt ℝ ω φ (m 0):= R.nice
    have hn := ((hY.transit hV).realizes ht); exact (hb.writes i hi).symm.trans ((hn.writes i hi).trans (((hZ.transit hV).writes i hi).symm.trans ((ha.transit (pick_nice R)).writes i hi)))
end YM.PositionX.Jet
