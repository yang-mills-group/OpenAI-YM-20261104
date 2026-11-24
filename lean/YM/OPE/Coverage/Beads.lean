import YM.OPE.Coverage.Mobility
import YM.Extra.WEAK_SCALING_ACTLAW.Adjust

/-!
## Finite-grid differential meters on those shelves

Read the probes by the exact differentiated-slot laws, both before and
after inclusion; not an equicontinuity assumption on stresses. Adjacent
weak maps are provisionally *not* assumed filtration aligned. -/
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 20000000
set_option synthInstance.maxHeartbeats 1000000
open scoped Matrix.Norms.Frobenius
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG
open Next.UVStress Spec Maxwell Extra
open WeakScaling (Equipped)
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}{F:Extraction.Order}{C:Family G}{S:Table C.book}{d D D' n n':ℕ}{μ R:ℝ}{r:ℕ→ℝ} (H:Final C F S)
set_option quotPrecheck false
local notation "𝑬" => (Bel C.book).Field
variable (p:Shelf H r D n μ) (P:(Bel C.book).Hierarchy)
def oldChart(d i:ℕ)(ha:Nonempty (Spin.change S d)): Spin.change S d:= if h:Bijective (p.maps i d) then LinearEquiv.ofBijective _ h else Classical.choice ha
variable (b:∀ e,Nonempty (Spin.change S e))
local notation "A" => fun k d=> oldChart H p d k (b d)
local notation "U" => p.maps
local notation "Hy" => H.room.kernel
lemma old_agrees(i d:ℕ)(h:Bijective (U i d)):(A i d).toLinearMap=p.maps i d:=by
  change (oldChart H p d i (b d)).toLinearMap = _; rw [oldChart,dif_pos h]; rfl

lemma apart_in(l:ℕ)(hr:0<R)(he:R≤ μ):WeakScaling.apart R l ⊆ Scaling.window μ l:= by
  intro x hx
  refine ⟨fun i j h=> ?_, hx.1.le.trans he⟩
  obtain ⟨a,ha⟩:= hx.2 i j h
  have hh:= dist_le_pi_dist ((x j).ofLp) ((x i).ofLp) a
  rw [← Real.dist_eq] at ha; change _ ≤ dist (x i).ofLp (x j).ofLp; rw [dist_comm];exact (inv_le_inv₀ (by linarith) hr|>.mpr he).trans (ha.le.trans hh)

def shelfWatch {n'}(w: Fin n' → (Bel C.book).Tag) (k:ℕ) (t:Test (n'+1))(d:ℕ):(Bel C.book).Field d→ₗ[ℂ]ℂ:=
  (WeakScaling.heard (Hy) (p.fades.1 k) (fun i' =>(panels (p.maps k) (w i'))) t d).comp (p.maps k d)

def fictive (P:(Bel C.book).Hierarchy) {n'}(w:Fin n'→ (Bel C.book).Tag) (t:Test (n'+1))(d:ℕ): ((Bel C.book).Field d) →ₗ[ℂ] ℂ:= WeakScaling.heard P one_pos w t d

lemma adjWindow (d l:ℕ) (w:Fin l→(Bel C.book).Tag) (t:Test (l+1)) (x:(Bel C.book).Field d)
        (hw : WeakScaling.capped D w) (hd : d ≤ D) (hn : l+1 ≤ n) (ht : tsupport t ⊆ Scaling.window μ (l+1)) :
    Tendsto (fun j=>shelfWatch H p w j t d x) atTop (𝓝 (fictive P w t d x)) :=by
      let v:= Fin.cons (α:=fun _ : Fin (l+1) => (Bel C.book).Tag) ⟨d,x⟩ w
      have ht' : ∀ i,(v i).1 ≤ D:= fun i=> Fin.cases hd (fun j=>hw j) i
      have hz := p.smears (l+1) hn v ht' t ht
      have heq(i)(Ui:Panel S): Fin.cons (α:=fun _ : Fin (l+1)=>S.Tag) ⟨d,Ui d x⟩ (fun j=>panels Ui (w j)) i = panels Ui (v i) := by unfold v; refine Fin.cases rfl (fun _=>rfl) i
      have hl(i): shelfWatch H p w i t d x = t.applyTo (Next.UVStress.tested (p.path i) (p.maps i) v):=by
         rw [shelfWatch,LinearMap.comp_apply, WeakScaling.heard_apply]
         apply congrArg t.applyTo; funext z; apply congrArg (fun η: Fin _→S.Tag =>disc η (p.path i • z)) (funext (fun j=> heq j _))
      simp_rw [hl]; rw [show fictive P w t d x= t.applyTo (WeakScaling.rescale (1:ℝ) w x) from WeakScaling.heard_apply P one_pos ..]
      have hf : WeakScaling.rescale (1:ℝ) w x=disc v:=by funext u; exact congr_arg (disc v) (one_smul ℝ u)
      rw [hf]; exact hz
-- all cutoffs scalarizing equipment probes, no refitting.
variable (hμR : R ≤ μ) (hR : (0:ℝ) < R) (he : ∀ e : ℕ, e ≤ d → WeakScaling.Equipped P e n D R) (hd : d ≤ D)
include hμR hR he hd b
lemma shelf_equipment_bij (e:ℕ)(he':e ≤ d): ∀ᶠ k : ℕ in atTop,Bijective (p.maps k e):=by
   obtain ⟨T,hT,hT'⟩:= he e he'
   let W₀(i:ℕ): (Bel C.book).Field e →ₗ[ℂ] (T→ℂ):=LinearMap.pi (φ:=fun _:T=> ℂ) (fun x:T =>shelfWatch H p x.val.w i x.val.t e)
   have ha:= Dash.fit_plane (ℱ:=atTop) W₀ (LinearMap.pi (fun x:T=> WeakScaling.rows P x.val e)) (fun v=>tendsto_pi_nhds.mpr (fun j:T=>?_))
   swap
   · obtain ⟨g,l,k⟩:=hT' j j.prop
     exact adjWindow H p P _ j.val.n j.val.w j.val.t v l (he'.trans hd) g ((k.trans WeakScaling.clearance_apart).trans (apart_in _ hR hμR))
   filter_upwards [ha.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds (show Injective (LinearMap.toContinuousLinearMap _) from hT))] with k hk
   suffices hf : Injective (p.maps k e) from ⟨hf,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ((Classical.choice (b e)).finrank_eq)).1 hf⟩
   intro x y h; apply hk
   change W₀ k x = W₀ k y; refine funext fun j=>?_
   change shelfWatch H p j.val.w k j.val.t e x=shelfWatch H p j.val.w k j.val.t e y
   unfold shelfWatch; rw [LinearMap.comp_apply,LinearMap.comp_apply,h]

lemma shelf_inc (V': DiffPlan (Bel C.book))(hf:V'.Inclusions (Bel C.book)) (j k:ℕ)(hk:j≤k)(hb:k ≤ d) (x: 𝑬 j):Tendsto (fun i=>(A i k).symm (H.sector.derivatives.rise hk (A i j x))) atTop (𝓝 (V'.rise hk x)):= by
   obtain ⟨T,hT,hT'⟩:= he k hb
   apply Work.A04.tendsto_of_fitted (fun i => LinearMap.pi fun u:T => shelfWatch H p u.val.w i u.val.t k) _ hT _ _
   · exact (fun v=>tendsto_pi_nhds.mpr fun u : T=>adjWindow H p P _ u.val.n u.val.w u.val.t _ (hT' u u.prop).2.1 (hb.trans hd) (hT' u u.prop).1 (((hT' u u.prop).2.2.trans WeakScaling.clearance_apart).trans (apart_in _ hR hμR)))
   refine tendsto_pi_nhds.mpr fun u => ?_
   change Tendsto _ _ (𝓝 (fictive P u.val.w u.val.t k _))
   simp_rw [fictive,WeakScaling.read_inclusion P hf one_pos]
   refine Tendsto.congr' ?_ (adjWindow H p P _ u.val.n u.val.w u.val.t _ (hT' u u.prop).2.1 (hk.trans (hb.trans hd)) (hT' u u.prop).1 (((hT' u u.prop).2.2.trans WeakScaling.clearance_apart).trans (apart_in _ hR hμR)))
   filter_upwards [shelf_equipment_bij H p P b hμR hR he hd j (hk.trans hb),shelf_equipment_bij H p P b hμR hR he hd k hb] with i hx hy
   change shelfWatch H p u.val.w i u.val.t j x= shelfWatch H p u.val.w i u.val.t k ((A i k).symm (H.sector.derivatives.rise hk (A i j x)))
   rw [shelfWatch, LinearMap.comp_apply, shelfWatch,LinearMap.comp_apply,← old_agrees H p b i j hx,← old_agrees H p b i k hy,LinearEquiv.coe_toLinearMap,LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply, WeakScaling.read_inclusion Hy H.phase.transport.injection (p.fades.1 i)] -- b binder? uncertain

lemma shelf_diff (V': DiffPlan (Bel C.book))(hf:V'.Derivatives (Bel C.book)) {j:ℕ}(hj:j+1 ≤ d) (a:Axis) (x: 𝑬 j):Tendsto (fun i=>(A i (j+1)).symm (p.path i • H.sector.derivatives.deriv j a (A i j x))) atTop (𝓝 (V'.deriv j a x)):=by
   obtain ⟨T,hT,hT'⟩:= he (j+1) hj
   apply Work.A04.tendsto_of_fitted (fun i => LinearMap.pi fun u:T => shelfWatch H p u.val.w i u.val.t (j+1)) _ hT _ _
   · exact (fun v=>tendsto_pi_nhds.mpr fun u : T=>adjWindow H p P _ u.val.n u.val.w u.val.t _ (hT' u u.prop).2.1 (hj.trans hd) (hT' u u.prop).1 (((hT' u u.prop).2.2.trans WeakScaling.clearance_apart).trans (apart_in _ hR hμR)))
   refine tendsto_pi_nhds.mpr fun u => ?_
   change Tendsto _ _ (𝓝 (WeakScaling.heard P one_pos u.val.w u.val.t _ _))
   have hp:=WeakScaling.read_derivative P (V:=V') hf (r:=1) zero_lt_one u.val.w u.val.t x a
   rw [one_smul] at hp; rw [hp]
   have letW : tsupport (Dash.down u.val.t 0 a) ≤ Scaling.window μ _ := (tsupport_fderiv_apply_subset ℝ _).trans (((hT' u u.prop).2.2.trans WeakScaling.clearance_apart).trans (apart_in _ hR hμR))
   refine Tendsto.congr' ?_ ((adjWindow H p P _ u.val.n u.val.w (Dash.down u.val.t 0 a) x (hT' u u.prop).2.1 (Nat.le_succ _ |>.trans (hj.trans hd)) (hT' u u.prop).1 letW).neg)
   filter_upwards [shelf_equipment_bij H p P b hμR hR he hd j ((Nat.le_succ _).trans hj),shelf_equipment_bij H p P b hμR hR he hd _ hj] with i hx hy
   change -(shelfWatch H p u.val.w i (Dash.down u.val.t 0 a) j x) = shelfWatch H p u.val.w i u.val.t (j+1) ((A i (j+1)).symm (p.path i • H.sector.derivatives.deriv j a (A i j x)))
   rw [shelfWatch, LinearMap.comp_apply, shelfWatch,LinearMap.comp_apply,← old_agrees H p b i j hx,← old_agrees H p b i (j+1) hy,LinearEquiv.coe_toLinearMap,LinearEquiv.coe_toLinearMap,LinearEquiv.apply_symm_apply, WeakScaling.read_derivative Hy H.phase.transport.derivatives (p.fades.1 i)]
end YM.OPE.Coverage
