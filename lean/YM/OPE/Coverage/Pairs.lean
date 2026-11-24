import YM.OPE.Coverage.Fields
/-! ## Genuine two-point reflection meters on finite shelf tests
Pick a finite list already in the common free field model through each
finite horizon. Pairings on the dense weak SHELF will dominate the squared
norm, by separated nonvanishing and operator-norm convergence (so both
spectator vector and input can vary). No physical coefficient is fitted
with these extra detectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG Next.UVStress Spec Levy MeterTest
open Maxwell Push.FiniteDetection.Free
open scoped ContDiff Topology BigOperators Classical
variable {G:Gauge}{F:Order}{L:Register G}
section pair
variable (S:Table L) (h:S.Smooth)(d:ℕ) (r:ℝ)(hr:0<r)(t:Test 2)
local notation "V" => S.Field d
def blit (x y:V):Fin 2→S.Tag:=Fin.cons ⟨d,x⟩ (fun _=>⟨d,y⟩)
def pointwise (x y:V)(z:Points 2):=disc (blit S d x y) (r • z)
def scene(x y:V):=t.applyTo (pointwise S d r x y)
def pixels(x y:V):= t.applyTo (disc (blit S d x y))
lemma lawful {x y:V}{z:Points 2}:pointwise S d r x y z = S.classMoment S (fun _:Fin 2=>d) (r • z) ![x,y] :=by
     have he:blit S d x y=fun (i:Fin 2)=> (⟨d, ![x,y] i⟩ : S.Tag):=by ext1 i; fin_cases i <;> rfl
     rw [pointwise,he]; rfl

def fide (x:V):V→ₗ[ℂ]ℂ where
   toFun := scene S d r t x
   map_add' p q :=by
      change t.applyTo _=_; rw [(_ : pointwise S d r x (p+q) = pointwise S d r x p + pointwise S d r x q)]
      · exact Next.UVStress.test_add _ _ ((smoothZoom h _ hr).continuousOn) ((smoothZoom h _ hr).continuousOn) _
      funext z; let g:= (S.classMoment S (fun _:Fin 2=>d) (r • z)).toLinearMap ![x,q] 1
      have he(p:V): ![x,p] = update ![x,q] 1 p:=by ext i; fin_cases i <;> simp
      simp only [Pi.add_apply]; have h'(p:V) : pointwise S d r x p z=g p:=by rw [lawful (x:=x) (y:=p),he]; rfl
      rw [h',h',h']; exact g.map_add p q
   map_smul' a p:=by
      change t.applyTo _=_; rw [(_ : pointwise S d r x (a • p) = a • pointwise S d r x p)]
      · exact Next.UVStress.test_smul ..
      funext z; let g:= (S.classMoment S (fun _:Fin 2=>d) (r • z)).toLinearMap ![x,p] 1
      have he(q:V): ![x,q] = update ![x,p] 1 q:=by ext i; fin_cases i <;> simp
      simp only [Pi.smul_apply]; have h'(p:V) : pointwise S d r x p z=g p:=by rw [lawful (x:=x) (y:=p),he]; rfl
      rw [h',h']; exact g.map_smul a p

def credits:V→ₗ[ℂ]V→ₗ[ℂ]ℂ where
   toFun := fide S h d r hr t
   map_add' p q:=by
      apply LinearMap.ext; intro x; let g:Next.UVStress.MeterTest S:=⟨1,t,fun _=>⟨d,x⟩⟩
      exact (g.checkAt h d r hr).map_add _ _
   map_smul' a p:=by
      apply LinearMap.ext; intro x; let g:Next.UVStress.MeterTest S:=⟨1,t,fun _=>⟨d,x⟩⟩
      exact (g.checkAt h d r hr).map_smul _ _
end pair
section topology
variable {E X:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]{u:Filter X}{f:X→E}{x:E}
local notation "Armed" => E→ₗ[ℂ] E→ₗ[ℂ] ℂ

theorem bilinear_collision {P:X→Armed} (g:Armed) {h:X→E} {y:E}(hu:∀ x y,Tendsto (fun i=>P i x y) u (𝓝 (g x y))) (hx:Tendsto f u (𝓝 x))(hh:Tendsto h u (𝓝 y)):Tendsto (fun i=>P i (f i) (h i)) u (𝓝 (g x y)):=by
     have he(p:E):Tendsto (fun i=>P i (f i) p) u (𝓝 (g x p)):=by
          let A : (E→ₗ[ℂ] ℂ)→ₗ[ℂ]ℂ := LinearMap.applyₗ (R:=ℂ) p
          exact Dash.arcing (Dash.fit_plane (fun i=> A.comp (P i)) (A.comp g) (fun v=>hu v p)) hx
     exact Dash.arcing (Dash.fit_plane _ _ he) hh

lemma collide (P:Armed) {g:X→E} (h:X→E){y:E}(hx:Tendsto g u (𝓝 x))(hh:Tendsto h u (𝓝 y)): Tendsto (fun i=>P (g i) (h i)) u (𝓝 (P x y)) :=
     bilinear_collision (P:=fun _:X=>P) P (fun _ _=> tendsto_const_nhds) hx hh
end topology
variable (C:Family G)(d:ℕ)
set_option quotPrecheck false
local notation "mCb" => Bel C.book
local notation "smH" => Maxwell.table_smooth _
local notation "W" => (mCb).Field d
def minted(t:Test 2) : W→ₗ[ℂ]W→ₗ[ℂ]ℂ := credits (mCb) smH d (1:ℝ) zero_lt_one t
def grant(t:Test 2)(v:W):ℂ:= minted C d t v (reflect (C:=C) d v)

lemma mint_exact(t:Test 2)(x y:W):minted C d t x y=t.applyTo (disc (blit (mCb) d x y)) :=by
     change t.applyTo (fun i=>disc _ ((1:ℝ) • i)) = _; simp only [one_smul]
lemma grant_tends {X:Type*}{l:Filter X}{u:W}(t:Test 2)(f:X→W)(h:Tendsto f l (𝓝 u)):Tendsto (grant C d t ∘ f) l (𝓝 (grant C d t u)) :=
  collide (minted C d t) ((reflect (C:=C) d) ∘ f) h (Levy.reflect_limit _ h)
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000 in
lemma grant_sees (v:W)(hv:v≠0):∃ t, grant C d t v ≠ 0:=by
     by_contra! ht
     let Q := disc (blit (mCb) d v (reflect (C:=C) d v))
     have hQ:ContinuousOn Q (conf _):=(Next.UVStress.smoothDisc smH _).continuousOn
     have he:= (Test.weak_null hQ).mp (fun t=> mint_exact C d t _ _ ▸ ht t)
     have hh:=he detectors_in
     have hf := (Levy.free_positive (C:=C) d v hv).ne'
     apply hf; change Complex.re (Levy.free2 d v _) = _
     refine congrArg Complex.re (Eq.trans ?_ (show Q detectors= _ from hh))
     have hp : Levy.free2 d v (Levy.reflect (C:=C) d v) =
                pointwise (mCb) d (1:ℝ) v (Levy.reflect d v) detectors := by
         have he:=Eq.symm (lawful (x:=v) (y:=Levy.reflect (C:=C) d v) (z:=detectors) (mCb) d (1:ℝ))
         rw [one_smul] at he; exact he
     have hj : pointwise (mCb) d (1:ℝ) v (Levy.reflect d v) detectors=Q detectors:=congrArg Q (one_smul ℝ detectors)
     exact hp.trans hj

lemma silver_tests: ∃ p:Finset (Test 2),∀ v:W,‖v‖=1 → ∃ t ∈ p,grant C d t v ≠ 0:= by
     let K t:= {x:W|grant C d t x≠0}
     have hf(t):IsOpen (K t):= isOpen_compl_singleton.preimage (continuous_iff_continuousAt.mpr fun x=>grant_tends C d t (l:=𝓝 x) id tendsto_id)
     let z:=Metric.sphere (0:W) 1
     obtain ⟨s,hs⟩ := (show IsCompact z from isCompact_sphere (0:W) 1).elim_finite_subcover K hf (fun x hx=> Set.mem_iUnion.mpr (grant_sees C d x (norm_ne_zero_iff.mp (((mem_sphere_zero_iff_norm (r:=1)).mp hx).trans_ne one_ne_zero))))
     refine ⟨s,fun x hx=> ?_⟩
     obtain ⟨a,ha⟩:= Set.mem_iUnion.mp (hs ((mem_sphere_zero_iff_norm).mpr hx)); obtain ⟨p,hp⟩:= Set.mem_iUnion.mp ha
     exact ⟨a,p,hp⟩
def silver:= (silver_tests C d).choose
lemma cap(D:ℕ):∀ᶠ R:ℝ in atTop,∀ (d:Fin (D+1)) t, t∈silver C (d:ℕ) → tsupport t ⊆ Scaling.window R 2 :=by
    exact eventually_all.mpr fun d=>Silver d
where Silver (d:Fin (D+1)):= (silver C d).eventually_all.mpr (fun i _=> Work.A05.compact_fits (show IsCompact (tsupport i) from i.hasCompactSupport) i.tsupport_subset)
end YM.OPE.Coverage
