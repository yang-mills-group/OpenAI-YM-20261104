import YM.GapsContact.Tube.Earn
/-!
# Scaled surface and quantitative temperance

Real **absolute and joint** tests including common position. Recovers W with the original
`condense` scaling and positivity limit order (first remove imaginary displacements to test
as W, then bounds independent of UV lengths). Doesn't assert the power series comparison
on that real boundary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Tunnel
open Function Set Filter Boundary Surface Analysis Distribution MeasureTheory Trace Trace.Pilot
open TraceExtension Ascent Ascent.Survey EveryPhase Next.BOUNDARY Spec
open scoped Topology BigOperators InnerProductSpace Classical ContDiff NNReal
universe u
variable {n:ℕ}
variable {G:Gauge}
section Damping
variable {L:Register G} {S:Table L}
abbrev reWaves (T:Waves S) (r:ℝ) : Waves S := ⟨fun n z y=> T.F n (r • z) (r • y)⟩
-- use `condense` geometry from Trace.
def shower {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] (r:ℝ):Probe E →L[ℂ] Probe E :=
     if h : r≠0 then (↑((r⁻¹)^Module.finrank ℝ E):ℂ) • Probe.along
       (ContinuousLinearEquiv.smulLeft (Units.mk0 r⁻¹ (inv_ne_zero h))) else 0
-- Only r>0 used; equality to both test definitions at those. Need lemma call syntax.
lemma shower_at {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E]{r:ℝ}(hr:0<r)(f:Probe E):shower r f= condense r⁻¹ f:=by
   ext1 x; unfold shower; rw [dif_pos hr.ne', condense_eval r⁻¹ (by positivity)]
   change (↑(r⁻¹ ^ Module.finrank ℝ E):ℂ) • f (r⁻¹ • x)=_; rw [Complex.coe_smul]
variable (T: Waves S)(v:Fin n→ S.Union)
lemma re_rest (y: Heights n)(x:Points n) (r:ℝ): (reWaves T r).restricted v y x=T.restricted v (r • y) (r • x):=by
   unfold Waves.restricted reWaves
   change T.F n (r • shift x y) (r • Boundary.trace x) v=_; rw [show r • shift x y=shift (r • x) (r • y) from ?_, show r • Boundary.trace x = Boundary.trace (r • x) from ?_] -- dsimp
   · funext i; simp [Boundary.trace]
   funext i; simp [shift,Complex.real_smul,mul_assoc] -- inspect

lemma ponder (f:Points n→ℂ)(g: Joint n){r:ℝ}(hr:0<r): (∫ y,f (r • y)*g y)=∫ y, f y*condense r⁻¹ g y:=by
   let k:= r^ Module.finrank ℝ (Points n)
   let T (y:Points n):=f y * g (r⁻¹ • y); have hh(y): T (r • y)= f (r • y)*g y:=by simp[T,hr.ne']
   simp_rw [← hh]; rw [Measure.integral_comp_smul_of_nonneg volume T _ (hR:=hr.le)]
   simp_rw [condense_eval _ (inv_pos.mpr hr), mul_smul_comm, integral_smul,inv_pow]; rfl
lemma ponder_int (f:Points n→ℂ)(g:Joint n){r:ℝ}(hr:0<r)(h:Integrable (fun y=>f y*condense r⁻¹ g y)) : Integrable fun y=> f (r • y) * g y:=by
   let T (y:Points n):=f y*g (r⁻¹ • y); have hh(y): T (r • y)= f (r • y)*g y:=by simp [T,hr.ne']
   simp_rw [← hh]; apply (integrable_comp_smul_iff volume T hr.ne').mpr
   have hk : r⁻¹^ Module.finrank ℝ (Points n)≠0:=by positivity
   simp_rw [condense_eval _ (inv_pos.mpr hr),mul_smul_comm] at h
   exact (integrable_smul_iff hk T).1 h
lemma re_psi (y: Heights n)(g:Joint n){r:ℝ}(hr:0<r): (reWaves T r).psi v y g=T.psi v (r • y) (condense r⁻¹ g):=by unfold Waves.psi; simp_rw [re_rest]; exact ponder _ g hr
lemma east_up (y: Heights n)(hy:y∈east n)(r:ℝ)(hr:0<r):r • y∈east n:=fun _ _ he=>mul_lt_mul_of_pos_left (hy he) hr
lemma at_shower {E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E]{r:ℝ}(hr:0<r)(g:Probe E)(x:E):
    let a:= r⁻¹; let T:= a • ContinuousLinearMap.id ℝ E; fderiv ℝ (condense r⁻¹ g) x=a^ Module.finrank ℝ E • (fderiv ℝ g (T x)).comp T:=by
    intro a T; rw [show (condense r⁻¹ g:E→ℂ)=(fun y=>a^Module.finrank ℝ E • g (T y)) from funext (condense_eval _ (inv_pos.mpr hr) g)]
    exact (((g.differentiableAt (x:=T x)).hasFDerivAt.comp x (T.hasFDerivAt (x:=x))).const_smul (a^Module.finrank ℝ E)).fderiv
lemma clock_scales (y:Heights n){r:ℝ}(hr:0<r)(g:Joint n):
     condense r⁻¹ (Waves.clock y g) = Waves.clock (r • y) (condense r⁻¹ g):=by
   let a:= r⁻¹; let A := a ^ Module.finrank ℝ (Points n)
   ext1 x
   let T:= a • ContinuousLinearMap.id ℝ (Points n)
   have hh:fderiv ℝ (condense r⁻¹ g) x=A • (fderiv ℝ g (T x)).comp T:= at_shower hr g x
   rw [condense_eval _ (inv_pos.mpr hr)]; simp only [Waves.clock,_root_.smul_apply,LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, hh, ContinuousLinearMap.comp_apply,T,ContinuousLinearMap.id_apply, Room.dawn_mul,smul_smul,a,inv_mul_cancel₀ hr.ne',one_smul]
   exact smul_comm .. -- inspect mixed

lemma Lines_scale (h:T.Lines) {r:ℝ}(hr:0<r): (reWaves T r).Lines:=by
   intro n v g y a i hi
   have he (t:ℝ):r •(y+t • a)=r • y + t • r • a:=by rw [smul_add,smul_comm t]
   simp_rw [re_psi T v _ _ hr, he,clock_scales a hr g]
   exact h n v (condense r⁻¹ g) _ _ i (he i ▸ east_up _ hi _ hr)
lemma Along_scale (h:T.Along){r:ℝ}(hr:0<r):(reWaves T r).Along:=by
   intro n v g; simp_rw [re_psi T v _ _ hr]; exact (h n v _).comp (show ContinuousOn (fun x : Heights n=>r • x) _ from by fun_prop) fun x hx=>east_up x hx _ hr

-- corner statement at scale in entire `fields n` profile, not just fixed slopes
variable {W : Surface S}{D:∀ n, Blanket n}(X:W.Aurora D)
lemma glow_scales (x y:Points n)(r:ℝ): glow (r • x) (r • y)=(r:ℂ) • glow x y:=by ext1 i; simp [glow]; ring
lemma cascade (h:Bid.cones (S:=S) W)(hT:X.FullBody T) (g:Joint n){r:ℝ}(hr:0<r):
    Tendsto (fun y=> ∫ x,X.emit v ((r:ℂ) • glow x y)* g x) (𝓝[fields n] 0) (𝓝 (W.W n v (condense r⁻¹ g))) :=by
   have ht:Tendsto (fun x:Points n=>r • x) (𝓝[fields n] 0) (𝓝[fields n] 0)  :=by
      rw [tendsto_nhdsWithin_iff]; refine ⟨?_, Eventually.mono self_mem_nhdsWithin fun _ hy=>swell hy hr⟩
      simpa using (((show Continuous (fun x:Points n=>r • x) from by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds)
   have hp:= (X.sees hT v _ (flat n) (blankets D n) (condense r⁻¹ g)).comp ht
   rw [(D n).flatD (blankets D n) (h ..)] at hp
   simp_rw [← glow_scales]; exact hp.congr (fun y=> (ponder (fun z=>X.emit v (glow z (r • y))) g hr).symm)
end Damping

abbrev finiteToll (n:ℕ) := Seminorm ℂ (Joint n)

def taxes (n m:ℕ) : finiteToll n:= let a:= fun j=>((normSeminorm ℂ _).comp ((SchwartzMap.toLpCLM ℂ ℂ 1 (volume (α:= Points n))).comp (Waves.moves j)).toLinearMap); (∑ j∈ Finset.range (m+1), ‖Waves.coal 1 j‖₊ • a j)+a (m+1)

lemma taxes_toll (x:Joint n)(k:ℕ)(A:ℝ):Waves.toll x A k=A*taxes n k x:=by
   unfold taxes Waves.toll
   simp [_root_.sum_apply,NNReal.smul_def,Boundary.weight,Finset.mul_sum,mul_add,mul_left_comm]
lemma taxes_cont (n k:ℕ):Continuous (taxes n k):=by
   apply (Waves.tolls (n:=n) k 1).2.congr; intro x; simp [taxes_toll]

lemma soot (k:ℕ): ∃ (s:Finset (ℕ×ℕ)) (C:ℝ), 0≤C ∧ ∀ x:Joint n,taxes n k x ≤ C * s.sup (schwartzSeminormFamily ℂ _ _) x:=by
   obtain ⟨s,C,-,hC⟩:= Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (Points n) ℂ) (taxes n k) (taxes_cont ..)
   exact ⟨s,C,by positivity,hC⟩
-- proof soot convert NN

def weather {L:Register G}{S:Table L}{T : Surface S}{D:∀ n, Blanket n}(X:T.Aurora D)(v:Fin n→ S.Union) (r:ℝ)(x:Full n):ℂ:= X.emit v ((r:ℂ) • x)
lemma hollow {L:Register G}{S : Table L}{T : Surface S}{D:∀ n,Blanket n}{W: Waves S}(X:T.Aurora D)(hx:X.FullBody W)(v:Fin n→S.Union) (r:ℝ)(hr:0<r):AnalyticOnNhd ℂ (weather X v r) (tube n):=by
    intro x he
    apply AnalyticAt.comp (f:=fun t:Full n=>(r:ℂ) • t) ?_ ((show AnalyticAt ℂ ((r:ℂ) • ContinuousLinearMap.id ℂ (Full n)) x from ContinuousLinearMap.analyticAt ..))
    apply hx.hol n v; change shade _∈fields n; rw [← valley x,← glow_scales,im_glow]; exact swell he hr
lemma weather_int {L:Register G}{S : Table L}{T : Surface S}{D:∀ n,Blanket n}{W: Waves S}(X:T.Aurora D) (hx:X.FullBody W) (v:Fin n→S.Union){r:ℝ}(hr:0<r) (g:Joint n){y: Points n}(hy:y∈fields n): Integrable fun x=>weather X v r (glow x y)*g x:=by
    unfold weather; simp_rw [← glow_scales]; exact ponder_int (fun z=>X.emit v (glow z (r • y))) _ hr (hx.leaned n _ _ (swell hy hr) _)
variable {C: Family G}{S:Table C.book}{f:Extraction.Order}
variable {F:Final C f S}{hG:G.Simple}{L:Almanac F}

-- use contour.NonTangentialFree to identify tempered estimate at tax k
lemma economic (L: Almanac F)(i:Survey F)(v:Fin n→ S.Union) (k:ℕ)(A r:ℝ)(hr:0<r){D:∀ n:ℕ, Blanket n}(X:(Survey.reads L i).world.Aurora D)
   (h:∀ δ∈ Ioc (0:ℝ) 1,∀ z:Full n,Room (shade z) δ → ‖weather X v r z‖≤A* δ⁻¹^k)
   (x:Joint n):‖(Survey.reads L i).world.W n v (condense r⁻¹ x)‖≤ A * taxes n k x:=by
  let Z:=Survey.reads L i
  let T:= Z.waves; let U:= reWaves T r
  obtain ⟨hh,hu⟩:= observe L i X; change X.FullBody T at hu
  obtain ⟨Y,hY,hV⟩:= observed L i; change Y.lift=T at hY
  have he : ∀ (y: Heights n)(t:ℝ),t∈ Ioc (0:ℝ) 1 → broad y t → ∀ x:Points n,‖U.restricted v y x‖ ≤ A*t⁻¹^k:=by
     intro y t ht hy q; have hm:= h t ht (glow q (dawn y)) (by rw [im_glow]; exact Room.of_broad hy)
     have hp:y∈east n:=fun a b he=>sub_pos.mp (ht.1.trans_le (hy a b he)); erw [re_rest]; unfold weather at hm; rw [← glow_scales,← Room.dawn_mul, hu.pure n v _ _ (east_up _ hp _ hr)] at hm; exact hm
  have hs:= U.storm he (Along_scale T (hY ▸ Y.shore.2) hr) (Lines_scale T (hY ▸ Y.shore.1) hr) 0 (light n) x
  have ht:= (Survey.fits L i).corner.corner n v (condense r⁻¹ x)
  have hP:Tendsto (fun y:Heights n=>r • y) (𝓝[east n] 0) (𝓝[east n] 0) :=by
     rw [tendsto_nhdsWithin_iff]; refine ⟨?_, Eventually.mono self_mem_nhdsWithin fun _ hy=>east_up _ hy _ hr⟩
     simpa using (((show Continuous (fun x:Heights n=>r • x) from by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds)
  haveI : (𝓝[east n] 0).NeBot:=awaits (light n)
  rw [tendsto_nhds_unique ((ht.comp hP).congr (fun y=> (re_psi T v y x hr).symm)) hs, ← taxes_toll]; exact U.cost he 0 (light n) x

-- uniform exact tempered conclusion through ANY measured frame based on own-scale Gram cost.
structure Temperate (L: Almanac F)(v:ℝ→ Fin n→S.Union)(k:ℕ)(A:ℝ)(r:ℝ) : Prop where
   full : ∀ (i:Survey F) (D:∀ n:ℕ, Blanket n)(X:(Survey.reads L i).world.Aurora D),∀ δ∈ Ioc (0:ℝ) 1, ∀ z:Full n, Room (shade z) δ → ‖weather X (v r) r z‖≤A*LogV r^k *δ⁻¹^k
   damped : ∀ (i:Survey F)(φ: Joint n),‖(Survey.reads L i).world.W n (v r) (condense r⁻¹ φ)‖ ≤ A*LogV r^k*taxes n k φ

lemma Temperate.ofFull (L: Almanac F) (v:ℝ→Fin n→S.Union)(k:ℕ)(A:ℝ)(r:ℝ)(hr:0<r)(h: ∀ (i:Survey F) (D:∀ n:ℕ, Blanket n)(X:(Survey.reads L i).world.Aurora D),∀ δ∈ Ioc (0:ℝ) 1, ∀ z:Full n, Room (shade z) (r*δ) → ‖X.emit (v r) z‖≤A*LogV r^k*δ⁻¹^k) : Temperate L v k A r:=by
  have he(i:Survey F)(D:∀ n:ℕ, Blanket n)(X:(Survey.reads L i).world.Aurora D)(δ:ℝ)(hd:δ∈Ioc 0 1)(z:Full n)(hx:Room (shade z) δ):‖weather X (v r) r z‖≤A*LogV r^k*δ⁻¹^k:=h i D X δ hd _ (by rw [← valley z, ← glow_scales,im_glow]; exact hx.mul hr.le)
  refine ⟨he,fun i φ=>?_⟩
  let D:= fun n:ℕ=> Classical.choice (Integrated.reconstructionArcs.cK n)
  obtain ⟨X⟩:=Next.BOUNDARY.visible (Survey.reads L i).world D
  exact economic L i (v r) k _ r hr X (he i D X) φ

lemma Temperate.core (H:Roll.{u} F hG L){d:Fin n→ℕ}(v: ∀ i: Fin n, ℝ→ S.Field (d i)) (hv:∀ i,Measured F (d i) (v i)):
    ∃ A:ℝ,0≤A ∧ ∃ m:ℕ,∀ᶠ r in trail, Temperate L (fun r j=> S.pin _ (v j r)) m A r:=by
  obtain ⟨A,hA,m,h⟩:= full_price H v hv
  exact ⟨A,hA,m,(h.and (show ∀ᶠ r in trail,0 < r from self_mem_nhdsWithin)).mono fun _ ht=> Temperate.ofFull _ _ _ _ _ ht.2 ht.1⟩
end YM.GapsContact.Tunnel
