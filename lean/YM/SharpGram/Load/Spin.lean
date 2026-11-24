import YM.SharpGram.Load.Illuminate
/-! Relative convergence under full Euclidean rotations (not uniform
in rotation here). Relations & exponentials in ℝ-linear realified reps;
no assumption that Broad scales originally carried exact orthogonal alignment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Ward Org Extraction Analysis Spec Next.UVStress NormedSpace
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
local notation "V'" => Maxwell.Free.scheme C.labels
local notation "σ" => Maxwell.Free.spin_free C.labels
local notation "E" => Maxwell.Free.gear C.labels
local notation "α" => F.sector.turns
local notation "S'"=> (Bel C.book)
local notation "T" => F.phase.transport
variable {u : Filter (ℕ×ℕ)}{d : ℕ}

section ode
variable {P: Type*}[NormedAddCommGroup P][NormedSpace ℝ P][CompleteSpace P]
-- Might be useful for RG15. coupling not involved in this parameter
lemma all_exp {B:P→L[ℝ] P} (f:ℝ→P) (hf:∀ t,HasDerivAt f (B (f t)) t) (t:ℝ) :
    f t = exp (t • B) (f 0) := by
    let k (t:ℝ): P →L[ℝ] P := exp (t • (-B)); let g(t:ℝ):P:= k t (f t)
    have h(t:ℝ): HasDerivAt g 0 t := by
      convert ((hasDerivAt_exp_smul_const (-B) t).clm_apply (hf t)) using 1
      simp only [mul_neg]; exact (neg_add_cancel (exp (t • -B) (B (f t)))).symm
    have he := is_const_of_deriv_eq_zero (fun i=>(h i).differentiableAt) (fun i=>(h i).deriv) t 0
    haveI : NormedAlgebra ℚ (P→L[ℝ] P) := .restrictScalars ℚ ℝ _
    have hg : k 0=1:=by unfold k;simp
    change k t (f t) = k 0 (f 0) at he; rw [hg] at he
    change k t (f t)= f 0 at he; rw [← he,show exp (t• B) (k t (f t))=(exp (t • B)*k t) (f t) from rfl]
    unfold k; rw [smul_neg,← exp_add_of_commute (Commute.refl _).neg_right,add_neg_cancel,exp_zero]; rfl
lemma across_ode (B:ℕ→P→L[ℝ] P)(X:P→L[ℝ] P)(h:Tendsto B atTop (𝓝 X))(x:P) (F0:ℕ→ℝ→P) (f:ℝ→P) (hF:∀ i,F0 i 0=x) (hf:f 0=x) (v:∀ i t,HasDerivAt (F0 i) (B i (F0 i t)) t) (w:∀ t,HasDerivAt f (X (f t)) t) (t:ℝ) :
     Tendsto (fun i=> F0 i t) atTop (𝓝 (f t)) := by
   simp_rw [all_exp f w t, all_exp (F0 _) (v _) t,hf,hF]
   haveI : NormedAlgebra ℚ (P→L[ℝ] P) := .restrictScalars ℚ ℝ _
   have ht : Tendsto (fun i => exp (t • B i)) atTop (𝓝 (exp (t • X))) := (show Tendsto _ atTop (𝓝 (t • X)) from ((tendsto_const_nhds (x:=t)).smul h)).exp
   exact (ContinuousLinearMap.apply ℝ P x).continuous.continuousAt.tendsto.comp ht
end ode
lemma parameter_start (w: Ortho.Skew) : Ortho.oneParameter w 0=1 := Subtype.ext (by change exp ((0:ℝ) • w.val)=1;simp)
lemma add_parameter (w : Ortho.Skew)(s t:ℝ): Ortho.oneParameter w (s+t)= Ortho.oneParameter w s*Ortho.oneParameter w t:= by
  apply Subtype.ext; let v:= w.val; haveI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ _
  change exp ((s+t) • v)= exp (s • v)*exp (t • v)
  rw [add_smul];exact exp_add_of_commute (((Commute.refl v).smul_left s).smul_right t)

abbrev realHom {G: Gauge}{L R:Register G} (S0:Table L) (T0:Table R) (d:ℕ) := S0.Field d→L[ℝ] T0.Field d
lemma acts_parameter {L:Register G} {S:Table L} {K : Rotation S}{B : DiffPlan S}{H:S.RealSpin}(h: K.Laws B H)
    (w: Ortho.Skew)(t:ℝ)(x:S.Field d): HasDerivAt (fun t=> K.act d (Ortho.oneParameter w t) x) (K.lie d w (K.act d (Ortho.oneParameter w t) x)) t := by
  let v:=K.act d (Ortho.oneParameter w t) x
  let f(s):=K.act d (Ortho.oneParameter w s) v
  have hk: HasDerivAt f (K.lie d w v) 0:= h.infinitesimal d w v
  have hi : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const t
  have he := hk.scomp_of_eq t hi (by simp)
  rw [one_smul] at he
  rw [show f ∘ (fun s:ℝ => s-t)=(fun t=> K.act d (Ortho.oneParameter w t) x) from funext (fun s=> Eq.symm ?_ )] at he
  exact he
  change _=K.act d (Ortho.oneParameter w (s-t)) v
  unfold v; rw [← h.group,← add_parameter,sub_add_cancel]

variable (d)
local instance {L:Register G}(S:Table L)(d) : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _

def coil {L:Register G}{S:Table L}(K:S.Rotation)(v:Ortho.Skew) : realHom S S d :=
   (LinearMap.toContinuousLinearMap (K.lie d v)).restrictScalars ℝ

def adjust {k : Filter (ℕ×ℕ)} (B:Lenses.Mantle F k)(i:ℕ)(w: Ortho.Skew) : realHom S' S' d :=
  LinearMap.toContinuousLinearMap (((B.lens i d).symm.toLinearMap.comp (((α).lie d w).comp (B.lens i d).toLinearMap)).restrictScalars ℝ)

section
-- pointwise from generator calculus
variable (B : Lenses.Mantle F u)(hg:OPE.Services C f S)
include hg
set_option maxHeartbeats 500000 in
lemma adj_limit (w:Ortho.Skew) : Tendsto (fun k=> adjust d B k w) atTop (𝓝 (coil d E w)) := by
    let P (K:Ortho.Skew):= Tendsto (fun k=> adjust d B k K) atTop (𝓝 (coil d E K))
    suffices h:w∈Submodule.span ℝ (range Spin.K) → P w from h (by rw [Spin.spans]; trivial)
    intro hW; apply Submodule.span_induction (p:=fun v _=>P v) _ _ _ _ hW
    · rintro v ⟨j,rfl⟩
      apply clm_criterion _ _
      intro x; exact Dash.arcing (turns B hg d j) tendsto_const_nhds
    · dsimp only [P]; have hx k: adjust d B k 0=0:=ContinuousLinearMap.ext (fun x=> by change (B.lens k d).symm ((α).lie d 0 _)=0;rw [map_zero];change (B.lens k d).symm 0=0; rw [map_zero])
      have h : coil d E 0=0:=ContinuousLinearMap.ext (fun x=>by change (E).lie d 0 x =0; rw [map_zero]; rfl)
      simp [hx,h]
    · intro a b _ _ ha hb
      have hh : coil d E (a+b)=coil d E a+coil d E b:=ContinuousLinearMap.ext fun _=> by unfold coil;rw [map_add];rfl
      unfold P; rw [hh]; apply (ha.add hb).congr; intro i; apply ContinuousLinearMap.ext; intro x; unfold adjust; rw [map_add]; simp
    · intro a b _ hb; unfold P
      have h : coil d E (a • b)=a • coil d E b:=ContinuousLinearMap.ext fun _=> by unfold coil;rw [map_smul];rfl
      rw [h]; apply (tendsto_const_nhds.smul hb).congr; intro k; apply ContinuousLinearMap.ext; intro x
      change a • (B.lens k d).symm _ =(B.lens k d).symm ((α).lie d (a • b) _)
      rw [map_smul]; exact (((B.lens k d).symm.toLinearMap.restrictScalars ℝ).map_smul ..).symm
variable {d}
def motion (k d:ℕ) (g:Ortho): Spin.change S d :=
  (B.lens k d).trans ((α).act d g)
def act (k d:ℕ)(g:Ortho): Spin.Mat ((Bel C.book).Field d) :=
   LinearMap.toContinuousLinearMap (((motion B k d g).trans (B.lens k d).symm).toLinearMap)
def model (C:Family G)(d:ℕ)(g:Ortho): Spin.Mat ((Bel C.book).Field d) :=
   ((Maxwell.Free.gear C.labels).act d g).toContinuousLinearEquiv.toContinuousLinearMap
lemma spinsAt (v:Ortho.Skew)(t:ℝ) : Tendsto (fun k=>act B k d (Ortho.oneParameter v t)) atTop (𝓝 (model C d (Ortho.oneParameter v t))):= by
    apply Dash.fit_plane _ _; intro x
    let W (k:ℕ)(t:ℝ):=(act B k d (Ortho.oneParameter v t)) x
    let w(t:ℝ):=model C d (Ortho.oneParameter v t) x
    have h : ∀ t, HasDerivAt w (coil d E v (w t)) t:=fun t=> acts_parameter (Maxwell.Free.gear_laws C.labels) ..
    have hv k t: HasDerivAt (W k) (adjust d B k v (W k t)) t := by
        let Y:= B.lens k d; let z:=Y x
        have q:=acts_parameter (T).spots v t z
        have h': adjust d B k v (W k t)=Y.symm ((α).lie d v ((α).act d (Ortho.oneParameter v t) z)) := by
           change Y.symm ((α).lie d v (Y (Y.symm _)))= _; rw [Y.apply_symm_apply];rfl
        rw [h']; exact (Y.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t q
    have hx k : W k 0=x := by
        change (B.lens k d).symm ((α).act d (Ortho.oneParameter v 0) _) = _
        rw [parameter_start,(T).spots.fixes]; exact (B.lens k d).symm_apply_apply _
    refine across_ode _ _ (adj_limit d B hg v) x W w hx ?_ hv h t -- syntax fix refine
    change (E).act d (Ortho.oneParameter v 0) x = _; rw [parameter_start,(Maxwell.Free.gear_laws C.labels).fixes]
end
end YM.SharpGram.Load
