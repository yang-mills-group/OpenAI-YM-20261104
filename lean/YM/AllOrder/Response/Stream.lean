import YM.AllOrder.Response.Invoice
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension.Series PositionX.Gauss Radial Asymptotics
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
   [NormedAddCommGroup X][NormedSpace ℝ X]{n k:ℕ}{q:X}
local notation "Ω" => X × Y
variable {V : X×Y→ℝ} {ρ:X→Y} {A H: ℝ×(X×Y)→ℝ} (h: Treaty V ρ A H)
-- no regulator/m cutoff information in the flat coefficient prescription.
local notation "F"=> (fderiv ℝ ρ 0)
def softPlane (M:X→L[ℝ] Y) : Ω →ₗ[ℝ] ℝ×(Ω) := LinearMap.prod 0 ((LinearMap.fst ℝ X Y).prod (M.toLinearMap.comp (LinearMap.fst ℝ X Y)+LinearMap.snd ℝ X Y))
def colorful (M:X→L[ℝ] Y) (x:Ω) := ((1:ℝ),x.1,M x.1+x.2)
def spine (M:X→L[ℝ] Y)(G:ℝ×(X×Y)→ℝ)(k:ℕ) : Book (X×Y) := fun i x=> Radial.jet G (i+k) (colorful M x)
def token (M:X→L[ℝ] Y)(A H:ℝ×(X×Y)→ℝ): Book (X×Y):=spine M (Real.log ∘ H) 0-spine M A 2
def liftQ (V:X × Y→ℝ)(M:X→L[ℝ] Y)(x:X):= Laplace.curvature V x (M x)
def vert (V:X × Y→ℝ)(x:Y):= Laplace.curvature V 0 x
def win (u:Book (X×Y)):Book (X×Y):=u-wirings (u 0)
def Impulse (M:X→L[ℝ] Y)(A H:ℝ×(X×Y)→ℝ):Book (X×Y):=win (token M A H)
local notation "W"=> Impulse F A H
lemma win0 (u:Book (X×Y)):win u 0=0:= sub_self _
lemma win_atn (u:Book (X×Y))(h:n≠0): win u n=u n:= funext fun i=> by change _- just (u 0 i) n=u n i; simp [just,h]
include h
lemma projected (x:Ω): token F A H 0 x=Real.log (H 0) -(liftQ V F x.1 + vert V x.2):= by
 unfold token spine; simp only [add_zero, Pi.sub_apply,jet_zero,zero_add,Function.comp_apply, h.rank 2 le_rfl]
 rw [jet_two_C contDiffAt_snd h.steer.hard rfl h.steer.quiet, show fderiv ℝ (@Prod.snd ℝ Ω) 0= _ from (hasFDerivAt_snd («𝕜»:=ℝ) (p:=(0:ℝ×Ω))).fderiv]; exact congr_arg (fun x=> Real.log (H 0)-x) (h.steer.gauge ..)
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] {P : ℝ→X}(hp:ContDiffAt ℝ ω P 0) (z:Y)
omit h in
lemma spine_cost (M:X→L[ℝ] Y)(A:ℝ×(X×Y)→ℝ)(n j:ℕ): Plausible (spine M A n j) := by
   have he:∀ x : Ω,colorful M x= ((1:ℝ), 0)+softPlane M x:=by intro x; simp [colorful,softPlane]
   unfold spine; simp_rw [he]; refine nearStep _ (Plausible.stamp ..)
omit h in
lemma token_cost (M:X→L[ℝ] Y)(A H:ℝ×(X×Y)→ℝ)(i:ℕ): Plausible (token M A H i):= (spine_cost ..).sub (spine_cost ..)
omit h in
lemma impulse_cost (M:X→L[ℝ] Y)(A H:ℝ×(X×Y)→ℝ)(i:ℕ):Plausible (Impulse M A H i):= by
   unfold Impulse; by_cases he:i=0; rw [he,win0]; exact Plausible.atom 0; rw [win_atn _ he]; exact token_cost ..
omit h in
lemma lift_cost (V:X×Y→ℝ)(M:X→L[ℝ] Y): Plausible (liftQ V M):= (Plausible.stamp V 2).app ((LinearMap.id : X→ₗ[ℝ] X).prod M.toLinearMap)
include hp
local notation "Y1"=>fun i=>(P i,z)
omit h in
lemma routeP (G:ℝ×Ω→ℝ)(hG:ContDiffAt ℝ ω G 0)(i:ℕ)(M:X→L[ℝ]Y)(n:ℕ)(hi:∀ j<n, Radial.jet G j=0): someJ (G ∘ echo (colorful M ∘ Y1)) (i+n) = weigh Y1 (spine M G n) i:= by
   let f (p:Ω):= colorful M p
   have hv:ContDiffAt ℝ ω f (P 0,z):= by unfold f colorful; exact contDiffAt_const.prodMk (contDiffAt_fst.prodMk ((M.contDiff.contDiffAt.comp (P 0,z) contDiffAt_fst).add contDiffAt_snd))
   rw [weigh_curved hG ( (show ContDiffAt ℝ ω (colorful M) (P 0,z) from hv).comp (f:=Y1) 0 (hp.prodMk contDiffAt_const)), weigh_higher hi]
   rfl
variable (he:0<H 0)
def tilted (P:ℝ→X) (M: X→L[ℝ] Y) (A H:ℝ×(X×Y)→ℝ) (z:Y):= let x:=colorful M ∘ (fun r=>(P r,z)); (Real.log ∘ H ∘ echo x)-climb2 (A ∘ echo x)
include he h
lemma tilt_bill : ContDiffAt ℝ ω (tilted P F A H z) 0 ∧
    someJ (tilted P F A H z)=weigh (fun i=>(P i,z)) (token (fderiv ℝ ρ 0) A H) ∧ ∀ᶠ i in Tested.germ, tilted P F A H z i = Real.log (H (echo (colorful F ∘ Y1) i))-A (echo (colorful F ∘ Y1) i)/i^2:= by
    let L:=F; let f:=echo (colorful L ∘ Y1); let g:=Real.log ∘ H
    let A':= A ∘ f
    have h1:= treaty_roots h; have h2: ContDiffAt ℝ ω g 0:= h.ample.log he.ne'
    have h3: ContDiffAt ℝ ω (colorful L ∘ Y1) 0:= by unfold colorful; refine ContDiffAt.comp (f:=Y1) 0 (contDiffAt_const.prodMk (contDiffAt_fst.prodMk ?_)) (hp.prodMk contDiffAt_const); exact (L.contDiff.contDiffAt.comp _ contDiffAt_fst).add contDiffAt_snd
    have hf:f 0=0:= zero_smul ..; have hg:ContDiffAt ℝ ω f 0:=contDiffAt_id.smul h3
    have ht:ContDiffAt ℝ ω A' 0:=(hf.symm ▸ h.activity).comp (f:=f) _ hg
    have hA:A' 0=0:= (congr_arg A hf).trans h1.1
    have hA': deriv A' 0=0:= ((show HasFDerivAt (𝕜:=ℝ) A 0 (f 0) from hf.symm ▸ (h1.2 ▸ (h.activity.differentiableAt (by simp)).hasFDerivAt)).comp_hasDerivAt (0:ℝ) (hg.differentiableAt (by simp)).hasDerivAt).deriv
    have hδ:ContDiffAt ℝ ω (g ∘ f) 0:=(hf.symm ▸ h2).comp _ hg
    have ht₀: ∀ j<2, jet A j=0 := by intro j hj; interval_cases j; ext; simp [h1.1]; exact funext (fun x=> by rw [Laplace.zero_first,h1.2]; rfl)
    have hs:= shifty (shifty ht); refine ⟨hδ.sub hs,?_, ?_⟩
    -- align via routeP
    · change someJ (g ∘ f-climb2 A')=_; rw [some_sub hδ hs,retrace hA hA' ht]; funext i; unfold token; rw [weigh_sub (hp.prodMk contDiffAt_const) (u:=spine F _ 0) (fun j _=> (spine_cost ..).smooth.contDiffAt) (le_refl i) (fun j _=> (spine_cost ..).smooth.contDiffAt), ←routeP hp z (g) h2 i _ 0 (by omega), ←routeP hp z A h.activity i _ 2 ht₀]; rfl
    filter_upwards [Tested.eventually_pos] with i hi; change g (f i)-climb2 A' i=g (f i)-A' i/i^2; nth_rw 1 [shift_two hA hA' i]; field_simp
end YM.AllOrder.Response
