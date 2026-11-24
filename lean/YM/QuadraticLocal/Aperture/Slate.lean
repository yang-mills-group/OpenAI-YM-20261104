import YM.QuadraticLocal.Aperture.Sage
import YM.Comparison.RG02.Cumulants.Parents
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture.Sage
open Function MeasureTheory Filter Finset Lattice Wilson RG Marker
open scoped Topology ENNReal ContDiff BigOperators Classical
open AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP Response PertExtension PertExtension.Series Radial
open Sunrise Focus Comparison.Cumulants Extra.Trajectories Toggle Drawer
open Multi Comparison.RG02 Comparison.RG02.Order Primitives.GCC PositionX.Gauss
variable {X V:Type} [Fintype V][DecidableEq V]
variable [MeasurableSpace X] (W:X→ℝ) (μ:Measure X) [IsFiniteMeasure μ] (ρ:V→X→ℝ)
variable (hW:RG.Envelope W) (hM:0≤W) (hZ:0<∫ i,W i ∂μ)(hρ:∀ i,RG.Envelope (ρ i))
local notation "𝕊"=> univ
local notation "V₁"=> Knife V
local notation "Z"=> Sage.moment W μ
local notation "P"=> (Knife V × X)
variable {k n:ℕ}
local notation "Region"=> entry_d X
local notation "φ"=> ratioN W μ ρ
local notation "ℱ"=> member ρ
local notation "Fr"=> Sunrise.Focus.census V
set_option quotPrecheck false
local notation "U"=> (Fr).Mode
local notation "Ψ"=> Scatter.transmit (Sunrise.Focus.census V) pose
variable {p:X→ℝ} {f:(V→ℝ)×X→ℝ}
-- pass to moment table.C Before projection. requires only same marker.poly.census.
include hW
open Drawer
lemma seeing (r:(Focus.census V).Mode)(u:ℂ→L[ℝ]ℝ)(h:Drawer.School Region k f): let t(x:P→ℝ):= Scatter.transmit Fr pose (fun z:V→ℝ=> moment W μ (fun y=> x (z,y)))
    u (((t f)).part r)= moment W μ (fun y=> u ((Scatter.transmit Fr pose (fun z:V→ℝ=> f (z,y))).part r)) ∧ RG.Envelope (fun y=> u ((Scatter.transmit Fr pose (fun z:V→ℝ=> f (z,y))).part r)):=by
 intro F; let a(v:V₁):=v; induction h with
 | one L h x hx=>
    let f:= shape L x; let T t:=Drawer.view t L; let L₀:=(Ψ T).part r; have hR:Plausible T:=(School.simpleR L).read
    have ht(p:ℝ): u ((Ψ (p • T)).part r)=p*u L₀:= by rw [Scatter.mul _ _ _ hR,Poly.part_smul,← Complex.real_smul, u.map_smul]; rfl -- real_smul orientation check
    have hh(p:ℝ): u ((Ψ (fun v=> T v*p)).part r)=p*u L₀:=by rw [show (fun v=>T v*p)=p • T from funext fun v=>mul_comm ..]; apply ht
    change u ((F f).part r)= Z (fun y=>u ((Ψ (fun z=>T z*x y)).part r)) ∧ _
    have hy : (fun y:X=> u ((Scatter.transmit Fr pose (fun z:V→ℝ=> (f (z,y)))).part r))=(fun y=> x y*u L₀):=funext fun y=> hh (x y)
    rw [show F f= Ψ (fun z=> T z*Z x) from ?_, hh]; swap; · apply congr_arg Ψ; exact funext fun w=> price_scale W μ x (T w)
    have hp'(x':X) := hh (x x'); simp_rw [hp']; constructor; · rw [mul_comm, show (fun y=> x y * u L₀)=u L₀ • x from funext fun y=>mul_comm .., Sage.price_scale]
    change Envelope (fun y=> u ((Ψ (fun z=> f (z,y))).part r)); rw [hy]; exact Envelope.mul hx (Envelope.const _)
 | @graft f g hH h hh h'=>
    let a (f:P→ℝ)(y:X):= u ((Ψ (fun z=> f (z,y))).part r); let p(f:P→ℝ)(z:V₁):= Z (fun y=> f (z,y));
    have hx (g:P→ℝ)(hg:School Region k g): Plausible (p g):= by
       let h:= School.cost (C:=Region) (fun (_:ℝ)=>moment W μ) (shadow ℝ) (fun _ _=>trivial) (fun u v hu hv _=> Sage.price_sum W μ hW hu hv) (fun u _ c _=> price_scale W μ u c) hg; exact School.understands h 0
    have ht:p (f+g)=p f+p g:= funext fun z=> price_sum W μ hW (hH.knows z) (h.knows z); have hv:a (f+g)=a f+a g:=funext fun y=>by
       let f'(z:V→ℝ):= f (z,y); let g'(z:V→ℝ):= g (z,y); change u ((Ψ (f'+g')).part r)= u ((Ψ f').part r)+u ((Ψ g').part r); rw [Scatter.sends (hH.understands y) (h.understands y),Poly.part_plus,map_add];
    change u (((Ψ (p (f+g)))).part r)= Z (a (f+g)) ∧ RG.Envelope (a (f+g)); rw [ht,Scatter.sends (hx f hH) (hx g h), Poly.part_plus,map_add,hv]; exact ⟨(congr_arg₂ (·+·) hh.1 h'.1).trans (price_sum W μ hW (a:=a f) hh.2 (b:=a g) h'.2).symm,hh.2.add h'.2⟩
local notation "T₀"=> fun x:X=> Multi.lambda Fr (fun i:V=> Complex.ofReal (ρ i x))
omit hW
lemma roster (x:X): Ψ (fun z=> Sage.member ρ (z,x))= T₀ x :=by
 let f(i:V)(z:V₁):= z i; let a(i:V):= (ρ i x) • f i; have he(i:V): Plausible (f i):= Plausible.line ((ContinuousLinearMap.proj (R:=ℝ) («φ»:=fun _=>ℝ) i).toLinearMap)
 change (Ψ _) = _; rw [show (fun z:V₁=> Sage.member ρ (z,x))= ∑ i:V,a i from ?_, Scatter.pile _ _ univ fun i _=> (he i).scale _]; rotate_left
 · funext z; unfold member; rw [Finset.sum_apply]; refine Finset.sum_congr rfl (fun i _=> mul_comm (z i) (ρ i x))
 exact Finset.sum_congr rfl fun i _=> by rw [Scatter.mul _ _ _ (he i),show Ψ (f i)= Focus.pose i from Scatter.factor _]; ext1 z; rw [Poly.part_smul]; unfold pose; simp only [Poly.part_send]; rw [show (Fr).fire i=(Focus.detailI i).val from rfl]; split_ifs<;> simp -- if fires defeq? 
include hρ
lemma exact_power (x:X) (n:ℕ): Ψ (fun z:V₁=> Sage.member ρ (z,x)^n)= (T₀ x)^n:=by
 induction n with
 | zero=> simp_rw [pow_zero]; exact Scatter.one ..
 | succ n ih=>
    let f(z:V₁):= Sage.member ρ (z,x); rw [pow_succ, ← ih, ← roster ρ x]; -- pow orientation applies both?
    change Ψ _ = Ψ (fun z=> f z^n)*Ψ f; simp_rw [pow_succ]; exact Scatter.carry (School.understands (school_spell ρ hρ n) x) (School.understands (school_point ρ hρ) x)
include hW
def draws (r:U) :ℝ:=moment W μ (fun y:X=>∏ i∈r.val,ρ i y)
local notation "Δ"=> draws W μ ρ
lemma Tag_bill (r:(Focus.census V).Mode) (k:ℕ) : (Scatter.transmit (Focus.census V) Focus.pose (φ k)).part r= if k=r.val.card then Complex.ofReal (draws W μ ρ r) else 0:= by
 let u:= (Fr); let g:= desk_mark ρ k; let P' i:=∏ j∈r.val,ρ j i; let v:=(Ψ (φ k)).part r; have he y : (Ψ (fun z=>g (z,y))).part r= if k=r.val.card then ↑(P' y) else 0:=by
    let f':= fun z:V→ℝ=> member ρ (z,y)^k; let f'':= ((k.factorial:ℝ)⁻¹) • f'; change (Ψ f'').part r=_; rw [Scatter.mul Fr pose _ (f:=f') (School.understands (school_spell ρ hρ k) y),show Ψ f'= _ from exact_power ρ hρ y k, Poly.part_smul, Comparison.Cumulants.lambda_power]; -- casts
    split; · push_cast; unfold P'; push_cast; rw [inv_mul_cancel_left₀ (show (k.factorial:ℂ)≠0 from Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
    rw [mul_zero]
 have hv (T:ℂ→L[ℝ]ℝ) : T v= Z (fun y=> T (if k=r.val.card then ↑(P' y) else 0)):= ((seeing W μ hW r T (f:=g) (school_ratio ρ hρ k)).1).trans (congr_arg (moment W μ) (funext fun y=>congr_arg _ (he y)))
 change v=_; by_cases h:k=r.val.card; · simp_rw [if_pos h] at hv ⊢; refine Complex.ext (hv Complex.reCLM) ?_; change Complex.imCLM v=0; rw [hv Complex.imCLM]; simp [Sage.moment]
 rw [if_neg h]; simp_rw [if_neg h,map_zero] at hv; apply Complex.ext; change Complex.reCLM v=0; rw [hv]; simp [Sage.moment]; change Complex.imCLM v=0; rw [hv]; simp [Sage.moment]
end YM.QuadraticLocal.Aperture.Sage
