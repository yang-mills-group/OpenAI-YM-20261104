import YM.X.Bend.Manor
/-!
# operational tested λ values.LinkReal.F sensitivity negative.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Lattice Wilson Next.Rank Normal LiftMark Crate Porch Rays Shelf Tot Fund
open Maxwell Maxwell.Free Extra.FD MvPolynomial Labels Pert.Position Pert.RawLabels
open Interval Size Filter Function MeasureTheory Set Reed Stems Haze Fielding PertExtension LatticePT Chir Sage Bare Tri Pulse
open Ribbon
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m:ℕ} {q:ℕ+} {V I:Type*} {r R s:ℝ}
local notation "K"=>(atTop:Filter ℕ)
variable (B:Bare.Shop F) (hq:1<q.val)(hg:G.Simple)
local notation "X₁"=>firstX B q hq hg 6
local notation "xL"=> beaconLabels F (Nat.le_refl 6)
local notation "m₁"=> talent F (Nat.le_refl 6)
variable (s:ℝ)(hs:4096 ≤ s)(hx:Avoid q s)
local notation "v"=> mainT s hs
lemma integral_sight (F:Test m)(p:Points m→ℂ)(H:Integrable ((F:Points m→ℂ)*p))(hA:∀ x, (↑(F x).re:ℂ)=F x)(ht:∀ x,(F x).re≥0)(he:∃ x:Points m,F x=1)(h:∀ x∈tsupport (⇑F),(↑(p x).re:ℂ)= p x∧ (p x).re < 0):
     (↑(F.applyTo p).re:ℂ) = F.applyTo p ∧ (F.applyTo p).re<0:= by
       let g(x:Points m):=F x*p x; have hg:Integrable g:=H
       have hc(x) : (↑(g x).re:ℂ)= g x:= by
           by_cases hx' : F x = 0; · simp only [g,hx',zero_mul,Complex.zero_re,Complex.ofReal_zero]
           have he:= h x (subset_closure hx'); unfold g; rw [← hA x, ← he.1,←Complex.ofReal_mul,Complex.ofReal_re]
       have hs' : F.applyTo p=Complex.ofReal (∫ x, (g x).re):= by unfold Test.applyTo; rw [← integral_complex_ofReal]; exact integral_congr_ae (Eventually.of_forall fun i=>(hc _).symm)
       let f(x:Points m):= -(g x).re; have he1(x)(hx:F x≠0) : f x >0:= by
           have he:= h _ (subset_closure hx); have hy : (F x).re>0:= lt_of_le_of_ne (ht x) (fun H=>hx (by nth_rw 1 [← hA x]; rw [← H];rfl)); unfold f g; rw [← he.1]; rw [Complex.mul_re];simp; linarith [mul_neg_of_pos_of_neg hy he.2] -- simp might solve
       have h0 : Function.support f=Function.support F:= Set.ext (fun x=> by by_cases hh:F x=0<;> first| exact ⟨fun _=> hh, fun _=> (he1 x hh).ne'⟩ | simp [Function.mem_support,f,g,hh])
       have hp : 0< ∫ x, f x := (integral_pos_iff_support_of_nonneg (μ:=volume) (fun x=>show 0≤ f x from by by_cases hv:F x=0<;> first|exact (he1 x hv).le | simp [f,g,hv]) (show Integrable f from by exact (Complex.reCLM.integrable_comp hg).neg)).2 (by rw [h0]; obtain ⟨x,hx⟩:=he; refine F.continuous.isOpen_support.measure_pos volume ⟨x,show F x ≠0 from hx.trans_ne one_ne_zero⟩)
       rw [hs', Complex.ofReal_re]; refine ⟨rfl,?_⟩; unfold f at hp; rw [MeasureTheory.integral_neg] at hp; linarith
lemma unitSight (s:ℝ)(hs:4096 ≤ s)(hx:Avoid q s):
    ∃ c:ℝ,c<0 ∧ X₁ 3 (mainT s hs) (beaconLabels F (Nat.le_refl 6))= (c:ℂ):= by
      let t:=mainT s hs; obtain ⟨r,hr,u,H⟩:= prepare_v B hg t; obtain ⟨χ⟩:= Floor.make (R:=r/2) (by linarith); let K':= Aspect B hq hg χ (show r/2<r from by linarith); have he:r/2<r:= by linarith
      have h tX : tX∈ tsupport t → ↑(K' tX).re = (K' tX) ∧ (K' tX).re <0:= fun hz=> let ⟨h,u⟩:= limit_eye B hq hg χ he hs hx (show Curve t ⊆_ from u) hz; ⟨ Complex.conj_eq_iff_re.mp h,u⟩ -- tipe fix syntax
      have hl:= integral_sight t K' (inside B t (xAway B q χ) hq hg (fun p=> robust B χ p hq) (light_res B χ he hq) m₁ u|>.1) (fun x=>rfl) (eye_pos s _ hs) (eye_has s _ hs) h; let v':ℝ:= boostB*boostU*boostU; let c':= v'*(t.applyTo K').re; rw [price_eq]; rw [has_tip B hq hg χ he t H u]; refine ⟨c',mul_neg_of_pos_of_neg (show 0<v' from ?_) hl.2,?_⟩;
      · unfold v'; have hb:= beta_posible; have hh:= u_posible; positivity
      change _*t.applyTo K'= (↑(v' *(t.applyTo K').re):ℂ); rw [Complex.ofReal_mul v', hl.1] -- subtle rw t let
end YM.PositionX.Bend
