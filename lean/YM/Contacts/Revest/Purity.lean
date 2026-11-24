import YM.Contacts.Revest.Flute
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
/-! # Assemble & certify hybrid output against the calendar.
 No reparametrize across trials. Auth **at actual Input rep**. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Revest
open AnalyticBridge VerifiedReset Collection
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {η C s t q v:ℝ}
namespace Purity
section fiat
variable {n:Side} {p:BudgetPoint} {X:Pipes G n} {d:Tap G n}
lemma arrest (h:Ingredients X d p s t)(R:PathData G)(c:Clip)(β τ:ℝ):
  let T:= finish R c p X d β τ
  T.eval 1= Real.exp (τ * Fintype.card (Site n)):=by
     intro T
     let Y : Template G n:=⟨R,c,p,fun _ _=> T.activities⟩; let V : ℝ→ℝ:= fun _=>0; have he:((Y).trial V 0 β τ)=T:= by unfold Template.trial Y V; simp only [zero_add]; rfl
     exact congr_arg (fun i:Rep G n=> i.eval 1) he.symm |>.trans ((Y).trial_one V (x:=0) (h.gates R c β τ).regular.at_flat)
lemma unshifted (h:Ingredients X d p s t)(R:PathData G)(c:Clip)(β τ:ℝ)(V:Config G n):
  let T:= finish R c p X d β τ
  (Progress.DirectedRecipe.trunk R c p X d β 0).eval V * Real.exp (∑' i, d.logarithm i V)= T.eval V/T.eval 1 := by
    intro T; dsimp only [T]; rw [arrest h,h.exact_eval R c β τ V]; field_simp
lemma pace {f g:Trio.Offer G n} (U:Config G n): Flute.film p (f-g) U + Flute.film p g U=Flute.film p f U:= by
  unfold Flute.film; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; unfold masked Set.indicator; split_ifs <;> simp
end fiat
variable {Z:Metals G}{D:Rolls Z.p}{B:Alloy Z D}(A:Factor B) {m n N:ℕ}
local notation "Y" => B.B.a
local notation "ω" => quoteHard Y m A.book
set_option quotPrecheck false
local notation "γS" => (Y).clock.allowance m
local notation "R" => B.B.kin.path N m
local notation "α₀" => B.B.kin.alpha N m
local notation "p" => ((Y).budget m)
local notation "S" => ((Y).S.side m n)
local notation "σ" => ((Y).params m)
local notation "c" => (σ).clip

variable {T:Rep G (B.B.a.S.side (m+1) n)}
local notation "β" => T.beta
-- generic payment invoice. not require Honors if cost extra.
section standby
variable {X:Pipes G (B.B.a.S.side m n)} {w:Tap G ((B.B.a.S.side m n))} (hm:m<N) (hf: T.beta∈ band B.B.a (m+1)) (h:Ingredients X w (B.B.a.budget m) s ((quoteHard B.B.a m A.book) T.beta))
    (hV: Lives B.B.bake N (m+1) n T) (H : (finish (B.B.kin.path N m) (B.B.a.params m).clip (B.B.a.budget m) X w t v).eval = (B.B.a.clock.op m n).push T.beta T.eval) (hv: |t-T.beta-(B.B.kin.alpha N m)|≤1)
local notation "P" => (finish R c p X w t v)
-- no forced allowance oracle; needed launch separately due to fraction. recovered for padding.
include A hm h hf hV hv H
lemma pours (hγ:((P).activities.Valid p γS ((Y).clock.forcedAllowance m)) ∧ (P).activities.KBound p (Return.forcing B.B m)) (hc:s≤ Echarge A.exchange A.book Y m β)(ha:(p).threshold^2*|t-β-α₀| ≤ portion A.exchange A.book Y m β):
      B.B.Move N m n (P) T:= by
  let z:=t-β-α₀; have he: β+α₀+z=t:=by unfold z; ring
  have hv': flatRate Y m n T=v:= by
     rw [flatRate,← H, arrest h,Real.log_exp]; exact mul_div_cancel_right₀ v (sites_pos _).ne'
  let F: ℝ →ℝ:=fun _=>portion A.exchange A.book Y m β; let X':ℝ→Rep G _:=fun _=>T
  have hk:= Use.respects (B:=B.B) A.machine.ready hm (l:= Set.univ) (Q:=X') (H:=F) («δ»:=fun _=>s) (γ:=fun _=>ω β) (fun y _=>⟨le_rfl,hc,quoteHard_le ..⟩) 0 (Set.mem_univ _) hV hf z X w
  change predictor B.B N X' 0 + z=t at he
  dsimp only at hk
  rw [he,show X' 0=T from rfl,hv'] at hk -- beware predictor changed first
  have hh:=hk h ha (fun U=> ?_); swap
  · change _=((Y).clock.op m n).push β T.eval U / ((Y).clock.op m n).push β T.eval 1; rw [← H]; exact unshifted h R c t v U
  exact ⟨H,hh.2,⟨B.B.bases ▸ rfl,rfl,rfl,⟨B.B.support.cap _ _ hm.le,hγ.1⟩,hh.1⟩,hγ.2,hv⟩
lemma pure (hP:s≤Time.fraction Y m)(ha:(p).threshold^2* |t-β-α₀| ≤ forecastE Y m): B.B.Move N m n (P) T:= by
  have he:∀ x ∈ (Set.univ:Set ℝ), Lives B.B.bake N (m+1) n ((fun _=>T) x) ∧ ((fun _=>T) x).beta∈band Y (m+1):= fun _ _=>⟨hV,hf⟩
  obtain ⟨hC,-⟩:= A.machine.passes hm he
  have hc₀ := A.machine.coverage _ _ (Push.PriceCompiler.step_paid (Y) m); have hh:= Time.now (Q:=fun _=>T) B.B hm A.machine.shops hc₀.1 (by rw [Push.PriceCompiler.params_eq B.B.valid]; exact hc₀.2) A.exchange A.machine.cubic (fun (x:ℝ)(hx:x∈(Set.univ:Set ℝ))=>hf)|>.2 0 (Set.mem_univ _)
  exact pours A hm hf h hV H hv (hC.closes 0 (Set.mem_univ _) _ ((Use.compatible_ingredients h hP le_rfl).gates R c t v)) (hP.trans hh.2) (ha.trans hh.1)
end standby
variable {X:Listing G ((B.B.a.S.side m n))} {w:Collection.Source G ((B.B.a.S.side m n))}

local notation "β₀" => β+ q -- tilt q
local notation "Δ" => delta (X.read w)
variable (g:G.Simple) (hm:m<N) (hp:Lives B.B.bake N (m+1) n T)(hf: T.beta∈ band B.B.a (m+1))
    (L:Local X (B.B.a.budget m) w s (forecastK B.B.a m A.scout T.beta))
    {F F':Trio.Offer G ((B.B.a.S.side m n))} (hF:Flute.Salary (B.B.a.budget m) (F-F') v) (hF':Flute.Salary (B.B.a.budget m) F' η)
    (H:∀ V, earlyValue X (B.B.kin.path N m) (B.B.a.params m).clip (B.B.a.budget m) w ((T.beta+ q)) t 0 V * Real.exp (layer (fun d : Low => d.loan (B.B.kin.path N m) (B.B.a.params m).clip 0 (B.B.a.budget m) q 0) V) * Real.exp (-Flute.film (B.B.a.budget m) F V)= (B.B.a.clock.op m n).push T.beta T.eval V)
local notation "K" => shelves X R p
local notation "D₀" => Hybrid.pliant X R c p w q
local notation "δ" => regularNeed G p c (σ).width (σ).paths 0 s
variable (hK : ∃ z κ, softNeed G (B.B.a.budget m) (B.B.a.params m).clip (((B.B.a.params m))).width (((B.B.a.params m))).paths q s ≤ z∧Payments.Rates ((B.B.a.budget m)).B ((quoteHard B.B.a m A.book) T.beta) (forecastK B.B.a m A.scout T.beta) z κ)
    (hE : η+(v+(regularNeed G (B.B.a.budget m) (B.B.a.params m).clip (((B.B.a.params m))).width (((B.B.a.params m))).paths 0 s)) ≤ Time.fraction B.B.a m)
local notation "W" => Flute.put (Flute.put K p) p
local notation "V" => finish R c p W (Flute.lay F' (Flute.lay (F-F') D₀)) (β+q+Δ) (vac w t)
include g A hm hp hf hF hF' H hK L
/-- The emitted E keys after reclosure reserve one commissioned copy at every anchor. Complement coat uses relative beta variance and the residual budget already secured. Does not restart at real path here. -/
lemma prizes (hx: |β+q+Δ-β-α₀| ≤1)(hr:(p).threshold^2*|q+Δ-α₀| ≤ forecastE Y m) (hE : η+(v+δ) ≤ Time.fraction Y m):
  B.B.Move N m n (V) T ∧ (p).threshold^2* |(V).beta-(β₀)| ≤ s ∧ ∃ k:Poetry.Lecturer (V) (p).B, Toll (V) (Poetry.unknown k) (η+(v+δ)) (v+δ) ∧ ∀ x,(V).activities.E (k.place x)=F' x := by
   obtain ⟨he,-⟩:= A.machine.passes hm (Q:=fun _=>T) (l:=Set.univ) (fun _ _=> ⟨hp,hf⟩); let Q':= D₀; let T':= β+q+Δ; let v':=vac w t; let K':= (K); let w':= Flute.put K' p; let y:= Flute.lay (F-F') D₀
   have hW:=Return.enough_room B.B m n; have hz:=Hybrid.fund g hW L (B.B.support.cap _ _ hm.le) he.decent he.width q hK; have h :=Flute.height hF hz; have hu:= Flute.height hF' h
   have hsum: (V).eval= ((Y).clock.op m n).push β T.eval:= by
       funext U; rw [hu.unshifted, Flute.covers h,Flute.covers hz,← H U, ← Hybrid.engine g hW L (B.B.support.cap _ _ hm.le) he.decent he.width, ← pace («p»:=p) (f:=F) (g:=F') U,neg_add_rev,Real.exp_add]; change _ * Real.exp (∑' i,Q'.logarithm i U)= _; ring
   have hΔ : (p).threshold^2 *|(V).beta-(β₀)| ≤ s:=by rw [show (V).beta - (β₀)=Δ from (by change _+q+Δ-_=_; ring)]; exact delta_bound g L.projects
   exact ⟨Purity.pure A hm hf hu hp hsum hx hE ((congr_arg (fun z:ℝ=>(p).threshold^2*|z|) (show _-β-_=q+Δ-α₀ from (by ring))).le.trans hr), hΔ, Flute.solo R c p w' y F' T' v',Flute.trumpet R c p w' y F' hF' T' v' h, Flute.lights R c p w' y F' T' v'⟩
end Purity
end YM.Contacts.Revest
