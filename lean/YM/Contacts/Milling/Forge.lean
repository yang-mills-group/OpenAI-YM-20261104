import YM.Contacts.Milling.Veneer
import YM.Branch.Covariant
import YM.Work.F04.Choices
/-! Uniform ray germ lift & actual local conditional Faces. Couplings positive. -/
noncomputable section
namespace YM.Contacts.Milling.Forge
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open PertExtension.GaussianScore FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Kale Spark House Radial Ion
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side} {S:StepData c f} {X E α:Type}{k r:ℕ}
local notation "T" => planting S.ratio S.patch.odd_side
local notation "κ" => (AxisChart G T)
local notation "Ξ" => insertion (plant T (G:=G))
local notation "Λ" => Link G f
local notation "Δ" => Link G c
local notation "Ω" => House.Dir (Yard G S)
-- Character through telescope horizons downward specific slot
structure Shaped (P:House α): Prop where
    poem i r : Poem (P i r)
    thin i r : (i=0∧ r≠2)∨i+2<r → P i r=0
def sealed (F:House (Lines G n 1))(k:ℕ) := ∀ i<k,Guards (wind F k i) (k-i)
structure Chest (F:House (Lines G n 1))(P:FreeResolvent.FaceRow): Prop extends Shaped F where
    glow x : design (F 0 2) x=x ⬝ᵥ (spindle G n P*ᵥ x)/2
structure Package (Y:ℝ→Config G n→ℝ)(F:House (Lines G n 1))(k:ℕ): Prop where
    legal t u s : Y t (pull s 0 u)= Y t u
    color t : GaugeInvariant (Y t)
    paid : Measurable (Function.uncurry Y)
    vest : AnalyticAt ℝ (fun p : cap G n=> Y p.1 (input G n p.2)) 0
    exact : Rays k ((fun p : cap G n=> Y p.1 (input G n p.2)) - swell F k)
def hand (F:House (Lines G n 1))(k:ℕ)(t:ℝ)(U:Config G n) := ∑ i∈Finset.range k, t^i * Kale.mirror (fire (wind F k i)) U
lemma candles (F:House (Lines G n 1))(k:ℕ)(h: sealed F k) : Package (hand F k) F k:= by
   let Φ i:= Kale.mirror (fire (wind F k i)); have he i (hi:i<k): Wedge (Φ i):=planted (h _ hi); let V i:= Φ i ∘ input G n
   refine ⟨fun t u s=> sum_congr rfl (fun i hi=> congr_arg (_*·) ((he i (mem_range.mp hi)).rounds ..)),fun t x u=>sum_congr rfl (fun i hi=>congr_arg (_*·) ((he i (mem_range.mp hi)).invariance x u)),?_ , stake_ana (F:=V) (fun i hi=>(he i hi).radiant),?_⟩
   · exact Finset.measurable_fun_sum _ fun i hi=> (measurable_fst.pow_const (by exact i)).mul (((he _ (mem_range.mp hi)).consent.measurable).comp measurable_snd)
   · change Rays k (Ion.stake V k - Ion.stake (wind F k) k); rw [show Ion.stake V k - Ion.stake (wind F k) k= Ion.stake (V-wind F k) k from (by ext1 x; simp [Ion.stake,conjunct, mul_sub,sum_sub_distrib])]; exact good_spaces (fun i hi=>(he i hi).radiant.sub ((h i hi).analytic)) fun i hi=> survives (h i hi)
variable {Y:ℝ→Config G f→ℝ}{F:House (Lines G f 1)}{P: FreeResolvent.FaceRow}
lemma theme (h:Chest F P)(u:cap G f)(hk:2<k): jet (swell F k) 2 u=u.2 ⬝ᵥ (spindle G f P*ᵥ u.2)/2:= by
  unfold swell Ion.stake; rw [loan_sum _ fun i hi=> conjunct_ana (wind_ana F k i 0) i,Finset.sum_eq_single 0, joint _ _ _ _ (wind_ana ..),if_pos (by decide),wind_jet, if_pos (by omega)]; · change u.1^0*_=_; rw [pow_zero,one_mul]; exact h.glow ..
  · intro i hi hp; rw [joint _ _ _ _ (wind_ana ..),wind_jet]; split
    next hx=> rw [if_pos (by omega),grate, show i+(2-i)=2 from by omega,if_pos le_rfl,h.thin _ _ (by omega)]; simp [design]
    rfl
  simp; omega -- maybe

def tribute (Q:ChartRatio G)(S:StepData c f)(Y:ℝ→Config G f→ℝ)(v:ℝ × House.Dir (Yard G S)):= Y v.1 (input G f (teen S v.2))+hot S v.2 -conjunct (gold Q) 2 v
lemma plan_m (hQ:Package Y F k)(h:S.patch.Branches S.kernel G)(u:ChartRatio G)(hs:LocalRatio u): Measurable (tribute u S Y):= by
   apply Measurable.sub
   refine Measurable.add (hQ.paid.comp (measurable_fst.prodMk ((input_cont (m:=f) (G:=G)).measurable.comp ((teen S).continuous.measurable.comp measurable_snd)))) ?_
   · simp_rw [hot_spec]; unfold noiseTaylor; apply Measurable.mul measurable_const (Finset.measurable_fun_sum _ (fun i _=>?_)); exact (show Continuous G.price by fun_prop).measurable.comp (Measurable.mul ((measurable_pi_apply i).comp ((input_cont (m:=c) (G:=G)).measurable.comp ((mature S).continuous.measurable.comp measurable_snd))) (((measurable_pi_apply i).comp ((S.prediction_meas h (art S)).comp ((input_cont (G:=G)).measurable.comp ((teen S).continuous.measurable.comp measurable_snd)))).inv)) -- continuous names
   exact (measurable_fst.pow_const (2:ℕ)).mul ((gold_meas hs).comp measurable_snd)
-- pars analytic
local notation "ν" => (ℝ × Ω)
def ace (S:StepData c f) : (ℝ × House.Dir (Yard G S)) →L[ℝ] cap G f := (ContinuousLinearMap.fst ℝ _ _).prod ((teen S).comp (ContinuousLinearMap.snd ℝ _ _))

lemma starts {X E:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup E][NormedSpace ℝ E](V:E→ℝ)(h:AnalyticAt ℝ V 0)(L:X→L[ℝ] E): AnalyticAt ℝ (V ∘ L) 0:= AnalyticAt.comp (by rw [map_zero]; exact h) (L.analyticAt _)
section
variable {Q:ChartRatio G}(hQ:Package Y F k)(h:S.patch.Branches S.kernel G)(hv:LocalRatio Q)
include hQ h hv
lemma tribute_ana : AnalyticAt ℝ (tribute Q S Y) 0:= ((starts _ hQ.vest (ace S)).add (starts _ (hot_ana h) (ContinuousLinearMap.snd ℝ ℝ _))).sub (conjunct_ana (gold_ana (S:=S) hv) 2)
lemma tribute_jet (r:ℕ)(hr:r<k)(x:ν) : jet (tribute Q S Y) r x=jet (swell F k) r (ace S x)+jet (hot S) r x.2 -if 2≤r then x.1^2*jet (gold Q) (r-2) x.2 else 0:= by
   let V : ν→ℝ := ((fun p:cap G f=> Y p.1 (input G f p.2)) ∘ ace S); let H := (hot S (G:=G)) ∘ (ContinuousLinearMap.snd ℝ ℝ Ω); have he : AnalyticAt ℝ V 0:= starts _ hQ.vest (ace S); have hy: AnalyticAt ℝ H 0:= starts _ (hot_ana h) _; change jet (V+H-conjunct (gold (S:=S) Q) 2) _ _=_; rw [jet_minus _ _ _ _ (he.add hy) (conjunct_ana (gold_ana hv) 2), serif he H hy, joint _ _ _ _ (gold_ana hv)]; congr 2
   · exact (woven hQ.vest _ _ _).trans (nightwalk hQ.vest (orchestra F k) hQ.exact _ hr _)
   exact woven (hot_ana h) _ _ _
lemma tribute_wanted (hk:1<k) : Radial.Stationary (tribute Q S Y):= by
   have he:=tribute_ana hQ h hv; have hs:= spectrum F k; have hp:= (torch_c (hot_ana h) (torch h)).1
   constructor
   · apply he.contDiffAt
   · have hz:= tribute_jet hQ h hv 0 (by omega) 0; simpa [hp.base0,hs.base0] using hz
   intro u; rw [tribute_jet hQ h hv 1 hk,hp.base1,hs.base1]; simp
lemma tribute_beams (hP:Chest F P)(hk:2<k)(x: ν) : jet (tribute Q S Y) 2 x=(teen S x.2) ⬝ᵥ (spindle G f P*ᵥ (teen S x.2))/2 + jet (hot S) 2 x.2:= by
   rw [tribute_jet hQ h hv 2 hk, theme hP _ hk,if_pos le_rfl,Nat.sub_self,jet_zero,gold_zero,mul_zero,sub_zero]; rfl
end
-- port station
local notation "ϕ" => (cap G c × κ)
def inked (S:StepData c f) : (cap G c × AxisChart G (planting S.ratio S.patch.odd_side)) →L[ℝ] (ℝ × House.Dir (Yard G S)) :=
 let F:= planting S.ratio S.patch.odd_side
 let L:= cap G c; let U:= AxisChart G F; let t:= ContinuousLinearMap.fst ℝ L U; let v:= ContinuousLinearMap.snd ℝ L U
 ((ContinuousLinearMap.fst ℝ ℝ (Link G c)).comp t).prod ((weave S).comp (((ContinuousLinearMap.snd ℝ ℝ (Link G c)).comp t).prod ((stash S F).comp v)))
lemma penPort (x:cap G c)(y:κ): inked S (x,y)=(x.1,weave S (x.2,stash S T y)):= rfl
-- full time Density with chart A equality
def visitor (S:StepData c f)(Y:ℝ→Config G f→ℝ)(t:ℝ)(U:Config G f)(V:Config G c):= (S.penaltyZ (t^2)⁻¹ G)^ Fintype.card (Edge (Site c)) * S.density (t^2)⁻¹ U V * Real.exp (-Y t U/t^2)
lemma ground_deduct (h:S.patch.Branches S.kernel G) : ∀ᶠ U:Config G f in 𝓝 1,∀ V:Config G c,∀ b:ℝ, (S.penaltyZ b G)^Fintype.card (Edge (Site c))*S.density b U V=Real.exp (-b*noiseTaylor S V U (art S)) := by
  filter_upwards [eventually_all.mpr (fun i:S.Choices=> Work.F04.prediction_germ h i (art S))] with U hi V b; unfold StepData.density; simp only [show ∀ i,S.prediction U i=S.prediction U (art S) from hi,←sum_mul, S.chosen h,one_mul]
  unfold StepData.noise StepData.penaltyWeight; let X:= noiseTaylor S V U (art S); have he:= S.penaltyZ_pos b (G:=G); simp only [Finset.prod_mul_distrib, Finset.prod_const,Finset.card_univ,← Real.exp_sum, inv_pow, ← mul_assoc,mul_inv_cancel₀ (pow_pos he _).ne',one_mul,← mul_sum]; rw [noiseTaylor]; congr 1; ring
section
variable {Q:ChartRatio G}(hQ:Package Y F k)(h:S.patch.Branches S.kernel G)
include hQ h
lemma seen : Sensor (visitor S Y) S.ratio:= ⟨fun i v U V=> by rw [visitor, S.covary h,hQ.color]; rfl,fun i u U V=> by rw [visitor,show pull u (0:Site f) U=pull u (S.ratio.embed 0) U from (by rw [show S.ratio.embed 0=0 from S.ratio.root.map_zero]), S.channel h]; rw [show S.ratio.embed 0=0 from S.ratio.root.map_zero,hQ.legal]; rfl⟩
lemma visit_meas (x:ℝ)(p:Config G c): Measurable (fun U:Config G f=> visitor S Y x U p) := by
   let t :ℝ:= (x^2)⁻¹; have hf: Measurable (fun U:Config G f=> S.density t U p):= by
        let L:= fun v:Config G f=>(v,p); let τ(z:Config G f × Config G c):= S.density t z.1 z.2; change Measurable (τ ∘ L); apply (show Measurable τ from S.density_meas h t).comp (f:=L); exact measurable_id.prodMk (measurable_const (a:=p))
   have hy: Measurable (Y x):= hQ.paid.comp ( (measurable_const (a:=x)).prodMk measurable_id)
   exact (hf.const_mul _).mul (hy.neg.div_const _|>.exp)
lemma foster (hv:LocalRatio Q): Faces Q (runner (visitor S Y) T) ((tribute Q S Y) ∘ inked S) (jacobian (U:=(T).Free) Q 0):= by
  have hx:= gold_jac_0 (S:=S) hv; let W:=visitor S Y; refine ⟨hx,fun ⟨x,p⟩=> ?_,?_ ⟩
  · exact (visit_meas hQ h x (input G c p)).comp (Forest.continuous_drape T (G:=G)).measurable
  have he : Tendsto (fun p:ϕ=> input G f (stash S T p.2)) (𝓝 0) (𝓝 1):= by simpa using! (input_cont.comp ((stash S T).continuous.comp continuous_snd)).tendsto (0:ϕ)
  filter_upwards [he.eventually (ground_deduct h), (show Tendsto (fun p:ϕ=>p.2) (𝓝 0) (𝓝 0) from continuous_snd.continuousAt ).eventually (gold_chart (S:=S) hv)] with z hϕ hxg (ht:0< z.1.1)
  let t:= z.1.1; let b:= z.1.2; let y:=z.2; let p:= weave S (b,stash S T y); let U:=input G f (stash S T y); let V:= input G c b; let X:=jacobian Q y; let A:= jacobian Q (0:κ);
  have hk : (visitor S Y t U V)=Real.exp (-Y t U/t^2 - hot S p/t^2) := by
    unfold visitor; rw [hϕ V,←Real.exp_add]; congr 1; rw [hot_spec,(show mature S p=b from grow _),(show teen S p=stash S T y from blooms _)]; unfold V U; ring
  change X* W t ((T).drape _) V= _; rw [←stash_drape]; change X*visitor S Y t U V=A*Real.exp (-tribute Q S Y (inked S z)/t^2); rw [hk]; -- expose
  let J:=Y t U+hot S p-t^2*gold Q p; rw [show tribute Q S Y (inked S z)= J from ?_]; swap; · rw [show inked S z=_ from penPort z.1 z.2]; change Y t (input G f (teen S p)) + _-_ = _; rw [show teen S p=_ from blooms _]; rfl
  calc
    _ = (A*Real.exp (gold Q p))*Real.exp (-Y t U/t^2 - hot S p/t^2):= by rw [show Real.exp (gold Q p)=X/A from hxg b]; field_simp [(show A≠0 from hx.ne')]
    _ = _:= by rw [mul_assoc, ← Real.exp_add]; unfold J; change A*_=A*Real.exp (-(_-t^2* _)/t^2); congr 2; field_simp [(show t≠0 from ht.ne')]; ring
end
end YM.Contacts.Milling.Forge
