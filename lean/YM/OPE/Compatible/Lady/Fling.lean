import YM.OPE.Compatible.Lady.Echo
/-! # production under old inventory roofs. Lip sensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma.Chase
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P:Teller G} {D:Patch} {E:ConnectedActivityE6.Target G P} {L:Side} {W a σ C κ v γ t s w:ℝ} {m:ℕ}
variable {o:ConnectedActivityE6.Target.Order G W}
variable {ι:Type*} {l g:Filter ι} {A:ι→ Model D P L E o κ C m}
variable (h:Chase A l)
include h
lemma PathJ (n:ℕ): Lite A l (fun i=>billSp A n i/σW A i):=by
      let f:=echoM A; refine ⟨n+1,?_⟩; filter_upwards [h.echoes.eventually_ge_atTop 2,h.LimitSp,h.Dscale] with i hi he hx; let v:=f i; have hv:2≤ v:=hi; let a:=roofW A i; let b:=σW A i; obtain ⟨_,hh,hb,H⟩:= he; have hp:0<b:=hx.1; rw [H]; change ‖a*v^n/b‖ ≤ v^(n+1); have ht:0 ≤a:= hb.le; rw [Real.norm_of_nonneg (by positivity),div_le_iff₀ hp,pow_succ]; exact (mul_le_mul_of_nonneg_right (show a ≤ v*b from (by nlinarith only [show a/2≤ b from hh,mul_le_mul_of_nonneg_right hv hp.le])) (show 0 ≤ v^n from by positivity)).trans_eq (by ring)
lemma LeapJ (n:ℕ): RateIs l (fate A) (σW A) (-(1/2))∧ Wage A l (billSp A n) (-(1/2)) ∧∀ᶠ i in l,0<billSp A n i:=by
      let v:=billSp A n; have he : Wage A l v (-(1/2)):= ((h.PathJ n|>.sound h|>.mul (h.ζOpR.pays h.tense)).mono (le_of_eq (zero_add _))).congr (h.ζOpR.pos.mono fun i hi=>div_mul_cancel₀ _ hi.ne'); refine ⟨h.ζOpR,he,?_⟩; filter_upwards [h.LimitSp,h.echoes.eventually_gt_atTop 0] with i hi hx; rw [hi.2.2.2]; exact mul_pos hi.2.2.1 (pow_pos hx _)
lemma viv : ∀ᶠ i in l,‖fate A i‖≤ echoM A i :=by
       filter_upwards [h.tense.eventually_ge_atTop 2] with i hi; rw [Real.norm_of_nonneg (show 0≤ fate A i by linarith only[hi])]; let f:=fate A i; have hv:(radiusB (A i).x:ℝ)≥ 0:= Nat.cast_nonneg _; unfold echoM Delay.bill; change _ ≤ 1+ _+f^2; nlinarith only [hv,hi] -- terms order
omit h in lemma echo_I : Lite A l (fun i=>echoM A i):=⟨1, Eventually.of_forall fun _=> by rw [pow_one,Real.norm_of_nonneg (zero_le_one.trans (Delay.bill_ge ..))]⟩ -- include h unused
lemma hike {F:ι→ℝ}(hx:Lite A l F):∃ b:ℕ,∀ n:ℕ,b ≤ n→ ∀ q:ℝ,∀ᶠ i in l, q*fate A i +F i<billSp A n i/(2*σW A i):=by
       obtain ⟨j,hp⟩:=hx; refine ⟨j+4,fun n hh q=>?_⟩; filter_upwards [h.viv,h.LimitSp,h.echoes.eventually_gt_atTop (max 16 ‖q‖),hp,h.ζOpR.pos] with i hi hZ hg hk hI; let t:= echoM A i; have ht:16<t:=(le_max_left ..).trans_lt hg; have hu:1≤t:=(by linarith only[ht]); have hv : ‖q*fate A i‖≤ t^2:=(by rw [norm_mul,pow_two]; exact mul_le_mul ((le_max_right ..).trans hg.le) hi (norm_nonneg _) (by linarith only[ht]))
       let v:= σW A i; let u:= roofW A i; rw [lt_div_iff₀ (mul_pos zero_lt_two hI),hZ.2.2.2]; let x:=q*fate A i+F i; have he : 0<t^ (n-1):=(by positivity); have hh₀ : x≤ 2*t^ (n-1):=by
             have hh1 :=pow_le_pow_right₀ hu (show j≤n-1 by omega); have hp':= pow_le_pow_right₀ hu (show 2≤n-1 by omega); unfold x; linarith only [ (Real.le_norm_self _).trans hv|>.trans hp',(Real.le_norm_self _).trans hk|>.trans hh1]
       have hP:v≤2*u:=(by linarith only[show v/2≤u from hZ.1]); have hb:0<u:=hZ.2.2.1; calc
             _ ≤ (2*t^ (n-1))*(4*u):=mul_le_mul hh₀ (by linarith only[hP]) (mul_nonneg zero_le_two hI.le) (by positivity)
             _ = u*(t^ (n-1)*8):=by ring
             _ < u*(t^ (n-1)*t):=mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (by linarith only[ht]) he) hb
             _ = _:= by rw [←pow_succ, Nat.sub_add_cancel (by omega)]
lemma gain {F:ι→ℝ}(hp:Lite A l F):∃ n:ℕ,∀ᶠ i in l, σW A i*‖F i‖ ≤ billSp A n i:=by
       obtain ⟨d,hD⟩:=h.hike (F:=fun i=>‖F i‖) (hp.ofLe (Eventually.of_forall fun _=>norm_norm _|>.le)); refine ⟨d,?_⟩; filter_upwards [hD d le_rfl 0,h.Dscale] with i hi hx; rw [zero_mul,zero_add,lt_div_iff₀ (mul_pos zero_lt_two hx.1)] at hi; linarith only [hi,mul_nonneg (norm_nonneg (F i)) hx.1.le]
lemma brush {F:ι→ℝ}(hp:Lite A l F) :∀ᶠ i in l, σW A i*‖F i‖≤ (A i).R.p.threshold:=by
       obtain ⟨j,hh⟩:=h.gain hp; filter_upwards [hh,h.tins j,h.LimitSp,h.echoes.eventually_ge_atTop 0] with i hi hx hΓ hv; have ht :0 ≤ spillMass (G:=G) L j (A i).x:=(mul_nonneg hΓ.2.2.1.le (pow_nonneg hv j)).trans_eq (hΓ.2.2.2 j).symm; exact hi.trans (by change spillMass _ _ _≤_; linarith only[hx,ht]) -- may infer
end YM.PhysicalNext.Repeat.Aroma.Chase
