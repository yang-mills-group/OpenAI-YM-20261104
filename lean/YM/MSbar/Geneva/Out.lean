import YM.MSbar.Geneva.Brio
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{ι:Type}{X:ι→ℝ}{φ:Filter ι}[φ.NeBot](hX:Tendsto X φ atTop)
variable (P:Patch)(K:KernelChoices)(J:Voice G) (χ:ChartRatio G)
variable {α:ℝ}{n:ι→Side}(H H':Stage){s p m k:ℕ}{x:ℝ}
noncomputable def peep (G:Gauge)(n:Side):=Measuring.chart n G -- maybe omitted
lemma poison {n:Side}{P:Pot (Primary n G)}{R:Positions (Primary n G)}{a v D:ℝ}(hf:P.totalDegree ≤ k+1)(hp:Tokew (Measuring.chart n G) a p k 0 P D)(hz:0≤ a)(ht:‖R‖≤v): Roil (clue P) k a R (D*(1+v)^(k+1)):=by
     let E:=D*(1+v)^(k+1); have hv:= (norm_nonneg _).trans ht; refine ⟨(helm ..).contDiffAt,mul_nonneg hp.1 (by positivity),fun i L he=> ?_⟩
     let e:=pderiv i P; let a':= Measuring.chart n G; let I:= Whisk.extent (Whisk.zone a' ∅ (i::L)); have hh: Vault a' {a' i} a p L.length R e E:= Bout.across R (hp.2 i) hz (sub_zero R|>.symm ▸ ht) (pdeg _ hf) _
     have he : Whisk.zone a' ∅ (i::L)= Whisk.zone a' {a' i} L:=by ext x; simp [Whisk.zone]; -- signature
     unfold raiseQ; rw [CrossH.tours, read_next]; change |Whisk.read R L e|≤ E*Real.exp (-a*I); rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
     let p':=rate a' {a' i} a p R e; refine le_trans ?_ ((Lis.lit L p' (fun i=>mul_nonneg (wpos ..|>.le) (abs_nonneg _))).trans (hh.2 _ le_rfl)); unfold p' Whisk.rate; rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); unfold I; rw [he]; apply le_mul_of_one_le_left (Real.exp_pos _|>.le); apply one_le_pow₀; simp
variable {X0 f' g:ι→ℝ}{A:ι→Issue G} (hp:G.Simple)
variable (hK:∀ᶠ i in φ,Issue.Paid (A i) P H H' J (X i)) (hg:Clear G J)
variable (hk:p+2≤ m)(hh:k=m+1) (M:StageCost)(v:G.ColorIndex)(B:ℝ)
variable (hc:∀ᶠ i in φ,Festival (A i) χ p v ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) v (f' i) B ∧ Issue.Receipt (A i) M (X i))
variable (hD:∀ᶠ i in φ,k≤ (A i).post.p.order)(hf:Run φ X f' 0)
include hp hg hX hK hk hh hc hf hD K
lemma cold : ∃ a:ℝ, ∃ f:ι→ℝ, Run φ X f a∧∀ᶠ i in φ, 0≤ f i∧∀ z:Positions (Primary (A i).c G),‖z‖ ≤ hull (X i)→ Roil (Issue.preModel (A i) χ p) k (Alto.cWidth (X i)) z (f i):=by
    let Y:= fun i=>(A i).post; let X₀(i):=hull (X i); let X'(i):=tip G P.L (X i); have hh':Tendsto X' φ atTop:= (Work.E09.betaF_growth G P.L).comp hX; let f(i):=(A i).fClock; let ν(i):=Alto.cWidth (X i)
    obtain ⟨w,hA,hw⟩:=server hX χ J H H' P hp hK M v hc hk hf; have hS := hK.mono (fun i hv=>hv.payments.hull); have hv:= roundS hX J H H' P hp hK; have hW:= tails hX J H H' P hp hK
    have hh :∀ᶠ i in φ,0< f i∧ f i≤ 4*cue (X i):= by
          filter_upwards [ hW, cuff hh' (hW.mono fun i h=>h.1), hX.eventually_gt_atTop 1] with i hi he h; have hc:X i ≤ X' i:= le_add_of_nonneg_right (mul_nonneg (slopeConstant_pos hp).le (Real.log_nonneg (Nat.one_le_cast.mpr P.L.property))); have ht:0<cue (X i):= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans h)); have hk: cue (X' i) ≤ cue (X i):=inv_anti₀ (Real.sqrt_pos.mpr (zero_lt_one.trans h)) (Real.sqrt_le_sqrt hc); exact ⟨he,hi.1.2.trans ((mul_le_mul_of_nonneg_left hk zero_le_two).trans (by linarith only [ht]))⟩
    obtain ⟨q,a,hq,he⟩:= roar hX P K J H Y k hS hD hh hg
    let v(i):= w i*(1+X₀ i)^(k+1); let b(i):= ∑ j∈range (p+1),|f i^j| *v i; have hV : Run φ X v 0:= by let e:Run φ X X₀ 0:=((Run.stanza hX).mulY hX ((32:ℝ)⁻¹)).mulK hX 4; exact hA.Ymul hX ((Run.addR hX (Run.token hX _) e).Ypow hX (k+1))
    refine ⟨q,fun i=> a i+b i,hq.kick hX (Run.count hX (Finset.range (p+1)) (fun j i=> |f i^j| *v i) (fun j _=> Run.Ymul hX (Run.absA hX (Run.Ypow hX (Run.loosen ((Run.wander hX G hp ..).2 hv.1) (by norm_num)) _)) hV)) (Nat.cast_nonneg _),?_⟩
    filter_upwards [he,hc,hw,hS] with i he ⟨hQ,hP,hC,hV⟩ hW hz; have hw:0≤ X₀ i:=mul_nonneg zero_le_four (div_nonneg (sq_nonneg _) (by norm_num : (0:ℝ)≤32))
    let Z:= A i; let z:= Z.color χ; let g(j):= atlas z p j Z.post.path Z.post.clip; have hm(j)(hj:j≤p):Tokew (Measuring.chart Z.c G) (ν i) M.s k 0 (PowerSeries.coeff j (tariff Z.c p (Y i).clip (Y i).path z)) (w i):=by
         have hx:= hW j hj|>.2.2; refine CrossH.token _|>.mpr ⟨hx.1,fun i' h v=>?_⟩; by_cases hv:i'≤ m; exact ((CrossH.token _|>.mp hx).2 i' hv v); have ht:=Wave.cool Z.c p Z.post.clip Z.post.path z (hQ.postC.choose_spec.plane); have hp: (PowerSeries.coeff j (tariff Z.c p (Y i).clip (Y i).path z)).totalDegree≤ m+1 := by change (PowerSeries.coeff j (tariff Z.c p (Y i).clip (Y i).path z)).totalDegree≤ _; exact (ht.profile j hj).trans (by omega)
         rw [CrossH.whole _ hp _ (by omega)]; exact hx.1
    have hh'(x:Positions (Primary Z.c G))(hp:‖x‖≤ X₀ i): Roil (Issue.preModel (A i) χ p) k (ν i) x (a i+b i):=by
         let a':=ν i; have h0:0≤ a':=by unfold a' ν Alto.cWidth; positivity
         have hv(q)(hq:q≤p+1):Roil (fun y=> ∑ j∈range q,f i^j *g j y) k a' x (∑ j∈range q, |f i^j| *v i) :=by induction q with
              | zero=> simp_rw [Finset.range_zero,sum_empty]; exact Roil.still 0
              | succ q ih=> simp_rw [Finset.sum_range_succ]; exact (ih (by omega)).plus ((poison (by apply le_trans ((Wave.cool Z.c p Z.post.clip Z.post.path z hQ.postC.choose_spec.plane).profile q (by omega)); omega) (hm q (by omega)) h0 hp).scale (f i^q))
         have hh:= (Roil.plus (he x hp) (Roil.scale (hv _ le_rfl) (-1))); unfold preModel film; rw [sub_eq_add_neg,← neg_one_smul ℝ (ore (A i).post ((A i).color χ) _ p)]; apply Roil.mono hh; simp [b] -- syntax
    exact ⟨(hh' 0 (by rw [norm_zero]; exact hw)).2,hh'⟩
end YM.MSbar.Geneva
