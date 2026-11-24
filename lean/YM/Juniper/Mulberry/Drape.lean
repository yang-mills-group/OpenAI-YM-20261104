import YM.Juniper.Mulberry.Crow
/-!
 # Tags entering the Gaussian account, tilt arbitrary E valuation

 Bound Tilt just locally in **scaled** ordinary chart (g, y). Enough; use
 rr=L.Quarry Tendsto. Satisfying this is a producer obligation, not that
 tilt=0 on all shapes. Order-dependent width can be shopped if ≤g^-βeta
 for the fixed reported precision; here uniform brush up to polynomial
 and scale ∼beta^-ζ. Exact τ branch, normalization constants retained in
 the Gaussian. Huge compensation for choosing high orders will be possible in this radius.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern RG Wilson
open ConnectedActivityE6 Blaze Brush Poll Sienna
open Work.G05 WilsonStartup Analysis Tensor
open LocalAtlas
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {ι : Type}[Fintype ι][DecidableEq ι]
    {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {φ ψ : E × Poll.Body ι→ℝ}{ρ:E→ Poll.Body ι}{M : E→ Matrix ι ι ℝ}
    {k : ℕ}{D b p W t q : ℝ}
local notation "V" => ℝ × E
local notation "g" => grace φ ψ ρ M
local notation "K" => (M 0)⁻¹
local notation "A"=> std V q
local notation "Z"=> Poll.Body ι
local notation "Ω"=> closedBall (0:Z) D
local notation "v"=> b/q
local notation "u"=> LocalAtlas.turn (E:=E)

structure Tilt (k : ℕ)(r D q w:ℝ)(f:Poll.Body ι→ (ℝ×E)→ℝ):Prop where
   mass : ∀ y:(ℝ×E), ‖y‖ < r → ContinuousOn (fun z=> f z y) (closedBall (0:Poll.Body ι) D)
   wise (t:ℝ)(z:Poll.Body ι) (x:ℝ×E): f (t • z) x=f z (LocalAtlas.turn t x)
   flat (z:Poll.Body ι) : f z 0=0
   atmospheric : ∀ (z:Poll.Body ι)(x:ℝ×E), ‖x‖ < r → ‖z‖ ≤ D → Brush k w q⁻¹ (f z) x
-- supply natural scaled form via previous Pose. mass asks continuity in z only on CUT radius. For exp no taylor assumptions of support wrt y.
variable {f:Poll.Body ι→(ℝ×E)→ℝ}
      (H : Golf φ ψ ρ M k D b b p)(hs : Tilt k b D q W f) (hD:1 ≤ D) (hq:0<q)(ht:q≤1)
local notation "F"=> (Lantern.grace φ ψ ρ M + f)
local notation "L"=> foldR (F) q
include H hs hD
include hq ht
omit H hs hD ht [FiniteDimensional ℝ E] in
lemma torsion (x:ℝ×E) : ‖x‖ < b/q ↔ ‖A x‖ < b:= by rw [atBase, norm_smul,Real.norm_of_nonneg hq.le]; exact lt_div_iff₀ hq|>.trans (by rw [mul_comm]) -- order
omit hq ht [FiniteDimensional ℝ E] in
lemma zoom_nn : 0 ≤ W:=by have hv:‖(0:V)‖<b:= norm_zero.trans_lt H.pos; exact (hs.atmospheric 0 0 hv ((norm_zero.trans_le (by linarith)))).nonneg -- include H typo
local notation "w"=> fee k p D+ W

lemma sea (hc:v ≤ 1)(hS:(w)*v ≤ 1) : Paint Ω k L v w := by
   have hp:= H.pos; have hb:0 ≤ D:= zero_le_one.trans hD; have ht':= zoom_nn H hs hD; have hf : 0 ≤ fee k p D:= (Lantern.compel D H (x:=(0,(0:E))) (show ‖(0:E)‖ < b from norm_zero.trans_lt hp) (show ‖(0:ℝ)‖<b from norm_zero.trans_lt hp) (z:=0) (norm_zero.trans_le hb)).nonneg
   refine ⟨by positivity, fun x hx=>?_,hc,hS,fun z=>?_,fun z x hz hx=>?_⟩
   · have ht := (torsion hq x).1 hx; apply measurable_of_restrict_of_restrict_compl (s:=Ω) measurableSet_closedBall
     · let Q (z:Z):= F z (A x); have hh : ContinuousOn (fun z=> Real.exp (Q z)) Ω := by
          apply Real.continuous_exp.comp_continuousOn; exact ContinuousOn.add (Lantern.gallon D H ((norm_snd_le (A x)).trans_lt ht) ((norm_fst_le (A x)).trans_lt ht)) (hs.mass (A x) ht)
       rw [show (Ω).restrict (ballot L Ω x)= (Ω).restrict (fun z=>Real.exp (Q z)) from funext fun i=> Set.indicator_of_mem i.2 (fun z=>Real.exp (Q z))]; exact (continuousOn_iff_continuous_restrict.mp hh).measurable
     rw [show Ωᶜ.restrict (ballot L Ω x)= (fun _=>0) from funext fun i=> Set.indicator_of_notMem i.2 (fun z=>Real.exp (L z x))]; exact measurable_const
   · unfold foldR; rw [Function.comp_apply,map_zero,Pi.add_apply,Pi.add_apply, show (0:ℝ×E)=(0,0) from rfl,Lantern.zeroC,show f z (0,0)=0 from hs.flat z]; ring
   have hv := (torsion hq x).1 hx; have hZ:= mem_closedBall_zero_iff.mp hz; have hu:= leading _ hq ht (Lantern.compel D H ((norm_snd_le _).trans_lt hv) ((norm_fst_le _).trans_lt hv) hZ); have hf:= Brush.reading (A) (hs.atmospheric z (A x) hv hZ) ((Mulberry.dim V q).trans_eq (abs_of_pos hq)); rw [inv_mul_cancel₀ hq.ne'] at hf; exact hu.gathering hf

omit hD in
lemma scaledC {x:ℝ×E}(hx:‖x‖<b) (z:Poll.Body ι)(hz:‖z‖ ≤ D): Brush k w 1 (L z) (std (ℝ×E) q⁻¹ x):= by
   let x':= std (ℝ×E) q⁻¹ x; have hv : A x'=x:= smul_inv_smul₀ hq.ne' _; rw [← hv] at hx; have ht':= leading _ hq ht (Lantern.compel D H ((norm_snd_le _).trans_lt hx) ((norm_fst_le _).trans_lt hx) hz); have hs:= Brush.reading A (hs.atmospheric z (A x') hx hz) ((dim V q).trans_eq (abs_of_pos hq)); rw [inv_mul_cancel₀ hq.ne'] at hs; exact ht'.gathering hs

section lift
variable {x:ℝ×E}
def travelW (n:ℕ)(p D W:ℝ) := LocalAtlas.scaleFee n p D + W*2^n
local notation "X"=> LocalAtlas.turn (E:=E) t
local notation "w'"=> travelW k p D W

omit H hs hD ht hq
omit [FiniteDimensional ℝ E] in
lemma rising (x:ℝ×E): X (A x) = A (X x):= by rw [atBase,map_smul,atBase]
include H hs hD ht hq
lemma atmosphere (hx : ‖u t x‖<b/q)(hv:1 ≤ t) (z:Poll.Body ι)(hz:‖z‖ ≤ t): Brush k (t^(k+2)*w') 1 (L z) x:= by
    have h₀:=zero_lt_one.trans_le hv; let K':=t⁻¹ • z; have hk:‖K'‖ ≤ D:= by unfold K'; rw [norm_smul,norm_inv,Real.norm_of_nonneg h₀.le]; apply le_trans ((inv_mul_le_iff₀ (a:=1) h₀).2 ?_) hD; rw [mul_one]; exact hz -- arg b notation
    have hK:t • K'=z:= smul_inv_smul₀ h₀.ne' _; have hA : ‖X (A x)‖< b := by rw [rising (q:=q) (t:=t)]; exact (torsion hq _).1 hx -- drop
    have ht':= leading _ hq ht (LocalAtlas.abroad H hD t hv _ (⟨mem_ball_zero_iff.mpr ((norm_fst_le _).trans_lt hA),mem_ball_zero_iff.mpr ((norm_snd_le _).trans_lt hA)⟩) z hz); let ζ:= f K' ∘ A; have hY': Brush k W 1 ζ (X x):=by
       rw [rising (q:=q) (t:=t)] at hA; have h:= Brush.reading (A) (hs.atmospheric K' (A (X x)) hA hk) ((dim V q).trans_eq (abs_of_pos hq)); rwa [inv_mul_cancel₀ hq.ne'] at h
    have hζ:f z ∘ A=ζ ∘ X:=by funext i; nth_rw 1 [← hK]; change f (t • K') (A i)=_; rw [hs.wise, rising (q:=q) (t:=t)]; rfl
    refine ((ht'.gathering ((Brush.reading X hY' (LocalAtlas.spin t hv)).trim)).climb ?_ le_rfl).shimmy (by
       refine Eventually.of_forall fun i=>?_ ; exact congr_arg (fun y=> g z (A i)+y) (congr_fun hζ i))
    have h0:= hY'.nonneg; rw [travelW,mul_add]; apply add_le_add le_rfl
    rw [show t^(k+2)*(W*2^k)= t^2* (W*(2*t)^k) from (by rw [mul_pow,pow_add]; ring)]; apply le_trans ?_ (le_mul_of_one_le_left (by positivity) (by nlinarith only [hv])); exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [hv]) _) h0
lemma to_sky (z:Poll.Body ι): Brush k (w'*LocalAtlas.bill (k+2) z) 1 (L z) 0:= by
    rw [mul_comm]; exact atmosphere H hs hD hq ht (by rw [map_zero,norm_zero]; exact div_pos H.pos hq) (show 1≤1+‖z‖ from le_add_of_nonneg_right (norm_nonneg z)) z (le_add_of_nonneg_left zero_le_one)

omit ht in
lemma continuity (hx : ‖u t x‖< b/q)(ht':1 ≤ t) : ContinuousOn (fun z=> L z x) (closedBall (0:Poll.Body ι) t):= by
    let s:= closedBall (0:Z) t; let A':= std V q; let X':= LocalAtlas.turn (E:=E) t; have h₀:=zero_lt_one.trans_le ht'; let f':= fun z:Z=> t⁻¹ • z; have hz: ‖X' (A' x)‖< b:= by rw [show X' (A' x) = A' (X' x) from rising (q:=q) (t:=t) ..]; exact (torsion hq _).1 hx
    have hp: LocalAtlas.turn t (A x) ∈ cylinder b b E:= ⟨mem_ball_zero_iff.mpr ((norm_fst_le _).trans_lt hz),mem_ball_zero_iff.mpr ((norm_snd_le _).trans_lt hz)⟩; refine ContinuousOn.add (f:=fun z=> g z (A' x)) («g»:=fun z=> f z (A' x)) (LocalAtlas.outskirts H hD t ht' hp) ?_
    apply ((hs.mass (X (A x)) hz).comp (f:=f') (by unfold f'; fun_prop) (show MapsTo f' s Ω from ?_)).congr
    · exact fun z _=> by change f z (A x)= _; nth_rw 1 [← smul_inv_smul₀ h₀.ne' z]; exact hs.wise ..
    intro z he; change t⁻¹ • z∈ _; rw [mem_closedBall_zero_iff,norm_smul,norm_inv,Real.norm_of_nonneg h₀.le]; exact le_trans ((inv_mul_le_iff₀ (a:=1) h₀).2 ((mem_closedBall_zero_iff.mp he).trans_eq (mul_one _).symm)) hD

local notation "K'"=> Lantern.grace φ ψ ρ M
lemma evacuation (i:ℕ)(hi:i≤ k) : AEStronglyMeasurable (fun z=>Tensor.coeff (Real.exp ∘ L z) i 0) (sweep K):= by -- adapted LocalAtlas.transport_meas
   let G:=sweep K; let T (n:ℕ):= closedBall (0:Poll.Body ι) (n+1:ℝ); have he : (⋃ i:ℕ,T i)=univ:= eq_univ_of_forall fun x=>by obtain ⟨n,h⟩:= exists_nat_gt ‖x‖; exact Set.mem_iUnion.mpr ⟨n,mem_closedBall_zero_iff.mpr (by linarith : ‖x‖≤ n+ (1:ℝ))⟩
   refine AEStronglyMeasurable.const_smul (f:=fun z=> iteratedFDeriv ℝ i (Real.exp ∘ L z) 0) ?_ (i.factorial:ℝ)⁻¹; rw [← Measure.restrict_univ (μ:=sweep K),← he]; apply aestronglyMeasurable_iUnion_iff.mpr; intro n
   let t:=(n:ℝ)+1; let U:= (turn (E:=E) t)⁻¹' ball (0:ℝ×E) (b/q); let Q := L; let D':= T n; let S z y:=D'.indicator (fun z=> Real.exp (Q z y)) z; let P z:=iteratedFDeriv ℝ i (Real.exp ∘ L z) 0; have ht':1 ≤ t:= by unfold t; simp
   have hx : StronglyMeasurable fun z=> iteratedFDeriv ℝ i (S z) 0:=by
      refine Meristem.legs (j:=k) (S:=U) (isOpen_ball.preimage (turn t).continuous) (fun z y hy=>?_) (fun y hy=>?_) hi (show (0:ℝ×E)∈U from mem_preimage.mpr (by rw [map_zero]; exact mem_ball_self (div_pos H.pos hq)))
      · by_cases hh:z∈ D'; swap; · exact contDiffAt_const.congr_of_eventuallyEq (Eventually.of_forall fun y=> indicator_of_notMem hh _)
        exact (atmosphere H hs hD hq ht (mem_ball_zero_iff.mp (mem_preimage.mp hy)) ht' z (mem_closedBall_zero_iff.mp hh)).smooth.exp.congr_of_eventuallyEq (Eventually.of_forall fun y=> indicator_of_mem hh _)
      let W' := Real.exp ∘ (fun z=> L z y); let f z:=S z y; have he : Measurable f := by
           apply measurable_of_restrict_of_restrict_compl (s:=T n) measurableSet_closedBall
           · rw [show (T n).restrict f=(T n).restrict W' from funext fun i=> Set.indicator_of_mem i.2 W']; exact (continuousOn_iff_continuous_restrict.mp (Real.continuous_exp.comp_continuousOn (continuity H hs hD hq (x:=y) (mem_ball_zero_iff.mp (mem_preimage.mp hy)) ht'))).measurable
           rw [show (T n)ᶜ.restrict f = (fun _=>0) from funext fun i=> Set.indicator_of_notMem i.2 W']; exact measurable_const
      exact he.stronglyMeasurable
   refine (aestronglyMeasurable_indicator_iff (s:=T n) (f:=P) measurableSet_closedBall).mp ((show (fun z=>iteratedFDeriv ℝ i (S z) 0)= (T n).indicator P from ?_) ▸ hx.aestronglyMeasurable)
   funext z; by_cases hz:z∈T n; · rw [show S z=Real.exp ∘ Q z from (funext fun y=> indicator_of_mem hz _), indicator_of_mem hz]
   rw [show S z=0 from funext fun y=> indicator_of_notMem hz _, iteratedFDeriv_zero, indicator_of_notMem hz]; rfl
end lift
end YM.Juniper.Mulberry
