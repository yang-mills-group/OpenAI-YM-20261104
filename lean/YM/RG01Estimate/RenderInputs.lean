import YM.RG01Estimate.Knot
/-!
# Actual interior rendering costs. Input packets, by their genuine unnormalised jets.

Does not prove ownership of these hypotheses by an arbitrary input representation. The
models must provide these analytic germ cost estimates (via real differentiation on the
propitious patches/forest) and valuation or factorization (the grades of the model!).
Only apply where unmasked. Usually use for one of finitely many formal powers aggregating
full path sums. Masks remain external, true-field aperture verified in Interior. These
bounds deal even with negative raw powers of the coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace.Layout
open Function Filter Set Metric MeasureTheory Finset Matrix
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush RealTaylor Office Courtyard Lapis
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {E F : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
    [NormedAddCommGroup F][NormedSpace ℝ F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "X" => ℝ × E
local notation "Z" => Poll.Body ι
variable (r : E→Poll.Body ι)(f:E× Poll.Body ι→ F) {b D R c C p v u : ℝ} {j k n:ℕ}

def waist (z:Z)(x:X):= visit r z 1 (rho x)
def form (z:Z)(x:X):= f (waist r z x)
-- Raw atlas before adding q-plugs. E(h,b,g) can also be ζ-depend analytic externally through finite polynomials; use finite-sum helpers.
structure Vertex (R U b C:ℝ)(j:ℕ) : Prop where
   port : ∀ x:ℝ × E, ‖x.2‖ < U → ‖x.1‖ < b → ∀ z:Poll.Body ι, ‖z‖≤R → Brush j C 1 f (visit r z 1 x)

-- typo v unused remove
local notation "W" => (ball (0:E) R)
section V
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable (h : Vertex r f D u v C j) (hc : ∀ x:E, ‖x‖ < u → Brush j p 1 r x)
    (hR:1≤R) (hv : v ≤ 1) (hu : u≤1) (he:b*R≤u) (hk:b≤v)

def rope (p D Y:ℝ)(j:ℕ):= clump j (expense j Y) (spanE p D)
include h hc hR hv hu he hk
omit [DecidableEq ι] [FiniteDimensional ℝ E]
lemma letter : Roll (form r f) (closedBall 0 D) W b (clump j (rope p D R j) C) j:= by
   let g z:= waist r z; let A:=closedBall (0:Z) D
   have hp (x:X)(hx : x∈ corridor b W): ‖(rho x).2‖ < u ∧ ‖(rho x).1‖<v:= ⟨(norm_snd_le (rho x)).trans_lt (((rho_mem x hR (mem_ball_zero_iff.mp hx.2)).trans_lt (mul_lt_mul_of_pos_right (mem_ball_zero_iff.mp hx.1) (zero_lt_one.trans_le hR))).trans_le he),(mem_ball_zero_iff.mp hx.1).trans_le hk⟩
   refine ⟨fun i hi x hx=> ?_,fun x hx=>?_⟩
   · obtain ⟨hX,hb⟩:=hp x hx
     let y:=rho x; have hy: ‖rho x‖ ≤ 1:= max_le (hb.le.trans hv) (hX.le.trans hu)
     have ht:= composite (travel_cap x (hb.le.trans hv) hR (mem_ball_zero_iff.mp hx.2).le)
          (camp r (show 1∈Set.Icc (0:ℝ) 1 by simp) hy (hc _ hX) (mem_closedBall_zero_iff.mp hi))
     exact composite (show Brush j (rope p D R j) 1 (g i) x from ht) (h.port (rho x) hX hb i (mem_closedBall_zero_iff.mp hi))
   have hc : Continuous (fun z=> waist r z x):= by unfold waist visit; fun_prop
   have he : ContinuousOn (fun z=> form r f z x) A:= fun i hi=> (((h.port (rho x) (hp x hx).1 (hp x hx).2 i (mem_closedBall_zero_iff.mp hi)).smooth.continuousAt).comp (f:=fun z=> waist r z x) hc.continuousAt).continuousWithinAt
   letI : MeasurableSpace F:= borel _; letI:= BorelSpace.mk (α:=F) rfl
   apply Measurable.stronglyMeasurable; apply measurable_of_restrict_of_restrict_compl (s:=A) measurableSet_closedBall
   · rw [show A.restrict (held _ (closedBall 0 D) x)=A.restrict (fun z=> form r f z x) from funext fun i=> indicator_of_mem i.property (fun z=> form r f z x)]; exact (continuousOn_iff_continuous_restrict.mp he).measurable
   rw [show Aᶜ.restrict (held (form r f) (closedBall 0 D) x)=(fun _=>0) from funext fun i=>indicator_of_notMem i.property (fun z=> form r f z x)]; exact measurable_const

omit he hk
lemma crown (hD : 0<D)(hC:0≤C)(hV:0<v)(hU:0<u): Atlas (form r f) W (1*j+0) j (clump j (rope p 1 R j) C):= by
    constructor; intro D' hD'
    let δ:=1+D'/D; let v':=v/δ; have hk : 1 ≤ δ:= le_add_of_nonneg_right (div_nonneg hD'.le hD.le); have h':0<δ:=zero_lt_one.trans_le hk
    have hv':0<v':=div_pos hV h'; have hK:v'≤ v:=div_le_self hV.le hk
    let b':=min v' (u/R); have hf:0<R:=zero_lt_one.trans_le hR; have Hb:0<b':= lt_min hv' (div_pos hU hf)
    have hp' : Vertex r f D' u v' C j := ⟨fun x h₁ h₂ z hz=> by
        let y:= δ⁻¹ • z; let x':X := (x.1*δ,x.2); have hb: D' ≤ δ*D:= by unfold δ; rw [add_mul,div_mul_cancel₀ D' hD.ne',one_mul]; linarith
        have he:=h.port x' h₁ (show ‖x.1*δ‖ < v by rw [norm_mul,Real.norm_of_nonneg h'.le]; exact (lt_div_iff₀ h').mp h₂) y
            (show ‖y‖≤ D by unfold y; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr h').le]; exact (inv_mul_le_iff₀ h').mpr (hz.trans hb))
        rw [show visit r y 1 x'=visit r z 1 x by unfold visit y x'; simp only [smul_smul,mul_assoc,mul_inv_cancel₀ h'.ne',mul_one] ] at he; exact he⟩
    have ha := letter r f hp' hc hR (hK.trans hv) hu (show b'*R≤u from (le_div_iff₀ hf).mp (min_le_right ..)) (show b'≤v' from min_le_left ..)
    refine ⟨b',Hb,ha.of_le ?_ le_rfl le_rfl⟩
    let t:= 1+D'; have ht : 1 ≤ t:=le_add_of_nonneg_right hD'.le
    have hP:0≤p:= (hc 0 (by simpa)).nonneg
    have hη : 0≤rope p D' R j:= by unfold rope clump expense spanE; positivity
    have hx:rope p D' R j ≤ rope p 1 R j * t^1:= by
        have hs : spanE p D' ≤ spanE p 1 * t^1:= by unfold t spanE; rw [pow_one]; nlinarith only [mul_nonneg hP hD'.le,hD',hP]
        have he:= clump_price (n:=j) ht (show expense j R ≤ expense j R*t^0 by simp) (show 0≤ expense j R by unfold expense; positivity) hs (show 0 ≤ spanE p D' by unfold spanE; positivity)
        rw [zero_mul,zero_add] at he; exact he
    exact clump_price ht hx hη (show C≤C*t^0 by simp) hC
end V
end YM.RG01Estimate.Laplace.Layout
