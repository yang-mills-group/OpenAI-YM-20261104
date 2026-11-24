import YM.MSbar.Mosaic.Roll
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{ι:Type}{X Tx:ι→ℝ}{φ:Filter ι}(hX:Tendsto X φ atTop)
variable (P:Patch)
lemma link {c: Side}(F:BudgetPoint)(v:ℝ)(J:Voice G)(h:Clear G J)(hv:v≤1)(hg: shade G*v ≤ J.r)(hy:J.C*(shade G*v) ≤ F.threshold/4): Bash (ball (0:Positions (Primary c G)) v) F:= by
      intro i hi; have hx:‖i‖ ≤ v := (mem_ball_zero_iff.mp hi).le; refine ⟨hx.trans hv,voids (r:=F.threshold) ?_ le_rfl⟩; intro b _; let x:= panel G c i b; have ht:‖x‖ ≤ shade G*v:= (pain i b).trans (mul_le_mul_of_nonneg_left hx (shade_pos G).le); let u:= palace i b; change G.chord _≤_; rw [show palace i b=G.lieExp x from ?_]; refine ((h.small _ (ht.trans hg)).2).trans ((mul_le_mul_of_nonneg_left ht (zero_le_one.trans h.cost)).trans hy); change G.lieExp x*1=_;rw [mul_one]
include hX
lemma music (p:ℕ)(c:ℝ): ∀ᶠ i in φ, c* hatW (X i)^p ≤ bbP (X i) :=by
    let f:=fun i=> Real.log (X i); have hh : Tendsto f φ atTop:= Real.tendsto_log_atTop.comp hX; let g(i):=hatW (X i)^p; have hx(i):g i=(f i)^(2*p):=by unfold g f hatW Alto.flurry; ring -- nat cast exponent
    have hb:Run φ f g (2*p:ℕ):=by
         have ht:= Run.core hh ((2*p:ℕ):ℝ); exact ht.alter (Eventually.of_forall (fun i=>by rw [hx]; exact Real.rpow_natCast ..))
    let x:ℝ:= (2*p:ℕ); have hP:= (hb.mulK hh c) (x+1) (by change x<_; linarith)
    have hp:Tendsto (fun i=> Real.log (f i)) φ atTop:=Real.tendsto_log_atTop.comp hh
    filter_upwards [hP,hp.eventually_ge_atTop (x+1),hh.eventually_gt_atTop 1] with i hi hX hx; refine (le_abs_self _).trans (hi.trans ?_); rw [Real.rpow_def_of_pos (zero_lt_one.trans hx)]; apply Real.exp_monotone; let a:= Real.log (f i); change a*(x+1)≤a^2; nlinarith only [mul_le_mul_of_nonneg_left hX (show 0 ≤ a from (Real.log_pos hx).le)]
-- cal widths. Ent aggregate.Near.*. Choose ball.X.
lemma melody (p':Patch)(K:KernelChoices)(G:Gauge) : Run φ X (fun i=> temp (X i)) (-(1/2))∧ Run φ X (fun i=>(temp (X i))⁻¹) (1/2) ∧ Run φ X (fun i=>bbP (X i)) 0∧ Run φ X (fun i=> ability (X i)) (-11/10):=by
     have hv: Run φ X (bbP ∘ X) 0:= fun a h=> (hX.eventually (microG G ⟨1,one_pos⟩ _ h)).mono (fun i he=> by change |bbP (X i)| ≤ (X i+G.slopeConstant*Real.log ((1:ℕ):ℝ))^a at he; change |bbP (X i)|≤ _; simpa using he)
     have hN : Run φ X (fun i=>(bbP (X i))⁻¹) 0:=by apply (Run.token hX 1).cash; refine Eventually.of_forall fun i=> ?_; have hc : 1≤bbP (X i):=Real.one_le_exp (sq_nonneg _); rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hc)),abs_one]; exact inv_le_one_of_one_le₀ hc
     simp_rw [temp_shape, _root_.mul_inv]; refine ⟨Run.Yrat hX (Run.waxing hX).1 hv,Run.Yrat hX (Run.waxing hX).2 hN,hv,?_⟩
     let s:Side:=⟨1,one_pos⟩; apply Run.alter (Run.core hX ((-11:ℝ)/10)); filter_upwards [hX.eventually_gt_atTop 0] with i hx; unfold ability cue; rw [Real.sqrt_eq_rpow,←Real.rpow_neg hx.le,←Real.rpow_mul hx.le]; congr 1; norm_num
variable (A:ι→BudgetPoint)(J:Voice G)(h:Clear G J)(c:ι→Side)
variable (he:∀ᶠ i in φ,(A i).threshold=temp (X i)) (hB:∀ᶠ i in φ,0<Tx i∧Tx i≤4*cue (X i))
local notation "u₀" i=> 2*Tx i*hull (X i)
include he hB h
lemma sizeF : ∀ᶠ i in φ,0<2*Tx i*hull (X i) ∧ (2*Tx i *hull (X i)) ≤1 ∧ Bash (ball (0:Positions (Primary (c i) G)) (2*Tx i*hull (X i))) (A i):=by
     let w(i):= u₀ i; have hb : Run φ X Tx (-(1/2)):= (Run.waxing hX|>.1.mulK hX 4).cash (hB.mono (fun i hi=>by rw [abs_of_pos hi.1];exact hi.2.trans (le_abs_self _)))
     have hc:Run φ X w (-(1/2)):= (hb.mulK hX _).Yrat hX (by exact ((Run.stanza hX).mulY hX ((32:ℝ)⁻¹)).mulK hX 4)
     have ht:=hc.bouquet hX (by norm_num); filter_upwards [he,hB,(Alto.broad.comp hX).eventually_gt_atTop 0,hX.eventually_gt_atTop 1,ht.eventually (ge_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)), (hc.mulK hX (shade G)|>.bouquet hX (by norm_num)).eventually (ge_mem_nhds h.depth),music hX 1 (4*J.C*shade G)] with i he hB hp hz ht hX H'
     have hW :0 ≤ hull (X i):=by unfold Mosaic.hull Mosaic.vol; positivity
     have hg:0 ≤ shade G:=(shade_pos _).le; have hi:=zero_le_one.trans h.cost; have hf:4*J.C*shade G*hatW (X i)≤ bbP (X i):=by simpa using H'
     have hk:0<cue (X i):=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hz))
     refine ⟨mul_pos (mul_pos zero_lt_two hB.1) (show 0 < hull (X i) from mul_pos (by norm_num) (div_pos hp (by norm_num))),ht, link _ _ J h ht hX ?_⟩; rw [he,temp_shape]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB.2 zero_le_two) hW) hg) hi) ?_; unfold Mosaic.hull Mosaic.vol; linarith only [mul_le_mul_of_nonneg_left hf hk.le]
end YM.MSbar.Geneva
