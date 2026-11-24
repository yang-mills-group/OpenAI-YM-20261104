import YM.SchemeConversionRG11.FirstW.Ore.Tare
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck SchemeConversionRG11
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}{Q:Wash}{R:ℝ} {P:Age G} {W A B:ℕ→Field4 G}
lemma grows_sell (hc:MarkGrid T c)(hr:Q.rOut < R)(p:E F 6)(hp:Messed T (4*R) 4 W)(h: Deaf T ((closedBall 0 Q.rOut) \ {0}: Set E4) (-1) W)(ht:∀ k: Labels.Key G,Helen (fun i=>T.gap i ^(-2:ℤ)* native k (0:Cover) (A i))):
 Helen (fun i=> T.gap i^(-6:ℤ) • saleF T i Q p (W i) (A i)) := by
 simp only [saleF,burn_eq,Finset.smul_sum]; apply collectH; intro a _; apply collectH; intro b _; apply collectH; intro k _
 by_cases he:root3 (cloak F p) a b k=0; · exact ⟨0,by simp [he]⟩
 obtain ⟨_,hb,ha⟩:= top_six F p a b k he; obtain ⟨u,hu⟩:= ht k.val; obtain ⟨x,hx⟩:= bodym hc a b ha hb _ hr hp h
 refine ⟨_,((Complex.continuous_ofReal.continuousAt.tendsto.comp (hx.mul hu)).const_mul (root3 (cloak F p) a b k)).congr fun i=>?_⟩
 dsimp only [comp_apply]; rw [show (-6:ℤ)=(-4)+(-2) from rfl,zpow_add₀ (T.positive _).ne']; unfold native; simp only [Complex.real_smul, Complex.ofReal_mul]; ring
lemma subsist (hc:MarkGrid T c)(h:R>0)(p:E F 6)(hp:Messed T R 4 W) (Q:Wash) (ht:∀ i≤4,Book (P i)) : Tendsto (fun i=> T.gap i ^(-6:ℤ) • saleF T i Q p (composeR T 4 P i) (W i)) atTop (𝓝 0):= by
 let f (i:ℕ) a b k:= root3 (cloak F p) a b k*(↑(T.gap i ^(-6:ℤ)*sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) a b (composeR T 4 P i)*tape k.val 1 0 (W i)):ℂ)
 have hh (a b k): Tendsto (fun i=> f i a b k) atTop (𝓝 0) := by
   by_cases he : root3 (cloak F p) a b k=0; · simp [f,he]
   obtain ⟨_,hb,ha⟩:=top_six F p a b k he; have hx:= zero_poly (Q:=Q) hc a b ha hb ht; have hr:= (mess_tapes k.val h hp).sink hx
   have h':= (Complex.continuous_ofReal.continuousAt.tendsto.comp hr).const_mul (root3 (cloak F p) a b k); rw [Complex.ofReal_zero,mul_zero] at h'; apply h'.congr; intro i; dsimp only [comp_apply,f]; rw [smul_eq_mul]; unfold native; ring
 have hv (a b):= tendsto_finsetSum Finset.univ (fun k _=>hh a b k); simp_rw [Finset.sum_const_zero] at hv
 have hq a:= tendsto_finsetSum Finset.univ (fun b _=>hv a b); simp_rw [Finset.sum_const_zero] at hq
 have he:= tendsto_finsetSum Finset.univ (fun a _=>hq a); simp_rw [Finset.sum_const_zero] at he; apply he.congr; intro i; simp only [saleF,burn_eq,Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl;intro k _; unfold f; rw [Complex.real_smul]; push_cast; ring
-- matrix correction small on tails. Use finite const right. Book.s.
private lemma complex_budget (z:ℕ→ Pack F) (h:Level z) (L:Pack F→ₗ[ℝ] ℂ): Tendsto (fun i=> L (z i)) atTop (𝓝 0):= by
 have h1 : Tendsto (fun i=>(L (z i)).re) atTop (𝓝 ((0:ℂ).re)):= h (Complex.reCLM.toLinearMap ∘ₗ L)
 have h2: Tendsto (fun i=>(L (z i)).im) atTop (𝓝 ((0:ℂ).im)):= h (Complex.imCLM.toLinearMap ∘ₗ L)
 have he:= (Complex.continuous_ofReal.continuousAt.tendsto.comp h1).add ((Complex.continuous_ofReal.continuousAt.tendsto.comp h2).mul_const Complex.I); rw [Complex.re_add_im] at he; exact he.congr (fun i=>Complex.re_add_im _)
lemma BondW_fe (p:E F 6)(Z:ℕ→Pack F)(h:Level Z)(a b: Who G 6): Tendsto (fun i=> loot (cloak F ((Z i).val p)) a b) atTop (𝓝 0):= by
 let L:Pack F →ₗ[ℝ] ℂ:= {
    toFun z:= loot (cloak F (z.val p)) a b
    map_add' p q:= by simp only [loot,D1, ← robes_eq, Submodule.coe_add, LinearMap.add_apply,map_add,MvPolynomial.coeff_add]
    map_smul' c z:= by
       have ht: (c • z : Pack F).val p=(c:ℂ) • z.val p:=by rw [SetLike.val_smul,LinearMap.smul_apply]; exact RCLike.real_smul_eq_coe_smul (K:=ℂ) c _
       simp only [loot,ht,D1,←robes_eq,map_smul, Derivation.map_smul,MvPolynomial.coeff_smul, RingHom.id_apply, Complex.real_smul];rfl }
 exact complex_budget _ h L
private lemma tiny_mon (p:E F 6)(Z:Pack F)(c:ℝ)(a b:Who G 6): loot (cloak F ((c • Z : Pack F).val p)) a b=c • loot (cloak F (Z.val p)) a b:= by
 have ht: (c • Z : Pack F).val p=(c:ℂ) • Z.val p:=by rw [SetLike.val_smul,LinearMap.smul_apply]; exact RCLike.real_smul_eq_coe_smul (K:=ℂ) c _
 simp only [loot,ht,D1,←robes_eq,map_smul,Derivation.map_smul,MvPolynomial.coeff_smul, Complex.real_smul];rfl
private lemma sink_price {f:ℕ→ℝ}{u:ℕ→ℂ} (h:Honey f)(hp:Tendsto u atTop (𝓝 0)): Tendsto (fun i=> u i*(↑(f i):ℂ)) atTop (𝓝 0):=by
 obtain ⟨C,H⟩:=h; rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall (fun i=> norm_nonneg _)) (H.mono (fun i hi => show ‖u i*(↑(f i):ℂ)‖ ≤ ‖u i‖*C from ?_)) (by simpa only [norm_zero,zero_mul] using hp.norm.mul_const C)
 rw [norm_mul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
lemma matW (h:R>0)(p:E F 6)(Z:ℕ→Pack F)(hz:Level (fun i=> T.gap i • Z i))(hp:Messed T R 4 W)(hq:∀ k:Labels.Key G,Helen (fun i=>T.gap i ^(-2:ℤ)* native k (0:Cover) (A i))) : Tendsto (fun i=> T.gap i ^(-6:ℤ) • chord (W i) (A i) (Full.sections 6 F ((Z i).val p))) atTop (𝓝 0):=by
 let C i:= cloak F ((Z i).val p); let K(i:ℕ)(a b:Who G 6):= T.gap i ^(-6:ℤ) • ((1/2:ℂ)*loot (C i) a b*(↑(native a.val 0 (W i)*native b.val 0 (A i)):ℂ))
 have he(i:ℕ): Full.sections 6 F ((Z i).val p)=uncap (C i):= (stretch ..).symm
 have ht(i): chord (W i) (A i) (Full.sections 6 F ((Z i).val p))= ballot (taxes 6 0 1) (C i) (W i) (A i):= by rw [he,ballots (C i) (by rw [←he]; exact (suitsP _).sees p)]
 have hk(a b:Who G 6): Tendsto (fun i=> K i a b) atTop (𝓝 0) := by
    have ha := mess_tapes a.val h hp; obtain ⟨u,hu⟩:= hq b.val; have hc:= BondW_fe p _ hz a b; simp_rw [tiny_mon] at hc
    have he:= (sink_price ha hc).mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hu); simp only [zero_mul] at he; have H := (T.cutoff.smul he).const_mul (1/2:ℂ); rw [smul_zero,mul_zero] at H; apply H.congr; intro i; simp only [K,comp_def,C,Complex.real_smul]; unfold native; simp only [Complex.ofReal_mul]; have hp : (T.gap i:ℂ) ≠ 0:= Complex.ofReal_ne_zero.mpr (T.positive _).ne'; push_cast; field_simp
 have hq(a):= tendsto_finsetSum Finset.univ (fun b _=> hk a b); simp_rw [Finset.sum_const_zero] at hq
 simp_rw [ht,ball_val,Finset.smul_sum]; simpa only [taxes,LinearMap.pi_apply, Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun a _=> hq a)
end YM.RG11.FirstW
