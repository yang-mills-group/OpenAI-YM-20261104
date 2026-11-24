import YM.SchemeConversionRG11.FirstW.Calx.BondM
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position SchemeConversionRG11 SchemeConversionRG11.Horizon Deck
open scoped BigOperators Classical ContDiff
variable {G:Gauge} {F:Labels.Frames G} {T:Itinerary} {n:Side} {c:ℕ→Side} {R:ℝ} {γ q : ℕ}
lemma tint_h (T:Itinerary)(a:Who G 6)(k: List Axis)(i : Axis) : Credit T R 0 (-((k.length+fee a+1:ℕ):ℤ)) (fun j x=> combine k (field4 i (tin G (T.period j) a)) x) := by
 obtain ⟨C,hC,H⟩:=tread a.val T i k; refine ⟨C,hC,?_⟩
 filter_upwards [H,entryM T R] with j hj h x hx; let N := T.period j; let l := k.length+fee a+1; let A:=canal a.val (0:Site N)
 have he (k:List Axis)(x:Cover): combine k (field4 i (tin G N a)) x= combine k (field4 i A) (wrap N x) := by
   induction k generalizing x with
   | nil=> unfold A; simp [combine,tin, terms,field4]
   | cons b k ih=>simp only [combine,up,ih,map_add,wrap_step]
 rw [he k x,zpow_zero,mul_one,zpow_neg,zpow_natCast,← div_eq_mul_inv, le_div_iff₀ (pow_pos (zero_lt_one.trans_le (unit_stepY _)) _)]
 have ht:=hj (wrap N x) 0; rw [sub_zero,show cy (wrap N x)=stepY x from congrArg stepY (h x hx)] at ht; rw [mul_comm]; unfold field4 A N fee; exact ht
lemma wheel_live (T:Itinerary)(a:Who G 6) (R:ℝ) : Scrip T R 0 (-((fee a+1:ℕ):ℤ)) (fun j=>tin G (T.period j) a):=by
 constructor
 · rintro s; simpa only [field4,combine,List.length_nil,zero_add] using tint_h (R:=R) T a [] s
 intro i s; convert tint_h (R:=R) T a [s] i using 1; rw [List.length_singleton]; omega
 rfl
lemma pol_live (T:Itinerary)(R:ℝ)(p : Field4 G)(h:p∈cabin G q) : Scrip T R 0 (q:ℤ) (fun _=>p) := by
 have hf(i:Axis): field4 i p∈ Loft _ q:= cabin_floor h i; constructor
 · rintro i; obtain ⟨C,hc,H⟩:=loft_scale q (hf i); refine ⟨C,hc,Eventually.of_forall fun j x hx=>?_⟩; rw [zpow_zero,mul_one,zpow_natCast]; exact H _
 intro i s; by_cases e:q=0
 · have hp(i:Axis)(x:Cover): up s (field4 i p) x=0 := by subst q; apply congrFun (hf i [s] (by simp)) x
   simp only [hp]; exact Credit.pure
 obtain ⟨w,rfl⟩:=Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero e)
 obtain ⟨C,hc,H⟩:=loft_scale w (loft_up (hf i) s); refine ⟨C,hc,Eventually.of_forall fun j x hx=>?_⟩; rw [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,zpow_zero,mul_one,zpow_natCast]; exact H _
-- integrable closure absolute
lemma tread_j (hc:MarkGrid T c)(a b: Who G 6)(ha:fee a=2)(hb:fee b=2)(p : Field4 G)(hp:p∈cabin G 3) (Q:Wash): Tendsto (fun i=> T.gap i * wheelS G T i Q (tin G (T.period i) a) (tin G (T.period i) b) p) atTop (𝓝 0) := by
 let R:=Q.rOut; let r:=R+1; let A i := tin G (T.period i) a; let B i:=tin G (T.period i) b; let f i x:=soft Q (Moss T i x)* ∑ u:Ticket,∑ w:Ticket,tower G x (icon (fresh u) (fresh w)) (A i) (B i) p
 have hA := wheel_live T a r; have hB:= wheel_live T b r; rw [ha] at hA; rw [hb] at hB
 have he(v w:Ticket): Credit T R 0 (-4) (fun i x=>tower G x (icon (fresh v) (fresh w)) (A i) (B i) p):= by
   have hr : R < r:= lt_add_one _; exact (show (-(((2+1:ℕ):ℕ):ℤ)) + (-(((2+1:ℕ):ℕ):ℤ)) + ((3:ℕ):ℤ)-1=(-4:ℤ) from by decide) ▸ roof_cap (fresh v) (fresh w) hA hB (pol_live T r p hp) hr -- first power a+a etc
 have hp : Credit T R 0 (-4) f:=by
   have h:=Credit.owed (T:=T) (s:=Finset.univ) fun u (_:u∈(Finset.univ (α:=Ticket)))=> Credit.owed Finset.univ (fun w _=>he u w); simpa only [f,zero_add] using! Credit.pays (soft_credit T Q R) h (ContinuousLinearMap.mul ℝ ℝ)
 let K:= fun (i:ℕ)(x:Cover)=> (T.gap i ^3)⁻¹ • f i x
 have hl:Lives T R f := Eventually.of_forall (fun i x hx=> by by_contra h; unfold f at hx; rw [soft_life Q _ (le_of_lt (lt_of_not_ge h)),zero_mul] at hx;exact hx rfl)
 have hd:= drop_far hp hl; have hK:Lives T R K := Eventually.mono hl (fun i hi x hx=> hi x (fun h=>hx (by simp [K,h])))
 have hc:= (mount (f:=K) (g:= (0:E4→ℝ)) hK hc hd.1 hd.2).2; simp only [Pi.zero_apply,integral_zero] at hc; apply hc.congr'; filter_upwards [stackV T R K hK] with i hi
 rw [show expenditure T K i=_ from hi,wash_eq]; simp only [K,smul_eq_mul,←Finset.mul_sum]; unfold f
 have h : T.gap i^4 * (T.gap i^3)⁻¹=T.gap i := by field_simp [(T.positive i).ne']
 rw [←mul_assoc,h]
lemma glow_small (hc:MarkGrid T c)(a b:Who G 6)(h:fee a=2)(hb:fee b=2)(Q:Wash)(p: Field4 G)(hp:p∈cabin G 3): Tendsto (fun i=> T.gap i * sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) a b p) atTop (𝓝 0):=by
 -- echo bounded from local report footprint
 obtain ⟨s,H⟩:= finite_glow (a.val)
 let f (i:ℕ)(t:↥s):= tin G (T.period i) b t.val
 have hh(t:↥s): ∃ C>0,∀ᶠ i in atTop, ‖f i t‖≤C:=by
    obtain ⟨C,hc,H⟩:= (wheel_live T b 1).1 t.val.2; have he:∀ᶠ i in atTop,Jam T 1 i t.val.1:= (Tendsto.norm (inc_const T t.val.1)).eventually (ge_mem_nhds (by simp)); have h0:= zero_lt_one.trans_le (unit_stepY t.val.1)
    refine ⟨C*(stepY t.val.1 ^ (-((fee b+1:ℕ):ℤ))),by positivity,(H.and he).mono fun i hi=>?_⟩; simpa only [zpow_zero,mul_one] using hi.1 _ hi.2
 have hz : Tendsto (fun i=> T.gap i • f i) atTop (𝓝 0) := by
   rw [tendsto_pi_nhds]; intro t; simp only [Pi.smul_apply,Pi.zero_apply]; obtain ⟨C,hc,H⟩:=hh t
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (H.mono fun i hi=>show _ ≤ T.gap i*C from ?_) (by simpa only [zero_mul] using T.cutoff.mul_const C)
   rw [norm_smul, Real.norm_of_nonneg (T.positive i).le]; exact mul_le_mul_of_nonneg_left hi (T.positive i).le
 let L : (s→G.Color)→ₗ[ℝ] ℝ := (echoAt 0 a.val).flip p ∘ₗ cle G s
 have hL(i:ℕ) : L (f i) = echoLeg 1 0 a.val (tin G (T.period i) b) p := by
   rw [echoLeg,one_pow,inv_one,one_smul]; exact H _ _ _ _ (fun t ht=>by simp only [cle,LinearMap.coe_mk,AddHom.coe_mk,clearWind,dif_pos (show t∈s from ht)]; rfl) (fun _ _=>rfl)
 have h1 := L.continuous_of_finiteDimensional.continuousAt.tendsto.comp hz; rw [map_zero] at h1; have h2:= (tread_j hc a b h hb p hp Q).const_mul 3 |>.add (h1.const_mul 2); simp only [mul_zero,add_zero] at h2; apply h2.congr; intro i; dsimp only [comp_apply]; rw [sector_eq,L.map_smul,hL]; simp only [smul_eq_mul]; ring
lemma clearL (p:E F 6) (q m:ℕ)(A B:la G)(hq:A.val∈cabin G q)(hm:B.val∈cabin G m) (e:q+m≤4)(hc:MarkGrid T c)(Q:Wash) : Tendsto (fun i=> T.gap i • saleF T i Q p A.val B.val) atTop (𝓝 0):= by
 by_cases h:m=0
 · subst m; obtain ⟨u,h,HU,hU⟩:= primitive _ 4 (cabin_stor B.property) (steady0 B hm); simp_rw [saleF,burn_eq,←HU,letter_T]; simp
 have hp : A.val∈cabin G 3:= stepped (by omega:q≤3) hq
 have ht (a b k:Who G 6): Tendsto (fun i=> T.gap i • (root3 (cloak F p) a b k * (↑(sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) a b A.val*tape k.val 1 0 B.val):ℂ))) atTop (𝓝 0):= by -- implicit n
   by_cases h:root3 (cloak F p) a b k=0; · simp [h]
   obtain ⟨hy,hb,hw⟩:=top_six F p a b k h
   have he:=(glow_small hc a b hw hb Q A.val hp).mul_const (tape k.val 1 0 B.val); rw [zero_mul] at he
   have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp he).const_mul (root3 (cloak F p) a b k); rw [Complex.ofReal_zero,mul_zero] at ht
   apply ht.congr; intro i; simp only [Complex.real_smul,comp_def,Complex.ofReal_mul]; ring
 simp only [saleF,burn_eq,Finset.smul_sum];
 have h (a b):=tendsto_finsetSum Finset.univ (fun k _=>ht a b k); simp only [Finset.sum_const_zero] at h
 have he (a):= tendsto_finsetSum Finset.univ (fun k _=>h a k); simp only [Finset.sum_const_zero] at he
 simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun a _=> he a)
lemma mom_paid (F:Labels.Frames G)(hc:MarkGrid T c)(Q:Wash): fitsM T (fun i=> bondM F T i Q) := fun q e=>by
 simp only [rate,LinearMap.coe_mk, AddHom.coe_mk, bond_paid,dew_val,← smul_mul_assoc] -- through slot
 have hv:= (clearL q.p _ _ q.a q.b q.e q.h e hc Q).add (clearL q.p _ _ q.b q.a q.h q.e (by omega) hc Q); rw [zero_add] at hv; have hz:=hv.const_mul (2:ℂ)⁻¹; rw [mul_zero] at hz; apply hz.congr; intro i; simp only [Complex.real_smul, mul_add]; ring
end YM.RG11.FirstW
