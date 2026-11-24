import YM.FrontierTrace.Primary.Locus
/-!
Traceless meter Ward leading. `a • pole = K(1)-K(2)` (trace never used).
Cone path shapes from Wings. Supports no diagonal derivative estimates. Cross-projections
in extra weight not budgeted yet. Does not require `Paying`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.FrontierTrace.Primary
open Function Set Filter Analysis Trace Table Work.A01 Work.A05 Next.UVStress MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval Classical Matrix
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Spec.Final C f S)
    (ℓ:E4) {t:ℝ}
local notation "X"=> F.sector.turns
local notation "J"=> F.sector.energy
local notation "Ξ₀"=> firstProbe
local notation "Ξ₁"=> secondProbe

noncomputable def bis := Real.sqrt (1/2)
noncomputable def bisM : M4 := Matrix.of fun i j=> if i=j then if i=0 ∨ i=1 then bis else 1 else if i=0∧j=1 then -bis else if i=1 ∧ j=0 then bis else 0
local notation "Λ"=>bisM
lemma bis_pos :0<bis:=by unfold bis; positivity
lemma bis_mul :bis*bis=1/2:= by unfold bis; rw [← pow_two]; exact Real.sq_sqrt (by norm_num)
noncomputable def bisector : Ortho:= ⟨bisM,by rw [Matrix.mem_unitaryGroup_iff']; ext i j; fin_cases i <;> fin_cases j <;> simp +decide [bisM,Matrix.mul_apply,Fin.sum_univ_four,bis_mul] <;> norm_num⟩
local notation "g"=> bisector

variable {r:ℝ} (A : S.Field 4) {v:E4}
lemma pair_aim (hA : ∀ K, (X).act 4 K A=A) (B:S.Field 4) (K:Ortho)(x:Points 3)(hx:x∈conf 3):
    three A A ((X).act 4 K B) (Points.move K x)=three A A B x := by
    let tags : Fin 3→ S.Tag:= Fin.cons (α:=fun _:Fin 3=>S.Tag) ⟨4,B⟩ (fun _=>⟨4,A⟩)
    let t (B:S.Field 4) : Fin 3→ S.Tag:= Fin.cons (α:=fun _:Fin 3=>S.Tag) ⟨4,B⟩ (Fin.cons ⟨4,A⟩ (fun _=>⟨4,A⟩))
    have he : (X).label K ∘ t B=t ((X).act 4 K B):=funext fun i=>Fin.cases rfl (fun j=>by
       fin_cases j <;> change (Sigma.mk 4 ((X).act 4 K A):S.Tag)=⟨4,A⟩ <;> rw [hA]) i
    change S.useAt _ _ (t _)= _; rw [← he,F.phase.transport.motion _ (t B) x hx K]; rfl
lemma quarter_turn (x:Points 3)(hx:x∈conf 3)(m:ℝ)(hA : ∀ K, (X).act 4 K A=A):
    three A A (m • J 0 0) x - three A A (m • J 1 1) x =
       (2:ℝ) • three A A (m • J 0 1) (Points.move g x):=by
    let K:=g; have he:=pair_aim F A hA (m • J 0 1) g⁻¹ (Points.move g x) (Points.move_in g hx)
    have hK : Points.move g⁻¹ (Points.move g x)= x:=PiLp.ext (fun i=>Ortho.inv_move g (x i))
    rw [hK] at he
    rw [← he];
    have ht: (X).act 4 g⁻¹ (J 0 1)=(1/2:ℝ) • (J 0 0-J 1 1):=by
       rw [F.phase.transport.spin]; simp_rw [Maxwell.Free.inv_entry,show (g:Ortho).val=Λ from rfl,Fin.sum_univ_four];
       rw [F.phase.transport.conserved.symmetric 1 0]; simp +decide [bisM,bis_mul];
       rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; push_cast; module
    unfold three; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) m,map_smul,ht,← front_eval,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_sub]; push_cast; module
local notation "𝜏"=> three A A
local notation "I"=> priceAt r
abbrev Reads3:= Axis→Axis→Points 3→ℂ

def frontLat (r:ℝ) (K: Reads3) (v:E4) : ℂ:=
    (2:ℝ) • priceAt r (K 0 1 ∘ Points.move g) Ξ₀ 0 v
        + priceAt r (K 1 0) Ξ₀ 1 v+ priceAt r (K 2 0) Ξ₀ 2 v+ priceAt r (K 3 0) Ξ₀ 3 v
        + priceAt r (K 0 1) Ξ₁ 0 v+ priceAt r (K 2 1) Ξ₁ 2 v+ priceAt r (K 3 1) Ξ₁ 3 v
-- using only J0,J1 probe on all flux. Not a sign-flipping double translation term.
def construe (r:ℝ) (K:Reads3) := ∫ t:ℝ in 0..acrossRay ℓ,frontLat r K (slide ℓ t)
local notation "𝒳"=> frontLat r

lemma front_smul (K L:Reads3) (r:ℝ)(m:ℝ)(u:E4)(h:∀ i j:Axis,i≠j→K i j=m • L i j):
      frontLat r K u = m • frontLat r L u:=by
    unfold frontLat; rw [h 0 1 (by decide),h 1 0 (by decide),h 2 0 (by decide),h 3 0 (by decide),h 2 1 (by decide),h 3 1 (by decide)]
    rw [show (m • L 0 1) ∘ Points.move g=m • (L 0 1 ∘ Points.move g) from rfl]; simp_rw [price_linear]; module
lemma construe_smul (K L:Reads3)(r:ℝ)(m:ℝ)(h:∀ i j:Axis,i≠j→K i j=m • L i j) : construe ℓ r K=m • construe ℓ r L:=by simp_rw [construe,front_smul K L r m _ h,intervalIntegral.integral_smul]

def readA (r:ℝ) : Reads3 :=fun i j=> three A A (r^4 • J i j)
local notation "U"=> readA F A r

lemma front_ward (hr:0<r)(hv:1≤‖v‖)(hA:∀ K, (X).act 4 K A=A):
    𝒳 U v = (-r) • D (basis 0) (fun z=> custom (atShape z) A A) (r • v):=by
    have h1:=first_axis F A r hr hv; have h2:=second_axis F A r hr hv
    let u:=U 0 0; let l:= U 1 1; let k:= U 0 1 ∘ Points.move g
    have hu : I (u-l) Ξ₀ 0 v= (2:ℝ) • I k Ξ₀ 0 v:=by
       rw [← price_linear]; unfold priceAt; congr with z; dsimp only [Pi.sub_apply,Pi.smul_apply,k,comp_apply]; by_cases h: D (basis 0) Ξ₀ z = 0
       · rw [h, zero_smul, zero_smul]
       exact congr_arg _ (quarter_turn F A _ (smul_conf hr (wing_room3 hv (first_wing 0 (subset_tsupport _ h)))) (r^4) hA)
    have hInt(b:S.Field 4): ContinuousOn (three A A b) (conf 3):=(S.class_smooth S F.room.kernel.smooth _).continuousOn
    rw [price_sub _ _ (K:=u) (M:=l) (price_int r Ξ₀ hr hv (K:=u) (hInt _) first_smooth (first_wing 0)) (price_int r Ξ₀ hr hv (K:=l) (hInt _) first_smooth (first_wing 0))] at hu
    have hb : I l Ξ₁ 1 v = - I l Ξ₀ 0 v:=by simp_rw [priceAt, div0,neg_smul,integral_neg]
    unfold frontLat; rw [←h1, Fin.sum_univ_four]; change (2:ℝ) • I k Ξ₀ 0 v + _ + _ + _ + _ + _ + _ = I u Ξ₀ 0 v + I (U 1 0) Ξ₀ 1 v + I (U 2 0) Ξ₀ 2 v+ I (U 3 0) Ξ₀ 3 v
    rw [← hu]; rw [Fin.sum_univ_four] at h2
    change I (U 0 1) Ξ₁ 0 v+ I l Ξ₁ 1 v + I (U 2 1) Ξ₁ 2 v+ I (U 3 1) Ξ₁ 3 v=0 at h2
    rw [hb] at h2; linear_combination h2

local notation "Z"=> fun z=> custom (atShape z) A A
def slideK (r:ℝ)(t:ℝ):=custom (atShape (r • slide ℓ t)) A A
local notation "X0"=> slideK ℓ A r
include F
lemma read_axis {t:ℝ}(hr:0<r)(hℓ:Aimed ℓ)(ht:0≤t):
    HasDerivAt X0 (r • D (basis 0) (fun z=>custom (atShape z) A A) (r • slide ℓ t)) t:=by
    have hx: slide ℓ t≠0:=norm_pos_iff.mp (zero_lt_one.trans_le (hℓ.slide_norm _ ht))
    let v:=r • slide ℓ t
    have hZ : DifferentiableAt ℝ (fun z=>custom (atShape z) A A) v := (smooth_cons S F.room.kernel.smooth _ _ (atRoom (smul_ne_zero hr.ne' hx))).differentiableAt (by simp)
    have he : HasDerivAt (fun z=> r • slide ℓ z) (r • basis 0) t := by
       have h: HasDerivAt (slide ℓ) (basis 0) t:= by simpa only [slide,one_smul] using! (((hasDerivAt_id' t).smul_const (basis 0)).const_add ℓ)
       exact h.const_smul r
    have hk:= hZ.hasFDerivAt.comp_hasDerivAt t he
    rw [map_smul] at hk; exact hk
lemma pole_ward (hr:0<r)(hℓ:Aimed ℓ)(hA:∀ K, (X).act 4 K A=A):
    construe ℓ r U= YM.FrontierTrace.pure (C:=C) ℓ A r 1- YM.FrontierTrace.pure (C:=C) ℓ A r 2:=by
    let Zt:=fun v=>custom (atShape v) A A
    let s:= acrossRay ℓ
    have hs:= across_pos ℓ
    let y(t:ℝ):=r • D (basis 0) Zt (r • slide ℓ t)
    have hz {t:ℝ}(ht:t∈ [[0,s]]):0≤t:=by rw [uIcc_of_le hs.le] at ht; exact ht.1
    have hp : ContinuousOn y [[0,s]]:= fun t ht=> by
       have hv: slide ℓ t≠0:=norm_pos_iff.mp (zero_lt_one.trans_le (hℓ.slide_norm _ (hz ht)))
       have hH: ContinuousAt (D (basis 0) Zt) (r • slide ℓ t):=(dSmooth (n:=∞) (m:=∞) (f:=Zt) (smooth_cons _ F.room.kernel.smooth _ _ (atRoom (smul_ne_zero hr.ne' hv))) (basis 0) (by simp)).continuousAt
       exact ((hH.comp (f:=fun z=>r • slide ℓ z) (by unfold slide; fun_prop)).const_smul r).continuousWithinAt
    have hb := intervalIntegral.integral_eq_sub_of_hasDerivAt (f':=y) (fun x hx=> read_axis F ℓ A hr hℓ (hz hx)) hp.intervalIntegrable
    have hk : EqOn (fun t:ℝ=>𝒳 U (slide ℓ t)) (-y) [[0,s]]:= fun t ht=> (front_ward F A hr (hℓ.slide_norm t (hz ht)) hA).trans (neg_smul ..)
    have he1 : X0 0=YM.FrontierTrace.pure (C:=C) ℓ A r 1 := by simp only [slideK, YM.FrontierTrace.pure,slide,zero_smul,add_zero,mul_one]
    have he2 : X0 s= YM.FrontierTrace.pure (C:=C) ℓ A r 2:=by
       let w:= (2:ℝ)⁻¹ • slide ℓ s; have hw:‖w‖=1:= by unfold w; rw [norm_smul_of_nonneg (by norm_num : (0:ℝ)≤2⁻¹),across_length ℓ hℓ]; norm_num
       have hv:= custom_aim F A hA w hw (r*2) (by positivity)
       rw [mul_smul, smul_inv_smul₀ (two_ne_zero' ℝ)] at hv
       exact hv.trans (custom_aim F A hA ℓ hℓ.unit _ (by positivity)).symm
    change (∫ t:ℝ in 0..s, _) = _
    rw [intervalIntegral.integral_congr hk]; simp_rw [Pi.neg_apply]; rw [intervalIntegral.integral_neg,hb,he1,he2,neg_sub]
lemma measured (r:ℝ)(a:ℝ)(hr:0<r)(hℓ:Aimed ℓ)(hA:∀ K, (X).act 4 K A=A)(B: S.Stress)
    (hB : ∀ i j:Axis,i≠j → r ^ 4 • F.sector.energy i j=a • B i j) :
    a • construe ℓ r (fun i j=>three A A (B i j)) =
       YM.FrontierTrace.pure (C:=C) ℓ A r 1- YM.FrontierTrace.pure (C:=C) ℓ A r 2:=by
   rw [← pole_ward F ℓ A hr hℓ hA, construe_smul ℓ (readA F A r) (fun i j=> three A A (B i j)) r a (fun i j hij=> by unfold readA; rw [hB i j hij]; exact funext (fun z=> three_linear A ..))]
end YM.FrontierTrace.Primary
