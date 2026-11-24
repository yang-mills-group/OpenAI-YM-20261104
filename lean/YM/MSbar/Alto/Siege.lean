import YM.MSbar.Bronze.Finish
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F:Forest S.ratio)
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "ℓ"=>Measuring.chart n G
local notation "T"=>Measuring.chart c G
local notation "L"=>(S.ratio.count.val:ℝ)
local notation "μ"=> PowerSeries.coeff
noncomputable def purse (E:ℕ→ℕ)(w:ℝ)(r:ℕ):= w^(E r)
structure Wedge (f:Nesting G n)(E:ℕ→ℕ)(w:ℝ)(a:ℝ)(p q:ℕ): Prop where
    shares (r:ℕ)(he:r≤q): Tin (Measuring.chart n G) a p (r+1) w (PowerSeries.coeff r f) (purse E w r)
variable (E:ℕ→ℕ) (hv:Monotone E)
-- charges for frame costs
structure Fees where
    pre : ℝ
    tilt : ℝ
    shape : ℝ
    axis : ℕ
    bc : ℝ
    bf : ℝ
    c1 : ℝ
    c2 : ℝ
    c3 : ℝ
    c4 : ℝ
    farms : ℝ
noncomputable def Fees.coin (V:Fees)(G:Gauge)(g:Side)(w:ℝ)(p r:ℕ)(a Ξ A:ℝ):= chem G a V.shape V.pre V.tilt r V.axis p g V.c1 V.c2 V.c3 V.c4 w Ξ A V.farms
noncomputable def Fees.lead (V:Fees)(E:ℕ→ℕ)(w:ℝ)(r:ℕ):= purse E w (r-1)+(1+V.bf)*w^2
structure Ready (V:Fees)(G:Gauge)(E:ℕ→ℕ)(g:Side)(n p:ℕ)(s v w:ℝ): Prop where
   axis : 3 ≤ V.axis
   grade: 6≤ n
   wise :1≤ v ∧ v≤ w
   s0 :0≤V.bc∧0≤ V.bf
   prize (r:ℕ)(h:0<r)(hp:r≤p) :
       let Z:= V.coin G g w n r s (purse E w r) (V.lead E w r)
       let C:=purse E w (r-1); let D:=Z+salary r C C
       Z ≤ purse E v r∧ D*(1+V.bc) ≤ purse E v r ∧ D/w^2 + Bronze.straw C r≤ purse E v r
noncomputable def fuelTest (F:Forest S.ratio)(t:S.Choices)(J:ChartRatio G) := splitV (singularity (swung F J) 0)-splitV (singularity (pushChart F G t) 2)
structure SceneB (V:Fees)(F:Forest S.ratio)(τ:S.Choices) (P:Cross S.ratio.count (TypeFace 1) (TypeFace 1))(J:ChartRatio G) (ρ:fieldDir G c 1→ AxisChart G F) (R:PathData G)(l:Clip)(H:PathData G)(q:Clip)(p k:ℕ)(a b w:ℝ)(x:G.ColorIndex):Prop where
    cane : Cane P V.tilt V.pre a V.shape V.axis k
    grade : a/(S.ratio.count.val:ℝ)≤ b
    seat : Station F τ ρ R l (installed S.ratio P) k (a/(S.ratio.count.val:ℝ)) V.c1 V.c2 V.c3 V.c4
    forest (r:ℕ)(hp:r≤p)(u:ℕ)(wo:u≤r) : Tokew (address F G) (a/(S.ratio.count.val:ℝ)) k (snag r) 0 (PowerSeries.coeff u (fuelTest F τ J)) V.farms
    pearl (r:ℕ)(hp:r ≤ p): Tin (Measuring.chart c G) a k (r+1) w (ink c q H) (w^2*V.bc) ∧ Tin (Measuring.chart n G) b k (snag r) w (ink n l R) (w^2*V.bf)
    cand :1 ≤ |caliper c (sun G x) (ink c q H)|
    cap : 2 ≤ S.ratio.count.val
    crop: Guessed F (installed S.ratio P) ρ
    critical: Critical F l R ρ
variable (V:Fees)(R:PathData G)(l:Clip)(ρ:fieldDir G c 1→AxisChart G F)(H:PathData G)(q:Clip)(τ:S.Choices)
variable (P:Cross S.ratio.count (TypeFace 1) (TypeFace 1)) (J:ChartRatio G)
variable (f:Nesting G n)(α:ℝ→ Config G n → ℝ)(x:G.ColorIndex){M p r k:ℕ}{v w a b:ℝ}(h:Trend α f R l p)(hG:G.Simple)(hh: Keeps f p (sun G x))
variable (ht:Ready V G E S.ratio.count M p a v w)(hr:SceneB V F τ P J ρ R l H q p M a b w x)(hk:Wedge f E w b M p)
variable {s:PowerSeries ℝ}(ho:PowerSeries.coeff 0 s=1)
local notation "f'"=>colorCut F τ R l J f ρ
local notation "K!"=> bley s f' (ink c q H)
variable (he: Keeps (bley s (colorCut F τ R l J f ρ) (ink c q H)) p (sun G x))
variable (hD:Expanse (colorCut F τ R l J f ρ) 1 p)(hz:Kind (colorCut F τ R l J f ρ))
include hv h hG hh ht hr hk ho he hD hz
lemma paths (r:ℕ)(hP:r≤p) : Tin T a M (r+1) w (PowerSeries.coeff r (colorCut F τ R l J f ρ)) (purse E v r) ∧
      Tin T a M (r+1) w (PowerSeries.coeff r K!) (purse E v r)∧|PowerSeries.coeff r s|≤ purse E v r:=by
    have h0:1≤v:= ht.wise.1; have h₀:=ht.s0; have hV:1≤ w:= le_trans h0 ht.wise.2; have hW:0<w:=zero_lt_one.trans_le hV; let D(x):=purse E v x; have hv0(x):1 ≤D x:=one_le_pow₀ h0; have hb:0≤b:=(div_nonneg hr.cane.a0 (by positivity)).trans hr.grade
    induction r using Nat.strong_induction_on with
    | h r ih=>
      by_cases h₁:r=0
      · subst r; have hx:0 ≤ D 0:= zero_le_one.trans (hv0 _); let T':= μ 0 K!
        have H:T'=0:=by unfold T' bley; rw [_root_.map_sub,PowerSeries.coeff_mk,Wave.ticket,PowerSeries.coeff_mk]; simp [Wave.fare,show PowerSeries.constantCoeff f'=0 from (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, Kind] using! hz), show PowerSeries.constantCoeff s=1 from (by simpa using ho)] -- Kind simp
        rw [show μ 0 f'=0 from hz, show μ 0 K! =0 from H]; have hX:Tin T a M (0+1) w 0 (purse E v 0):=by rw [← show (MvPolynomial.C 0: Pot Y)=0 from MvPolynomial.C_0]; exact Tin.constant hW 0 hx
        exact ⟨hX,hX,by rw [ho,abs_one]; exact hv0 _⟩
      let Z:= purse E w r; let A₀:= purse E w (r-1); let B:= V.lead E w r; let K:= V.coin G S.patch.L w M r a Z B
      have hL : 1≤ A₀:=one_le_pow₀ hV; have hB:A₀ ≤ B:= le_add_of_nonneg_right (mul_nonneg (show 0≤1+V.bf from (add_nonneg zero_le_one h₀.2)) (sq_nonneg _))
      have hq (i:ℕ)(hi:i<r):D i≤ purse E w i ∧ purse E w i ≤ A₀:= ⟨pow_le_pow_left₀ (zero_le_one.trans h0) ht.wise.2 _,pow_le_pow_right₀ hV (hv (by omega : i≤ r-1))⟩
      have hz(i:ℕ)(hi:i<r): Tokew ℓ b M (snag r) 0 (μ i f) B:= ((Tin.aspires hW (hk.shares _ (hi.le.trans hP)) (h.plane.profile _ (hi.le.trans hP)|>.trans (by omega)) (snag r)).weightTok hW hV).delta le_rfl ((hq i hi|>.2).trans hB)
      have hu(i:ℕ)(hi:i<r):Tokew ℓ b M (snag r) 0 (PowerSeries.coeff i (tariff n p l R f)) B:=by
         unfold tariff; rw [map_sub]; by_cases hh:i=0
         · subst i; rw [h.bond,PowerSeries.coeff_zero_eq_constantCoeff_apply (PowerSeries.C _),PowerSeries.constantCoeff_C,zero_sub,←neg_one_smul ℝ]; refine Tokew.delta (Tokew.smoky ((hr.pearl r hP).2.weightTok hW hV) (-1)) le_rfl ?_; simp only [abs_neg,abs_one,one_mul]; calc
              _ ≤ (1+V.bf)*w^2:=by rw [mul_comm]; gcongr; linarith
              _ ≤ B:=le_add_of_nonneg_left (zero_le_one.trans hL)
         rw [PowerSeries.coeff_C_of_ne_zero hh,sub_zero]; exact hz i hi
      have hp':0 < r:=by omega
      have hm :Tin T a M (r+1) w (μ r f') K:= ascentPub F τ P f α R l x J hG h hh hP hp' hb ht.grade (hk.shares _ hP) hV hr.cane ht.axis hr.cap hr.grade (zero_le_one.trans (hL.trans hB)) hr.seat hr.critical hr.crop hz hu (hr.forest r hP)
      obtain ⟨hp₀,hp₁,hp₂⟩:=ht.prize r hp' hP
      have hA:= he.level; have hX:Keeps K! r (sun G x):=⟨fun i hi=> he.sitting _ (hi.trans hP),⟨fun i hi=> he.level.1 _ (hi.trans hP)⟩⟩
      have hh:= prestige _ x _ _ hp' (show ∀ i<r,|μ i s|≤ A₀ from fun i hi=> ((ih i hi (hi.le.trans hP)).2.2).trans (le_trans (hq i hi|>.1) (hq i hi|>.2))) ho hL ‹Kind f'› ⟨fun i hi=>hD.1 _ (hi.trans hP)⟩ hV (A:=A₀) (fun i hi=>?_) hm h₀.1 (by omega) (hr.pearl r hP|>.1) hr.cand ((by omega: 2≤6).trans ht.grade) hX hr.cane.a0
      · exact ⟨hm.it hW hp₀ le_rfl,hh.1.it hW ((by change _ ≤ (D r); rw [add_comm (salary r A₀ A₀) K]; exact hp₁)) le_rfl, hh.2.trans (by rw [add_comm (salary r A₀ A₀) K]; exact hp₂)⟩
      exact ((ih i hi (hi.le.trans hP)).1.aspires hW (hD.profile _ (hi.le.trans hP)|>.trans (by omega)) (r+1)).it hW (le_trans (hq i hi|>.1) (hq i hi|>.2)) le_rfl
end YM.MSbar.Alto
