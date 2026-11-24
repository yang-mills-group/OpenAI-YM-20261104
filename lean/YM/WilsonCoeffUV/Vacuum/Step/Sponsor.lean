import YM.WilsonCoeffUV.Vacuum.Step.Recurrence
/-!
# Uniform purse pre/post. Kinematic post also independent of cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{k r:ℕ} {I:Gear G} {A B B' C s t σ: ℝ}
-- one diagonal retention & all other arrows.
structure Kept (R:Rally (k+1) (r+2) I) (D:ℕ) (Z A B:ℝ): Prop where
  front: Amber terrain I.σ (I.gain r*A/I.patch.L.val+Z*R.x^D) (R.P.stake (k+1) (r+2))
  backC: Amber terrain I.σ (I.gain r*A/I.patch.L.val+Z*R.x^D) (R.Q.stake (k+1) (r+2))
  gap : Amber terrain I.σ (I.gain r*B/I.patch.L.val+Z*R.x^D*(1+A)*R.σ) (R.P.stake (k+1) (r+2)-R.Q.stake (k+1) (r+2))

private lemma stylize (x g S V K C E O R A B L θ:ℝ)(u:ℕ)(hx: 1≤x)(hp:0≤g)(hv:0≤ V)(hk:0≤K)(hh:0≤C)(hS:0≤ S)(hE:0≤E)(hO:0≤O)(hR:0≤R)(hL:0<L)(hz:0≤θ)(hA:0≤ A):
    let H₀:=V*S+C
    let H₁:= (R+g/L+V+K+1)*(1+S+C+E+O)^3
    ((g*A/L+V*x)*S+C*x^u ≤ g*S*A/L+(H₀ + H₁)*x^(u+1)) ∧
    ((g*B/L+V*(x*θ)+ K*A*θ)*S+(g*A/L+V*x)*E*(O*θ)+C*x^u*θ ≤ g*S*B/L+(H₀ +H₁)*x^(u+1)*(1+A)*θ):=by
    intro H₀ H₁; have h0:= add_nonneg (mul_nonneg hv hS) hh
    have ht:0≤ H₁:= by unfold H₁; positivity
    let Z:= x^(u+1)
    have hhx:=zero_le_one.trans hx
    have hXZ : x≤Z:= by unfold Z; rw [pow_succ]; exact le_mul_of_one_le_left hhx (one_le_pow₀ hx)
    have hZ:= hx.trans hXZ
    have hT: x^u≤Z:= pow_le_pow_right₀ hx (by omega)
    have hr:= div_nonneg hp hL.le
    let U:=1+S+C+E+O
    have hu : 1≤U:= by unfold U; linarith;
    have hb := zero_le_one.trans hu
    have h01 : S ≤ U:=by unfold U; linarith
    have h02 : E * O ≤ U^2 := by rw [pow_two]; exact mul_le_mul (by unfold U; linarith) (by unfold U; linarith) hO hb
    have hv0 : K*S+(g/L+V)*E*O≤ H₁:= by
       unfold H₁; apply le_trans (b:=K*U+(g/L+V)*U^2) (add_le_add (mul_le_mul_of_nonneg_left h01 hk) (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h02 (add_nonneg hr hv)))
       have h3: U≤ U^3 := (pow_one U).ge.trans (pow_le_pow_right₀ hu (show 1≤3 by omega))
       have h4: U^2 ≤ U^3:= pow_le_pow_right₀ hu (by omega)
       change _ ≤(R+g/L+V+K+1)*U^3
       exact (add_le_add (mul_le_mul_of_nonneg_left h3 hk) (mul_le_mul_of_nonneg_left h4 (add_nonneg hr hv))).trans (by
          have hx:0≤ R*U^3 := by positivity
          linarith only [hx,pow_nonneg hb 3])
    have ha : 0≤ 1+A:=by linarith
    have hA': A≤ Z*(1+A) := by
       apply le_trans _ (le_mul_of_one_le_left ha hZ); linarith
    have he : x≤ Z*(1+A):= hXZ.trans (le_mul_of_one_le_right (zero_le_one.trans hZ) (by linarith))
    have he0 : x^u≤Z*(1+A):=hT.trans (le_mul_of_one_le_right (zero_le_one.trans hZ) (by linarith))
    have H2 : g*A/L+V*x≤(g/L+V)*(Z*(1+A)) := by
       rw [add_mul]; nth_rw 1 [mul_comm g]; rw [mul_div_assoc, mul_comm A]; exact add_le_add (mul_le_mul_of_nonneg_left hA' hr) (mul_le_mul_of_nonneg_left he hv)
    constructor
    · calc
       _ = g*S*A/L+(V*S*x+C*x^u):= by ring
       _ ≤ g*S*A/L+H₀*Z := add_le_add_right (by unfold H₀; rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_left hXZ (mul_nonneg hv hS)) (mul_le_mul_of_nonneg_left hT hh)) _
       _ ≤ _:= add_le_add_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ht) (zero_le_one.trans hZ)) _
    calc
       _ = g*S*B/L+(V*S*x+C*x^u+ (K*S*A+(g*A/L+V*x)*E*O))*θ := by ring
       _ ≤ g*S*B/L+(H₀*(Z*(1+A)) +(K*S+(g/L+V)*E*O)*(Z*(1+A)))*θ:= by
          apply add_le_add_right; apply mul_le_mul_of_nonneg_right _ hz; rw [show H₀=V*S+C from rfl, add_mul (V*S) C, add_mul (K*S)]
          apply add_le_add (add_le_add (mul_le_mul_of_nonneg_left he (mul_nonneg hv hS)) (mul_le_mul_of_nonneg_left he0 hh))
          apply add_le_add (mul_le_mul_of_nonneg_left hA' (mul_nonneg hk hS)); refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right H2 hE) hO) (le_of_eq ?_); ring
       _ ≤ _:= by
          apply add_le_add_right; apply mul_le_mul_of_nonneg_right _ hz; rw [mul_assoc (H₀+H₁),add_mul H₀ H₁]; exact add_le_add_right (mul_le_mul_of_nonneg_right hv0 (mul_nonneg (zero_le_one.trans hZ) ha)) _

theorem purse (G:Gauge)(k r:ℕ): ∃ d:ℕ,∀ I:Gear G,∃ C:ℝ,0≤ C ∧∀ R:Rally (k+1) (r+2) I,I.towing r→∀ A B, Amber terrain I.past A (R.P.page (k+1) (r+2))→Amber terrain I.past A (R.Q.page (k+1) (r+2))→ Amber terrain I.past B (R.P.page (k+1) (r+2)-R.Q.page (k+1) (r+2))→ Kept R d C A B := by
    obtain ⟨u,H⟩:= early_stripe (G:=G) (k+1) (r+2)
    obtain ⟨v,T⟩:= note_partial (G:=G) (k+1) (r+2)
    refine ⟨u+1,fun I=>?_⟩; obtain ⟨c,hc,H⟩:= H I
    let g:=I.bill r; let s:=I.σ; let S:= ruby s I.sig; let V:= I.twist (k+1) r; let E:=ceilPoly 2 (s/2)*sheetPay (s/2); let L:ℝ:=I.patch.L.val; let O:=I.D; let K:=barrel I r
    have hg:0≤g:=Gear.bill0; have hS:0≤S:=zero_le_one.trans (ruby_nn I.price I.tag_nn); have hK:=barrel_nn I r; change 0≤K at hK; have hV:0≤V:= Gear.twist0; have hO:0≤O:= zero_le_one.trans I.bill_nn
    have hL :0<L:=by unfold L; positivity
    have hE : 0≤E:= mul_nonneg (ceilPoly_pos ..).le (sheetPay_pos _ (div_pos I.price (by norm_num))).le
    refine ⟨(V*S+c)+(0+g/L+V+K+1)*(1+S+c+E+O)^3,by positivity,?_⟩
    intro R hp A B he hq ht
    obtain ⟨ha,hb,he'⟩:= turningC R he hq ht hp
    have hf:= H R; obtain ⟨_,_,T⟩:= T I; have h':=T R
    let w:=R.P.zenith (k+1) (r+2); let W:=R.Q.zenith (k+1) (r+2)
    let D:= orbQ R.P.Z; let D':=orbQ R.Q.Z
    have hD: Amber terrain s I.sig D:= drag_orb (R.P.topQ.mono I.holds.le); have hD': Amber terrain s I.sig D':=drag_orb (R.Q.topQ.mono I.holds.le)
    have hh : PairA s O R.σ D D':= by have he := kernel_pair (R.Ω.mono I.holds.le) 0 2; simp only [flatPal,↓reduceIte,shine_lit] at he; exact he
    have hx := stylize R.x g S V K c E O 0 A B L R.σ u R.rich hg hV hK hc hS hE hO le_rfl hL R.θ he.1
    rcases hx with ⟨hl,hm⟩
    have hv0 := Stand.shake_post R.P k r h'.pose ha
    have hv1:= Stand.shake_post R.Q k r h'.vale hb
    constructor
    · rw [hv0]; exact (((apt I.price hD ha).add hf.pose).le hl)
    · rw [hv1]; exact (((apt I.price hD' hb).add hf.vale).le hl)
    rw [hv0,hv1,add_sub_add_comm];
    have Hz : retent D w-retent D' W= retent D (w-W)+(retent D W-retent D' W):= by rw [retent_sub _ ha hb I.price]; abel
    change Amber terrain _ _ ((retent D w - retent D' W)+ _); rw [Hz]; have he:= (app_gap I.price hh.visit hb).neg
    rw [neg_sub] at he; exact (((apt I.price hD he').add he).add hf.visit).le hm
end YM.WilsonCoeffUV.Bank
