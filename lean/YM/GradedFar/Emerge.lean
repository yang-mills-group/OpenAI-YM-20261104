import YM.GradedFar.Detector
/-!
# MeasuredInverse at centers of original OPE comparisons, pointwise all phases (no short-r derivatives here)

This exercises M3 on an additional finite detecting program. OPE coefficient/packet estimation
on all Near **u** simultaneous. Both estimates below on s=r*T horizon, third cost of M.4 post-pick
reports against every fixed order target, via selecting p after allowed B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Finset Filter Function Set Spec Table Extraction
open OPE OPE.Orbits
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2 FVA2.O.Enh FVA2.GradedFar FVA2.Scale FVA2.O.Score
open Budget FVA2.Dframe MS MS.Book MS.Fleet MS.Land FVA2.Register
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book} (F:Final C fo S)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower S)
    {n p p' l h:ℕ}{d:Fin n→ℕ}
variable (N:WilsonPrescription G){hG:G.Simple}(Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:MS.Land.Prescription (Press.portDeck G)}(H:Main.Match N hG Z σ true)(ν:ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "g" => strength G
local notation "port" => RootG
variable {K:Set (Points n)}{t:ℝ→ℝ}{η B Λ a:ℝ}(hd:AppointedH140Through l d)(hh:h≤l)
    (hΛ:0<Λ)(hB:0<B)(ha:0<a)
def Emerging (a Λ η B:ℝ)(p' p:ℕ) (K:Set (Points n)) (h:ℕ)(d:Fin n→ℕ) (t:ℝ→ℝ):Prop:=
    ∃ b:ℝ, 0 ≤ b ∧ ∀ᶠ r in trail, ∀ T:ℝ,receding (g r) B a Λ T → ∀ o,
      (∀ v:Viewers F,∃ hi:Injective (Detect F J h v o r T), Bank.invPrice _ hi ≤ b*T^h) ∧
      ∀ x∈K,∀ u:AppointedH140Inputs G d, Box u 1 →
      width (packet F J Q h o r x u - croppedVector A h p u x (t r)) ≤ b*(g r)^p'*T^(-η)

-- elementary subtraction extraction helper
private lemma sensorBound {Y y:ℂ}{M m:Sec G h →ₗ[ℂ] ℂ}{a b:Sec G h}{L:ℝ}
    (ha: ‖Y-y‖ + rowPrice (M-m) + ‖(Y-y)-(M-m) a‖ + ‖Y-M b‖+ ‖Y-M a‖ ≤ L):
    ‖M (b-a)‖ ≤ L := by
  rw [map_sub, show M b - M a=(Y-M a)-(Y-M b) from by abel]; refine (norm_sub_le ..).trans (le_trans ?_ ha); rw [add_comm ‖Y-M a‖]
  rw [add_assoc (‖Y-y‖ + rowPrice (M-m) + ‖(Y-y)-(M-m) a‖)]
  exact le_add_of_nonneg_left (add_nonneg (add_nonneg (norm_nonneg _) (show 0 ≤ rowPrice (M-m) from ContinuousLinearMap.opNorm_nonneg (row (M-m)))) (norm_nonneg _))

include H hΛ hB ha
theorem landed (predict:FrameForecast J t W h Λ B) (fund:LeadingTicket F J h t N Λ B)
    (budget:BeforeInverse F J Q N Z ν t hd (e:=Output h) (fun _=>hh) hh K {port} a Λ η B p' p):
    Emerging F Q J N a Λ η B p' p K h d t := by
  obtain ⟨b,hb,H'⟩:=Wall_inverse F J h N Z H ν hΛ hB fund predict
  obtain ⟨V,vpos,E⟩:=budget
  refine ⟨max b (b*V), (zero_le_one.trans hb).trans (le_max_left ..),?_⟩
  filter_upwards [H',E,strength_positive hG, (strength_falls hG).eventually (upwards hB ha 1)] with r hr he hp ho T hT o
  have ht:= ho _ hT.1; let R(ω:Viewers F):= Detect F J h ω o r T
  constructor
  · intro ω; obtain ⟨Hno,Hs⟩:= hr _ ht hT.2 ω o; exact ⟨Hno,Hs.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))⟩
  intro x hxx u hu
  have hX:= (he T hT x hxx port (Set.mem_singleton _)).2.2
  -- x-u & v stay independent. use all phases; pick e.g. none for proof (estimate before true on arbitrary v).
  let P:=packet F J Q h o r x u; let c:=croppedVector A h p u x (t r)
  have hz : 0≤ (g r)^p'*T^(-(h:ℝ)-η):=by positivity
  have ht'(ω:Viewers F): ‖R ω (P-c)‖ ≤ V*(g r)^p'*T^(-(h:ℝ)-η):= by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2; intro i
    rw [show R ω (P-c) i=atCenter F J h ω o r T port (Bank.play i) (P-c) from detects ..]; exact
      sensorBound (hX o ω u (Bank.play i) hu (Bank.plays _))
  obtain ⟨Hno,Hs⟩:= hr T ht hT.2 none o; apply (Bank.margin Hno (P-c)).trans
  refine (mul_le_mul Hs (ht' none) (norm_nonneg _) (by positivity)).trans ?_
  have hP:0<T:=zero_lt_one.trans_le ht
  rw [show b*T^h*(V*(g r)^p'*T^(-(h:ℝ)-η))= b*V*(g r)^p'*T^(-η) from ?_]; gcongr; apply le_max_right
  rw [show -(h:ℝ)-η=-η-(h:ℝ) by ring, Real.rpow_sub hP, Real.rpow_natCast]; field_simp

-- delete orders > q on compact Near
variable (hK:IsCompact K)(hx:K⊆conf n)(ht:Coupling G t)
include ht hK hx ν
omit hΛ in
lemma rich {q:ℕ} (_hd:AppointedH140Through l d) (_h:h≤l) (H':Emerging F Q J N a Λ η B (q+1) p K h d t) (hη:0<η) (hsub:a≤Λ) (hp:q≤p):
    ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ∀ o x, x∈K → ∀ u:AppointedH140Inputs G d, Box u 1 →
    width (packet F J Q h o r x u - croppedVector A h q u x (t r)) ≤ C*(g r)^(q+1) := by
  obtain ⟨b,hb,H''⟩:=H'; obtain ⟨c,hc,hc'⟩:= crop_cap (d:=d) (H.separatedOPE ν).wilson hK hx h hp 1 zero_le_one
  refine ⟨b+c*2^(q+1),by positivity,?_⟩
  filter_upwards [clock_budget hG ht,H'',(strength_falls hG).eventually (upwards hB ha 1)] with r hr H u'
  intro o x hX w hw; let T:ℝ := a*(g r)^(-B); have hr':0<g r:=hr.1
  have hT : receding (g r) B a Λ T:=⟨le_refl _, by unfold T; gcongr⟩
  let A':=croppedVector A h p w x (t r); let T':=croppedVector A h q w x (t r); let B':=packet F J Q h o r x w
  have hp:= (H T hT o).2 x hX w hw; have he:= hc' x hX w hw _ hr.2.1
  have hf : T^(-η)≤1:= Real.rpow_le_one_of_one_le_of_nonpos (u' T hT.1) (neg_nonpos.mpr hη.le)
  calc _ = width ((B'-A')+(A'-T')):=by rw [sub_add_sub_cancel]
       _ ≤ width (B'-A')+width (A'-T'):= width_add ..
       _ ≤ _:= (add_le_add (hp.trans (mul_le_of_le_one_right (by positivity) hf)) (he.trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hr.2.2 _) hc))).trans_eq (by ring)

omit ha hB
-- requested H-frame version toward final OPE comparison: retains choice Q and all compacts. Uses B after geometry.
theorem localized
    (Hq:LogTrace F Q.port) (Hh:Fork.Coat F Q J h)(Hp:∀ i,Fork.Coat F Q J (d i))
    (hW:∀ B> (0:ℝ),FrameForecast J t W h Λ B)
    (fund:∀ B>0, LeadingTicket F J h t N Λ B)
    (hf:∀ B>0,∀ p,RoundPoint F J t A hd (e:=Output h) (fun _=>hh) Λ B p K {port})
    (hout:∀ B>0,∀ p,RoundPoint F J t A (d:=Output h) (fun _=>hh) (e:=Output h) (fun _ => hh) Λ B p {0} {port}) (q:ℕ):
    ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail, ∀ o x, x∈K → ∀ u:AppointedH140Inputs G d, Box u 1 →
    width (packet F J Q h o r x u - croppedVector A h q u x (t r)) ≤ C*(g r)^(q+1) := by
  obtain ⟨B,hB,H'⟩:= ((eventually_gt_atTop 0).and (before_of_prices F Q J N Z H ν ht hd (e:=Output h) (fun _=>hh) hh hK hx isCompact_singleton
    (singleton_subset_iff.mpr ok_wall) Hq Hh Hp (fun _=> Hh) hΛ hΛ (by norm_num : 1/2 < (1:ℝ)) (fun i hi _=>hW i hi) hf hout (q+1))).exists
  obtain ⟨p,hp,hX⟩:= ((eventually_ge_atTop q).and H').exists
  exact rich F Q J N Z H ν hB hΛ hK hx ht hd hh
    (landed F Q J N Z H ν hd hh hΛ hB hΛ (hW B hB) (fund _ hB) hX) (by norm_num) le_rfl hp

-- (M.4) from `RoundPoint` still a hypothesis, not discharging all actual comparisons.
end YM.Integration.GradedFar
