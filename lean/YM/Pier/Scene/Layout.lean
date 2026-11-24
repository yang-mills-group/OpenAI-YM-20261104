import YM.Pier.Scene.Integral
/-! Keep ONE explicit Layout for this scene comparison, sharing its reporting scale with
any such given RG17 extraction order and Mantle. Still no matching to a
Wilson perturbative field frame or all-scale inverse. Keep the Pegs &
sparse resource. Actually check a comparability price on the true
chosen level for all small scales, before finer arity/order budgets, including
a common thread of the Pegs radii if needed. The step `reading` of the
actual marked scene may then take further polynomial zoom refinements; its
costs also live on this Layout, not recoined fields, and allow every fixed power.
Adapted from Tarmac/Sparse/Pitch, and idea cf. Lyre.lean.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Panoramic
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Overlay
open FullVolume.Sever MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Extra.Multi Next.Rank Edition Spindle SharpGram Trace RG12 Next.UVStress
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open OPE OPE.Yarn Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Patrol PertExtension
open OPE.Strobe OPE.Strobe.Panoramic
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G)
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "C"=> R.family
local notation "A"=> R.family.path.levels
local notation "a" => R.family.S.a
set_option quotPrecheck false
variable {T0:Campaign R}{W:Campaign.Pillars R T0} {h:G.Simple}(U:Pier.Starter R h T0 W)
include U

/-! ### Polynomial depth for precision gains -/
omit U in
private lemma betas_m (h:G.Simple) : Monotone (H):= WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos h).le
omit U in
private lemma delta (m n:ℕ): H n=H m+G.slopeConstant*(Real.log (a m/a n)) := by
    rw [Real.log_div ((C).S.a_pos _).ne' ((C).S.a_pos _).ne']
    unfold Calendar.hatBeta Schedule.scale; simp_rw [Real.log_inv]; change _ + G.slopeConstant*(-(Real.log (a n)))= _+G.slopeConstant*(-Real.log (a m))+G.slopeConstant*_ -- parentheses
    ring
omit U in
private lemma someMark (m p:ℕ): ∃ n:ℕ,m<n ∧ a n*H m^p ≤ a m := by
    let t:= H m^p; have hx:= (C).S.shrinks.mul_const t
    exact ((eventually_gt_atTop m).and (hx.eventually (ge_mem_nhds (show 0*t < a m from (zero_mul _).trans_lt ((C).S.a_pos m))))).exists
omit U in
-- mark parameter `s` number units of log(H); pick an actual finer node (may jump a rung even for 0).
def berth (s m:ℕ) : ℕ := Nat.find (someMark R m s)
omit U in
lemma arrival (s m:ℕ) : m<berth R s m ∧ a (berth R s m)*H m^s ≤ a m := Nat.find_spec (someMark R m s)

/-- fixed power without recurrence loss. -/
lemma cruise (s:ℕ) : ∀ᶠ m:ℕ in atTop,
    let y:= berth R s m
    H y ≤ 2*H m ∧ (a m)*(H m)⁻¹^(s+2) ≤ a y := by
    let K(z:ℝ):= Real.log z; let l:= G.slopeConstant; have hl:0<l:= Gauge.slopeConstant_pos h
    have hm:Tendsto (fun z:ℝ=> l*((s+2:ℕ)*K z)/z) atTop (𝓝 0):=by
       have hv:= Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
       simpa only [K, mul_zero, ←mul_div_assoc, mul_assoc, id_eq] using! hv.const_mul (l*(s+2:ℕ)) -- type
    have hβ := Station.hat_rate (A) h; filter_upwards [hβ.eventually_ge_atTop 2, hβ.eventually (hm.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)))] with m hs hb y
    let p:= H m; have hp:2≤p:= hs; have hx:0<p:= zero_lt_one.trans ((A).fits.delayed m)
    have hh:l*((s+2:ℕ)*Real.log p) ≤ p:= (div_le_one₀ hx).mp hb
    obtain ⟨i,hI⟩:= Nat.exists_eq_succ_of_ne_zero (show y ≠ 0 from (Nat.zero_le m|>.trans_lt (arrival R s m).1).ne') -- y is let! can't rfl
    have hi:m ≤ i:=by have hh : m<y:= (arrival R s m).1; omega
    have he : a m/a i ≤ p^s:=by
       obtain he|rfl:= lt_or_eq_of_le hi
       · have hq:a m < a i*p^s:= lt_of_not_ge fun h'=> by
              have hi:y ≤ i:= Nat.find_min' (someMark R m s) ⟨he,h'⟩; omega
         exact (div_le_iff₀ ((C).S.a_pos i)).mpr (hq.le.trans_eq (mul_comm ..))
       rw [div_self ((C).S.a_pos _).ne']; exact one_le_pow₀ (by linarith)
    have hz {z q:ℕ} (hq:q≤ s+2) (hf:a m/a z ≤ p^q) : H z ≤ 2*p := by
       have hσ:= Real.log_le_log (div_pos ((C).S.a_pos _) ((C).S.a_pos _)) hf; rw [Real.log_pow] at hσ
       have hf := (mul_le_mul_of_nonneg_left (hσ.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hq)
          (Real.log_nonneg ((A).fits.delayed m).le))) hl.le).trans hh
       rw [delta R m]; change p+l*_≤_; linarith only [hf]
    let V:= ((A).S.block i).val
    have hP : (V:ℝ) ≤ p^2:= by
       have hr: (V:ℝ) ≤ H i:= (U.flick.grade i).trans (Real.log_le_self (zero_lt_one.trans ((A).fits.delayed _)).le)
       exact hr.trans ((hz (show s≤ s+2 by omega) he).trans (by nlinarith only [mul_le_mul_of_nonneg_right hp hx.le]))
    have hk : a m / a (i+1) ≤ p^(s+2):=by
       have hf: a m/a (i+1)=(a m/a i)*(V:ℝ):= by rw [(C).S.a_step i]; let M:=a i; exact (by unfold V; rw [div_div_eq_mul_div, div_mul_eq_mul_div])
       rw [hf,pow_add]; exact mul_le_mul he hP (Nat.cast_nonneg _) (pow_nonneg hx.le _)
    rw [hI]; refine ⟨hz le_rfl hk,?_⟩; rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ (pow_pos (show 0<H m from hx) _)]; exact ((div_le_iff₀ ((C).S.a_pos _)).mp hk).trans_eq (mul_comm ..)

open Extraction SharpGram Spec
variable {u:Filter (ℕ×ℕ)}{f:Extraction.Order}{S:Table R.family.book}{F:Final R.family f S}(B:Lenses.Mantle F u)
local notation "s₀"=> R.family.S.scale
local notation "ω"=> OPE.run

def Comparably (p : ℝ→ℕ) : Prop:= ∀ᶠ r in home,a (p r) ≤ r ∧ r ≤ a (p r)*H (p r)^2

lemma comparableDefault : Comparably R (fun r=> PertExtension.Running.choose (C) r⁻¹) := by
   let p r := Running.choose C (r⁻¹)
   filter_upwards [positiveLength, (catchLevel (C)).growing.eventually_gt_atTop 0] with r hr hs
   obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero (show p r≠ 0 from (ne_of_gt hs))
   have hv : s₀ i < Real.log r⁻¹:=lt_of_not_ge fun h'=> by
         have hx:p r ≤ i:= Nat.find_min' _ h'; omega
   have hx : Real.log r⁻¹ ≤ s₀ i.succ:= by rw [← hi]; exact Running.chosen C r⁻¹ -- elim problematic
   have hp(z):0<a z:= (C).S.a_pos _
   unfold Schedule.scale at hx hv; rw [Real.log_inv,Real.log_inv,neg_le_neg_iff] at hx; rw [Real.log_inv,Real.log_inv,neg_lt_neg_iff] at hv
   have hw := (Real.log_lt_log_iff hr (hp _)).mp hv
   change a (p r) ≤ r ∧ r ≤ a (p r)*H (p r)^2; rw [hi]
   have hL : ((A).S.block i).val ≤ (H (i+1))^2 := (U.flick.grade i).trans ((Real.log_le_self (zero_lt_one.trans ((A).fits.delayed _)).le).trans ((betas_m R h (Nat.le_succ i)).trans (by
      conv_lhs => rw [← pow_one (H (i+1))]
      exact pow_le_pow_right₀ ((A).fits.delayed _).le (by decide))))
   refine ⟨(Real.log_le_log_iff (hp _) hr).mp hx, hw.le.trans (le_trans ?_ (mul_le_mul_of_nonneg_left hL (hp (i+1)).le))⟩
   exact (le_of_eq (by change _ = (a (i+1))* (((C).S.block i).val:ℝ); rw [(C).S.a_step i,div_mul_cancel₀ _ (by positivity)])) -- adjust

omit U in
private lemma visible {radii:ℕ→ℝ} (h:StrictAnti radii)(ht:∀ i,0<radii i)(Q:ℝ→Prop)
    (hQ:∀ᶠ i in atTop,Q (radii i)) (hp:∀ᶠ i in home,i∉ Set.range radii → Q i) : ∀ᶠ i in home,Q i:=by
   obtain ⟨N,hN⟩:= eventually_atTop.mp hQ
   filter_upwards [hp,(nhdsWithin_le_nhds (ge_mem_nhds (ht N)) : ∀ᶠ i in home,i ≤ radii N)] with i he hm
   by_cases hh:i ∈ Set.range radii; swap; exact he hh
   obtain ⟨m,rfl⟩:= hh; exact hN _ (h.le_iff_ge.mp hm)
lemma pierLevel (s:Extraction.Sequence)(hs:StrictAnti (B.radius ∘ ⇑s)) : ∃ p:ℝ→ℕ,Reach C p ∧ Comparably R p ∧ ∀ i:ℕ,p (B.radius (s i))=s i:=by
   let radii:= B.radius ∘ ⇑s
   let p (r:ℝ):ℕ:= if h:r∈ Set.range radii then s h.choose else Running.choose C r⁻¹
   have hp(i:ℕ): p (radii i)=s i := by
       rw [show p (radii i)=_ from dif_pos (Set.mem_range_self i)]; exact congr_arg _ (hs.injective (Classical.choose_spec (mem_range_self i : ∃ j, radii j=radii i)))
   have ht i :0 < radii i:= B.positive _
   have hv:=catchLevel C
   refine ⟨p,⟨tendsto_atTop.mpr ?_, Metric.tendsto_nhds.mpr ?_⟩,?_,hp⟩
   · intro n; apply visible hs ht
     · filter_upwards [s.cofinal.eventually_ge_atTop n] with i hi; change n ≤ p (radii i); rw [hp i]; exact hi
     filter_upwards [hv.growing.eventually_ge_atTop n] with i hi ht; change n ≤ p i; rw [show p i=Running.choose C i⁻¹ from dif_neg ht]; exact hi
   · intro ε he; apply visible hs ht
     · filter_upwards [s.cofinal.eventually (Metric.tendsto_nhds.mp (retainedPaid B) ε he)] with i hi; change dist (s₀ (p (radii i))/ _) (1:ℝ)<ε; rw [hp]; exact hi
     filter_upwards [Metric.tendsto_nhds.mp hv.nearby ε he] with i hi he; rw [show p i= _ from dif_neg he]; exact hi

   apply visible hs ht (fun r=>a (p r) ≤ r ∧ r ≤ a (p r)*H (p r)^2)
   · filter_upwards [s.cofinal.eventually B.proper] with n hn
     change a (p (radii n)) ≤ radii n ∧ radii n ≤ a (p (radii n))*H (p (radii n))^2
     rw [hp]
     exact hn
   filter_upwards [comparableDefault R U] with i hi he
   rw [show p i= Running.choose C i⁻¹ from dif_neg he]
   exact hi

variable (J: Services R.family f S) (P:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
include B J P
lemma installable [u.NeBot] (he:u ≤ f.fuse):
    ∃ (L:Layout F), L.shift=(fun _ _=> LinearEquiv.refl ..) ∧ Pegs B L ∧ Located L ∧ Handles L ∧
       Comparably R L.level ∧ ∃ s : Extraction.Sequence,
       StrictAnti (B.radius ∘ ⇑s) ∧ ∀ i:ℕ, L.level (B.radius (s i))= s i := by
   obtain ⟨s,hs⟩:= thinning B
   obtain ⟨p,hp,hC,hR⟩:= pierLevel R U B s hs
   obtain ⟨L,hl,hX,hU⟩:= installed (B:=B) he p hp (fun d _=> LinearEquiv.refl ..)
   refine ⟨L,hX,hU,situated B L J hU P ?_ ?_ ?_, commands B L J hU, hl.symm ▸ hC,s,hs, by rw [hl]; exact hR⟩
   · intro d; rw [hX]; exact RateLE.const _ ageLarge
   · intro d; rw [hX]; exact RateLE.const _ ageLarge
   rw [hX]; exact Eventually.of_forall fun _=>rfl
end YM.RG17.Panoramic
