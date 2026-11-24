import YM.Integration.CalibratedCellMatch

/-! The original anchored coefficient can be chosen at any admitted coarse
stop. Its inverse coordinate is computed in the actual music of the same
finite family. This refines the native `MergeProof.Accent.commune` argument
and retains the consecutive `Accord`s and signed column identities. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.TransmittedCellMatch
open MergeProof MergeProof.Accent MergeProof.Float PhysicalNext.Repeat Lotus
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Relay
variable {G : Gauge} (C : Family G) (N k m p d : ℕ) (H : C.Makes)
variable {W : Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ} {ζ : ℕ → ℕ → ℝ}
  {D : ∀ N p m : ℕ, m < N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w : ℝ) (h : Scrim C W u ψ φ δ ζ r D)
variable (y : Coefficient (C.labels.level d) (C.side k p))
set_option quotPrecheck false
local notation "T" => C.path
local notation "F" => C.labels.level d
local notation "Y!" => C.localSection d
local notation "s!" => C.factory d N p
local notation "R" => C.path.rep N p

/-- The source coefficient at k, every intermediate step, the matching
primary at the prescribed stop, and the signed residual all share one
finite Wilson representation. -/
def Transmitted (stop : ℕ) (hr : C.ref d ≤ stop) (hs : stop ≤ m) (hk : m ≤ k)
    (hN : k ≤ N) (fee E : ℝ) (B : C.label d) : Prop :=
  let X := (h.costs.aim d N p (hr.trans (hs.trans (hk.trans hN)))).lyrics.choose
  let b := (C.factory d N p).terminal.symm B
  ∃ (A : ∀ i, Solo (C.labels.level d) C.path p i)
    (P : ∀ i, Coefficient (C.labels.level d) (C.side i p)) (g : ℕ → ℝ),
    A k = pair C.path N p X y fee ∧
      Challenge (C.localSection d) C.path N p C.params W X stop k A ∧
      (∀ i : ℕ, stop ≤ i → ∀ hi : i < k, Accord (C.localSection d) C.path N p X (ψ i)
        i (D N p i (hi.trans_le hN)) (A (i+1)) (A i)) ∧
      B = (C.factory d N p).terminal ((X.tone stop).index.symm (((A stop).bar X 0).x)) ∧
      (P k).x = y.x - (X.tone k).index b ∧
      (P stop).x = 0 ∧
      (∀ i, stop ≤ i → i ≤ k → (P i).x = (X.tone i).index ((A i).a - b)) ∧
      Club C.path C.params (C.localSection d) (ζ d) ψ m k N p (stair φ w m) D P g hN ∧
      (C.labels.level d).coeffSize ((X.tone k).index b) ≤ 2 * E ∧
      (P k).exponentialEntry 0 (C.localSection d) (R k) =
        y.exponentialEntry 0 (C.localSection d) (R k) +
          ((X.tone k).plays (-b)).exponentialEntry 0 (C.localSection d) (R k) ∧
      profile (R k).activities (P k).forced =
        profile (R k).activities y.forced + profile (R k).activities ((X.tone k).plays (-b)).forced

/-- A transmitted label at the radius used for the Gram estimate supplies
the complete calibrated matching certificate. -/
theorem matched (stop : ℕ) (hr : C.ref d ≤ stop) (hs : stop ≤ m) (hk : m ≤ k)
    (hN : k ≤ N) (fee E : ℝ) (B : C.label d)
    (hb : Transmitted C N k m p d (2*w) h y stop hr hs hk hN fee E B) :
    CalibratedCellMatch.Matched C N k m p d w h y (hr.trans hs) hk hN E B := by
  obtain ⟨_, P, g, _, _, _, _, _, _, _, hclub, hsize, hsingle, hforced⟩ := hb
  exact ⟨P, g, hclub, hsize, hsingle, hforced⟩

/-- A proposed column matches precisely when its calibrated coordinate
equals the actual transported primary at the chosen stop. -/
theorem primary_iff (stop : ℕ) (hr : C.ref d ≤ stop) (hs : stop ≤ m) (hk : m ≤ k)
    (hN : k ≤ N) (fee E : ℝ) (B : C.label d)
    (hb : Transmitted C N k m p d w h y stop hr hs hk hN fee E B) :
    let X := (h.costs.aim d N p (hr.trans (hs.trans (hk.trans hN)))).lyrics.choose
    ∃ A : ∀ i, Solo (C.labels.level d) C.path p i,
      A k = pair C.path N p X y fee ∧
      Challenge (C.localSection d) C.path N p C.params W X stop k A ∧
      (∀ i : ℕ, stop ≤ i → ∀ hi : i < k, Accord (C.localSection d) C.path N p X (ψ i)
        i (D N p i (hi.trans_le hN)) (A (i+1)) (A i)) ∧
      ∀ z : C.label d, B = z ↔
        ((A stop).bar X 0).x = (X.tone stop).index ((C.factory d N p).terminal.symm z) := by
  obtain ⟨A, _, _, hA, hC, hsteps, hB, _⟩ := hb
  refine ⟨A, hA, hC, hsteps, ?_⟩
  intro z
  constructor
  · intro he
    rw [← he, hB, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  · intro he
    rw [hB, he, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

include H
/-- The original constructed coefficient can be followed to the chosen
admitting stop. Its true primary there is pulled back by the same finite
calibrated coordinate map. -/
theorem transmit (stop : ℕ) (hr : C.ref d ≤ stop) (hs : stop ≤ m) (hk : m ≤ k)
    (hN : k ≤ N) (c₀ Q E : ℝ) (hχ : y.Format 0 C.params (R k))
    (hφ : y.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) c₀)
    (hq : (C.labels.level d).coeffSize y.x + c₀ ≤ Q)
    (hc : 4 * (1 + (C.path.levels.params k).columns) * Q ≤ E)
    (hx : 0 < Q) (hw : 0 < w)
    (ht : w * ‖alto T m d‖ * (E / gainChart T k m) ≤ ζ d m / 2) :
    ∃ B : C.label d, Transmitted C N k m p d w h y stop hr hs hk hN c₀ E B := by
    let X := (h.costs.aim d N p (hr.trans (hs.trans (hk.trans hN)))).lyrics.choose
    obtain ⟨_, hL, hp, _⟩ := (h.costs.aim d N p (hr.trans (hs.trans (hk.trans hN)))).lyrics.choose_spec
    have hstart := hr
    have hK := hr.trans hs
    have hM := hK.trans hk
    obtain ⟨A,hA,hx',hb,hc',hq',hp',h''⟩:= antilles Y! T N p C.params W X (D N p) ψ hr (hs.trans hk) hN H.wilson hL (fun i he hx=> ⟨h.listens d N p i (hr.trans he) (hx.trans_le hN),hp i (hr.trans he) (hx.trans_le hN)⟩) (y) hχ hφ hq h.costs.cost h.costs.back
    let b:= (A stop).a; let y':= -b; let Z:= Relay.dualize T N p X stop k A y'; let I:= X.tone k; let v:=(Z).voice k
    have hj :∀ i:ℕ,m ≤ i→i ≤ k→ w*0 ≤ ζ d i:=fun i hp _=> (mul_zero _).le.trans (h.grows d i (hK.trans hp)).le
    have he (i) (hi:m ≤ i) (ht:i≤k): Z.cost i+(F).coeffSize (Z.voice i).x ≤ E/gainChart T k i:= (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm ..).trans_le ((h'' i (hs.trans hi) ht).trans hc))
    let τ i:= march (fun _:Unit=>w) φ m i (); have h₀: Brine T m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    let c:=(C.path.levels.params k).columns; have hl :1 ≤ c:= (C.path.levels.params k).columns_ge; have hr:Q ≤ E:= le_trans (le_mul_of_one_le_left hx.le (show 1 ≤ 4*(1+(C.path.levels.params k).columns) by dsimp only [c] at hl; linarith only [hl])) hc
    have ht:= diet T d m φ (fun i=>ζ d i/2) w hw (fun i he=> (h₀.water i he).1) (fun i he=> le_trans (le_of_eq (b:=(φ i * ((C.S.block i).val:ℝ)^(d+1)* ζ d i)/2) (by  ring)) (div_le_div_of_nonneg_right (h.jump d i (hK.trans he)) (by norm_num))) k E (hx.le.trans hr) ht
    have hτ i (he:m ≤ i): 0 < τ i:= march_pos _ _ _ _ _ (fun _=>hw) h₀ i he _
    have stays(i)(hi:stop ≤ i)(ht:i ≤ k): (Z.voice i).Format 0 C.params (R i) ∧ (Z.voice i).remBound 0 (R i) (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (Z.cost i):= keys Y! T N p C.params X y' (hx'.chairs i hi ht) (hL.earned i (hstart.trans hi) (ht.trans hN))|>.2
    have hS : v.x=y.x-I.index b:=by refine ((hc' y').1).trans ?_; change y.x+I.index (-b)=_; rw [map_neg]; rfl
    have hpath (i : ℕ) (ha : stop ≤ i) (he : i ≤ k) :
        (Z.voice i).x = (X.tone i).index ((A i).a - b) :=
      (keys Y! T N p C.params X y' (hx'.chairs i ha he)
        (hL.earned i (hstart.trans ha) (he.trans hN))).1
    have hzero : (Z.voice stop).x = 0 := by
      rw [hpath stop le_rfl (hs.trans hk)]
      change (X.tone stop).index (b - b) = 0
      rw [sub_self, map_zero]
    refine ⟨(s!).terminal b, ?_⟩
    simp only [Transmitted, LinearEquiv.symm_apply_apply]
    refine ⟨A, Z.voice, Z.cost, hA, hx', hb, ?_, hS, hzero, hpath, ⟨fun i hi=> stays i (hs.trans hi),fun i hi h₁=> (mul_le_mul_of_nonneg_left (he i hi h₁) (mul_nonneg (hτ i hi).le (norm_nonneg _))).trans ((ht i hi).trans (div_le_self (h.grows d i (hK.trans hi)|>.le) (by norm_num))),fun i hi hm=> ⟨(hx'.ships i (hs.trans hi) hm).debt y',?_⟩⟩,?_,?_,?_⟩
    · rw [hq', LinearEquiv.symm_apply_apply]
    · obtain ⟨v,hv,hP⟩:=(hb i (hs.trans hi) hm).plays; exact ⟨v,hv,hP y'⟩
    · let l:= F; have hT:= he k hk le_rfl; rw [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at hT
      have hz: (F).coeffSize (I.index b) ≤ 2*E:=by
         have hP : I.index b=y.x - v.x:=by rw [hS]; abel
         rw [hP,sub_eq_add_neg]; apply (Size.add ..).trans; have he : (F).coeffSize (- v.x)=(F).coeffSize v.x:= by simp [Labels.Frame.coeffSize]
         rw [he]; linarith only [rem_nonneg ((stays k (hs.trans hk) le_rfl).2),hT,hq,rem_nonneg hφ,hr]
      exact hz
    · let t':= pair T N p X (y) c₀; let b':= t'.a; let Q':=t'.sil; let I':= X.tone k; have he :=hL.earned k hM hN; have hz(w):=(he.earns w).2; have hm:=duo_exp Y! hφ (hz (-b')); let q w:=(I'.plays w).exponentialEntry 0 Y! (R k); have hQ:IsLinearMap ℂ q:=expoLinear I'.plays I'.charge he.book hz
      have hs: Z.voice k=t'.bar X y':=show (A k).bar X y'=_ from by rw [hA]
      rw [hs,show t'.bar X y'=beside Q' (I'.plays (b'+y')) from rfl, show (beside Q' (I'.plays (b'+y'))).exponentialEntry 0 Y! (R k)=_ from duo_exp Y! ((presentation hχ hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+y'))]; change Q'.exponentialEntry _ _ _ + q (b'+y')=_; rw [show Q'.exponentialEntry _ _ _=_ from hm]; change _ + q (-b')+q (b'+y')=_+q y'
      rw [hQ.map_add, show q (-b')= -q b' from (IsLinearMap.mk' q hQ).map_neg b']; abel
    · let t':= pair T N p X (y) c₀; let b':= t'.a; let Q':=t'.sil; let I':= X.tone k; have he :=hL.earned k hM hN; have hz(w):=(he.earns w).2; have hm:=duo_profile hφ (hz (-b')); let q w:=profile (R k).activities (I'.plays w).forced; have hQ:IsLinearMap ℂ q:=inkL I'.plays I'.charge he.book hz
      have hs: Z.voice k=t'.bar X y':=show (A k).bar X y'=_ from by rw [hA]
      rw [hs,show t'.bar X y'=beside Q' (I'.plays (b'+y')) from rfl, show profile (R k).activities (beside Q' (I'.plays (b'+y'))).forced=_ from duo_profile ((presentation hχ hφ (he.earns (-b')).1 (hz (-b'))).2) (hz (b'+y'))]; change profile (R k).activities Q'.forced+q (b'+y')=_; rw [show profile (R k).activities Q'.forced =_ from hm]
      change (_+q (-b'))+q (b'+y')=_+q y'; rw [hQ.map_add,show q (-b')= -q b' from (IsLinearMap.mk' q hQ).map_neg b']; abel

section
open GridApprox
variable (L : Stock.Tabs C.path.levels) (J : ℕ) (hV : Stock.Tabs.opens C.path.levels 1 J m)
local notation "V" => Site (C.side J p)
local notation "Bt" => Stock.census V
local notation "o" => fun i => Mix.camp C p J i
local notation "u'" => hands C p J
local notation "α'" => march (fun _ : V => w) φ m k
variable (f : Config G (C.side N p) → ℂ)

include H L
/-- The full replicated physical source buys the very same transmitted
label at the chosen stop, with its quota and signed root-test price. -/
theorem paid_at_stop (stop : ℕ) (hr : C.ref d ≤ stop) (hs : stop ≤ m) (hk : m ≤ k)
    (hN : k < N) (hR : GridApprox.room C.path.levels J k (lensScope C d))
    (hC : ∀ b : C.label d, Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0)
      (C.O N p b 0))
    (hf : Continuous f)
    (ha : Interior ((center C.S p (hV.1.trans (hk.trans hN.le)) 0).chamber 0) f)
    (fee q E : ℝ) (hformat : y.Format 0 C.params (R k))
    (hrem : y.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) fee)
    (hq : (C.labels.level d).coeffSize y.x + fee ≤ q)
    (hc : 0 < q) (hE : 4 * (1 + (C.path.levels.params k).columns) * q ≤ E)
    (hw : 0 < w)
    (hP : 32 * (1 + (C.path.levels.params k).columns) * w * ‖alto T m d‖ *
      (E / gainChart T k m) ≤ ζ d m / 2)
    (hZ : Served (R k) (fun i => radiant (alto T k d) (u' i) (o k i)
      (y.exponentialEntry 0 Y! (R k))) (fun i => sunny (R k) y.forced (u' i) (o k i) (alto T k d))
      (gust T N p N (birth Bt (R N) (fun i => (center C.S p
        (hV.1.trans (hk.trans hN.le)) 0).copy i f)) k hN.le)
      (o k) α' (C.path.levels.budget k).supportExponent 1) :
    ∃ B : C.label d,
      Transmitted C N k m p d (2*w) h y stop hr hs hk hN.le fee E B ∧
      Next.UVStress.quota C d k N p B ≤ 2 * E ∧
      (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest
        (C.beta N p) (f - C.O N p B 0) ≤ 2 * (stakes C J m / w) := by
  let K := (C.path.levels.params k).columns
  have hK : 1 ≤ K := (C.path.levels.params k).columns_ge
  have hpos : 0 < E := (show 0 < 4 * (1 + K) * q by positivity).trans_le hE
  have hrad : 2 * w * ‖alto T m d‖ * (E / gainChart T k m) ≤ ζ d m / 2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (show 2 ≤ 32 * (1 + K) by linarith only [hK]) hw.le) (norm_nonneg _))
      (div_nonneg hpos.le (Real.exp_pos _).le)).trans hP
  obtain ⟨B, hB⟩ := transmit C N k m p d H (2*w) h y stop hr hs hk hN.le fee q E hformat hrem hq hE hc (by positivity) hrad
  refine ⟨B, hB, ?_⟩
  exact CalibratedCellMatch.prescribed_price C N k m p d H w h L J hV f y (hr.trans hs)
    hk hN hR hC hf ha E hpos hw hP B (matched C N k m p d w h y stop hr hs hk hN.le fee E B hB) hZ
end

end YM.Integration.TransmittedCellMatch
