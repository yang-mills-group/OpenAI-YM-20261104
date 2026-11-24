import YM.GradedFar.Wage
/-!
# Uniform (G.6) for the physical price hypothesis, even without receding-g interval yet

Various elementary cost commitments, e.g. poly log of *both* lengths, can be discharged here
on simultaneous true estimates. Doesn't use any compact formal comparison. This slightly cheaper
way to buy the requested size (than line 1623--25) doesn't conclude best bound on `D_v`:
some extra log powers, still no B spent. Normalize on basis program through every cap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Filter Finset Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2.GradedFar
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (Jp:ℝ→tower S)
    {I J:Type}[Fintype I][Fintype J](d:I→ℕ)(e:J→ℕ) (h:ℕ)
    {M δ:ℝ} (hm:0≤M)(hd:0<δ)
def Yν (v:Viewers F)(r s:ℝ)(o:E4)(x:I→E4)(y:J→E4)(u:WholeInput G d)(w:WholeInput G e):ℂ:=
  whole (spectator F v) (move o r x) (moved Jp r u) (move o s y) (moved Jp s w)
def Dν (v:Viewers F)(r s:ℝ)(o:E4)(y:J→E4)(w:WholeInput G e): Sec G h →ₗ[ℂ] ℂ :=
  upon (spectator F v) h o (move o s y) (moved Jp s w) ∘ₗ (assign Jp r h).toLinearMap
def Vν (r:ℝ)(o:E4)(x:I→E4)(u:WholeInput G d): Sec G h:= (assign Jp r h).symm (R.packet h (move o r x) (moved Jp r u) o)
lemma Dν_value (v:Viewers F)(r s:ℝ)(o:E4)(x:I→E4)(y:J→E4)(u:WholeInput G d)(w:WholeInput G e):
    Dν F Jp e h v r s o y w (Vν F R Jp d h r o x u) =
      upon (spectator F v) h o (move o s y) (moved Jp s w) (R.packet h (move o r x) (moved Jp r u) o):= by
  simp [Dν,Vν]

structure House (I J:Type)(d:I→ℕ)(e:J→ℕ)(h:ℕ) where
    scene : Purchase F I J
    u : WholeInput G d
    v : WholeInput G e
    m : Sec G h
local notation "Plot" => House F I J d e h
local notation "A" => F.sector.derivatives

def Ticket (M δ:ℝ)(s:ℝ)(z:Plot):Prop := Ready M δ s z.scene ∧ (∀ i,width (z.u i) ≤ 1) ∧
    (∀ i,width (z.v i)≤1) ∧ width z.m≤ 1

def powerLog (s:ℝ)(p:Plot):= duo s p.scene
local notation "L" => powerLog F d e h
local notation "T" => Ticket F d e h M δ
local notation "rdate" => fun (s:ℝ)(p:Plot)=>Purchase.logFrom (House.scene p)
local notation "sdate" => fun (s:ℝ)(_p:Plot)=>s
local notation "scene₀" => fun (s:ℝ)(p:Plot)=>House.scene p
include hm hd in
omit [Fintype I] [Fintype J] in
lemma content : Labor M δ trail T L sdate scene₀:= by
  have hR : ∀ᶠ r:ℝ in trail, ∀ p:Plot, T r p→ Ready M δ r p.scene := Eventually.of_forall fun r p he=>he.1
  have he : ∀ᶠ r:ℝ in trail, r≤1:= (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hA : ∀ r:ℝ, 0<r → r≤1 → 1 ≤ badge r:=fun r hr hz=> le_add_of_nonneg_right (neg_nonneg.mpr (Real.log_nonpos hr.le hz))
  have hx : ∀ᶠ r in trail, ∀ p:Plot,T r p → 1 ≤ badge (smallLength scene₀ r p) ∧ 1 ≤ badge r:=by
    filter_upwards [he,self_mem_nhdsWithin] with r hr (hp:0<r) p hz; obtain ⟨h₁,h₂,hQ⟩:= hz.1; exact
      ⟨hA _ h₁ (h₂.trans hr), hA r hp hr⟩
  refine ⟨⟨fun P h=> ?_, hx.mono (fun r hr x he=>
    ⟨(hr x he).1, le_mul_of_one_le_left (zero_le_one.trans (hr x he).1) (hr x he).2⟩)⟩,
    ⟨fun P h=>h.mono (fun _ hx _ _=>hx), hx.mono (fun r hr x he=>
    ⟨(hr x he).2, le_mul_of_one_le_right (zero_le_one.trans (hr x he).2) (hr x he).1⟩)⟩,
    Eventually.of_forall (fun _ _ _=> le_rfl),hR,hm,hd⟩
  obtain ⟨p,hp,H⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp h
  filter_upwards [(ge_mem_nhds hp).filter_mono nhdsWithin_le_nhds] with r hr z hz
  exact H ⟨hz.1.1, hz.1.2.1.trans hr⟩

variable (hG:G.Simple)(Ht:LogTrace F R.port) (Hw:∀ i,Coat F R Jp (d i))(Hw':∀ i,Coat F R Jp (e i))(Hh:Coat F R Jp h)
include hm hd hG Ht Hw Hw' Hh
set_option maxHeartbeats 600000 in
private lemma readyBank : ∃ k:ℕ,∃ b:ℝ,1≤b ∧ ∀ᶠ s in trail,∀ p:Plot, T s p →
    let z:=p.scene
    let r:=z.logFrom
    let Y(v:Viewers F):= Yν F Jp d e v r s z.center z.x z.y p.u p.v
    let D (v:Viewers F):= Dν F Jp e h v r s z.center z.y p.v
    let γ:=z.viewer
    let B:=Vν F R Jp d h r z.center z.x p.u
    let cost:= b * L s p^k
    ‖Y γ-D γ B‖ ≤ cost*(s+(r/s)^(h+1)) ∧ ‖Y γ - Y none‖ ≤ cost*s ∧ width B ≤ cost ∧
      ‖(D γ-D none) p.m‖ ≤ cost*s ∧ ‖D γ p.m‖ ≤ cost := by

  let l:= content F d e h hm hd
  let u(_:ℝ)(z:Plot):= z.u; let v(_:ℝ)(z:Plot):=z.v; let ξ(_:ℝ)(z:Plot):=z.m
  have hu:∀ᶠ r:ℝ in trail,∀ z i,T r z→ width (u r z i) ≤ 1:= Eventually.of_forall (fun _ _ i h=> h.2.1 i)
  have hv:∀ᶠ r:ℝ in trail,∀ z i,T r z→ width (v r z i) ≤ 1:= Eventually.of_forall (fun _ _ i h=> h.2.2.1 i)
  have hξ:∀ᶠ r in trail,∀ z,T r z→ width (ξ r z) ≤ 1:= Eventually.of_forall (fun _ _ h=>h.2.2.2)
  have H₀:= l.properO F (W:=fun _ _=>1) (Eventually.of_forall (fun _ _ _=> zero_le_one))
  obtain ⟨k,h0,h1,h2,h3,h4⟩:= (( (projection F R Jp l hG Ht Hw Hw' hu hv h).buy (l.properT F h)).and
       (((phases F R Jp l hG Ht Hw Hw' hu hv).buy (l.properS F)).and (((cap_price F R Jp l Ht Hw hu h Hh).buy H₀).and
         (((phaseStable F R Jp l hG Ht Hw' hv h Hh hξ).buy (l.properS F)).and
           ((homeStable F R Jp l hG Ht Hw' hv h Hh hξ).buy H₀))))).exists
  obtain ⟨b,hb,hA,hB,hC,hD,hE⟩:=((eventually_ge_atTop 1).and (h0.and (h1.and (h2.and (h3.and h4))))).exists
  refine ⟨k,b,hb,?_⟩
  filter_upwards [hA,hB,hC,hD,hE] with s Harr Harr' HC HD HE p hp
  specialize Harr p hp; specialize Harr' p hp; specialize HC p hp; specialize HD p hp; specialize HE p hp
  rw [mul_one] at HC HE
  dsimp only; rw [Dν_value]
  exact ⟨Harr,Harr',HC,HD,HE⟩

set_option maxHeartbeats 600000 in
theorem log6 :∃ C:ℝ,0<C ∧ ∃ k:ℕ, ∀ᶠ s in trail,∀ r o x y,0<r → r ≤ s → Setting M δ x y → r*M ≤ s*δ →
    ∀ (v:Viewers F) (u:WholeInput G d)(w:WholeInput G e), (∀ i,width (u i) ≤1) → (∀ i,width (w i)≤1) →
    let Y := fun v=>Yν F Jp d e v r s o x y u w
    let B := Vν F R Jp d h r o x u
    let D := fun v=> Dν F Jp e h v r s o y w
    let bill := C*(badge s*badge r)^k
    ‖Y v-D v B‖ ≤ bill*(s+(r/s)^(h+1)) ∧ ‖Y v‖+width B+rowPrice (D v) ≤ bill ∧
      ‖Y v-Y none‖ + rowPrice (D v-D none) ≤ bill*s := by
  let l:= content F d e h hm hd
  obtain ⟨k,b,hb,hA⟩ := readyBank F R Jp d e h hm hd hG Ht Hw Hw' Hh
  refine ⟨7*b*b, mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hb)) (zero_lt_one.trans_le hb), k+k, ?_⟩
  filter_upwards [hA,l.tiny.logs,(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with
    s Harr H Hs r o x y hp hs hx hz γ θ θ' hθ hθ'
  let p (v:Sec G h):= (⟨⟨x,y,o,r,γ⟩,θ,θ',v⟩:Plot); let cost:=b*(badge s*badge r)^k
  have hP (v:Sec G h)(hv:width v ≤ 1): T s (p v) :=⟨⟨hp,hs,hx,hz⟩,hθ,hθ',hv⟩
  let Y := fun v=> Yν F Jp d e v r s o x y θ θ'; let D := fun v=> Dν F Jp e h v r s o y θ'; let B:= Vν F R Jp d h r o x θ
  let q:=s+(r/s)^(h+1)
  have hT : T s (p 0):= hP _ (by rw [width_zero]; norm_num)
  have hu1 : 1 ≤ badge s * badge r:=H (p 0) hT
  have Hu:1≤cost:=one_le_mul_of_one_le_of_one_le hb (one_le_pow₀ hu1)
  have Hc:=zero_lt_one.trans_le Hu
  have H₁ : ‖Y γ-D γ B‖ ≤ cost*q := (Harr _ hT).1
  have H₂ : ‖Y γ-Y none‖ ≤ cost*s := (Harr _ hT).2.1
  have H₃ : width B ≤ cost := (Harr _ hT).2.2.1
  have H₄ : rowPrice (D γ-D none) ≤ cost*s := row_pay (mul_nonneg Hc.le (hp.le.trans hs))
    fun i hi=> (Harr (p i) (hP i hi)).2.2.2.1
  have H₅ : rowPrice (D γ) ≤ cost:= row_pay Hc.le fun i hi=> (Harr (p i) (hP i hi)).2.2.2.2
  have h₆ : ‖Y γ‖ ≤ cost*q + cost*cost := by
    calc
      _ = ‖(Y γ-D γ B) + D γ B‖:=by rw [sub_add_cancel]
      _ ≤ _:= (norm_add_le ..).trans (add_le_add H₁ ((row_le (D γ) B).trans
        (mul_le_mul H₅ H₃ (width_nn _) Hc.le)))
  have hs1 : 0 < s := hp.trans_le hs
  have hq0:0≤q:= by dsimp [q]; positivity
  have hq1:q ≤ 2:=by
    dsimp [q]; have hp':r/s ≤ 1:= (div_le_one hs1).mpr hs; linarith only [Hs,pow_le_one₀
      (div_nonneg hp.le hs1.le) hp' (n:=h+1)]
  dsimp only; rw [show 7*b*b*(badge s*badge r)^(k+k)=7*cost^2 from by dsimp [cost]; ring]
  exact ⟨ H₁.trans (mul_le_mul_of_nonneg_right (by nlinarith only [Hu]) hq0),
    (add_le_add (add_le_add h₆ H₃) H₅).trans (by nlinarith only [mul_le_mul_of_nonneg_left hq1 Hc.le, Hc,Hu]),
    (add_le_add H₂ H₄).trans (by rw [← add_mul]; exact mul_le_mul_of_nonneg_right (by nlinarith only [Hu]) hs1.le)⟩
end YM.Integration.GradedFar.Fork
