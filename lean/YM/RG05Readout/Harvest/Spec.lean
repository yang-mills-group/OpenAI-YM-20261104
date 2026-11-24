import YM.RG05Readout.Harvest.Reader
/-! Supply licenses on ALL admitted regulators by taking illumination after
 reference.Shape.Report carried with subpolynomial size on THESE apertures,
 exponential error for normalized replicas.With arbitrarily many apertures
 admitted sequentially on SAME C/data. Read shifts/raw pelvis. Does not fund
 near-coincidence geometry.δ.Rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Harvest
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G}{ι: Type} {l:Filter ι}{n m:ι→ℕ}{d:ℕ}
    {j b k ℓ t t' o:ℕ}{e B η R:ℝ}{Q T r:ι→ℝ}{V:Type}[Fintype V][DecidableEq V] (s:V→ℕ)
set_option quotPrecheck false
local notation "A"=> C.S.a
local notation "A!"=> C.path.levels
local notation "N"=> fun i=> n i+1
variable {D:Address.Rail C}{ψ:ℕ→ℕ}{w:Worth}(Yc:OPE.Package C w ψ D)(hC:Storage C D)(hS:Cater C D)(hG:G.Simple)
variable (ht:Tendsto T l atTop)(hn:Height C.S l T n 1)(hm:Height C.S l T m 1)(hQ:RateIs l T Q 0) (hN:∀ᶠ i in l,n i+1 < m i) (hR:∀ᶠ i in l,CaptureW C (n i+1) (m i) (r i) B)
    (hB:4 < B)
lemma radius_paid (C:Family G) (j p:ℕ): C.S.a j ≤ 1 ∧ 1 ≤ C.S.radius p:=by
     constructor; · rw [← C.S.a_zero]; exact C.S.strictAnti.antitone (Nat.zero_le j)
     unfold Schedule.radius; rw [le_div_iff₀ (by norm_num:(0:ℝ)<2),one_mul]
     let x:= (C.S.side 0 p).val; have he: x=(C.S.period p).val:=by simp [x,Schedule.side]
     exact_mod_cast he ▸ (le_trans (show 2 ≤ (4:ℕ) by decide) (Nat.le_of_dvd (show 0<x from (C.S.side 0 p).property) (C.S.side_four 0 p)))
include ht hm hn hQ hN hR hB Yc hC hG
local notation "C!"=> Fintype.card (Color V)
lemma dispenses (hη : 0<η)(hv:η≤1)(h'R:0≤ R)(j:ℕ)(he:R+2 ≤ t')(hz:2*t' ≤ t)
    (hX:∀ i:V,s i ≤ ℓ)(hd:d ≤ ℓ)(hb:∀ᶠ b in atTop,∀ i,b ≤ i→ Pin C i d)(hc:∀ᶠ b in atTop, Stock.Tabs.opens C.path.levels (bumper (2*t)) j b)(hu:∀ᶠ b in atTop, Warm C b (ℓ+1) k):
    ∀ᶠ b in atTop, ∀ᶠ i in l, ∀ p:ℕ, Right C p (n i) (m i) j b k ℓ t t' d s (r i) R (C.S.a j/8) η (2*t') (Q i):=by
      obtain ⟨-,hP,hf⟩:= paid_rates Yc hC hG ht hm hn hN hQ hR hB (k:=k) (v:=C!) (d:=d) (ℓ:=ℓ) Fintype.card_pos
      have h':= unit_chart hG ht hm hR
      let x:ℝ:= C.S.a j; let K:=16*(1+t+Scope C ℓ); have hx:0<x:= C.S.a_pos _; have hA : Tendsto (fun i=> A (N i) * (R+2)) l (𝓝 0):=by simpa only [zero_mul,Function.comp_apply] using ((C.S.shrinks.comp ((amounts hn).grows)).mul_const (R+2))
      filter_upwards [eventually_ge_atTop j,hb,hc, C.S.shrinks.eventually (gt_mem_nhds (by positivity:0<x/8)), (show Tendsto (fun i=>K*C.S.a i) atTop (𝓝 0) by simpa only [mul_zero] using C.S.shrinks.const_mul (↑K:ℝ)).eventually (gt_mem_nhds hx)] with b hj hb hc hx' hx''
      have hk:= canKnock hG hm hn hN hR hB b s hX hd (t:=t) (a:=(2:ℝ)*t') (by exact_mod_cast hz) hu (by positivity) (show 0<η/2 from by positivity)
      filter_upwards [hN,hP.1,hf.1,h'.1, hk, hn.grows.eventually_ge_atTop b,hR,hn.grows.eventually (C.path.levels.fits.deep.eventually_ge_atTop (d+3)),hQ.1,hA.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with i hi hp hh hv' hk hK hR h_J hu hl p
      let Z:= C.S.toDepth hj p; have hL: (K:ℝ)*C.S.a b<x:=hx''; have htP: K≤ Z.count.val:=by
          have he:C.S.a b* Z.count.val=x:= C.S.embeds_scale _
          have hv: (K:ℝ)≤ Z.count.val:=le_of_mul_le_mul_left (show C.S.a b*K ≤ C.S.a b* Z.count.val from by rw [he,mul_comm]; exact hL.le) (C.S.a_pos _); exact_mod_cast hv
      have ha := hR.nearF; let a:= A (N i); have hh₀:r i *R+2*a ≤ a*t':=by have hw:= mul_le_mul_of_nonneg_left he (C.S.a_pos (N i)|>.le); linarith only [mul_le_mul_of_nonneg_right ha h'R,hw]
      have hR':r i*R+2*a <1/2:=by linarith only [mul_le_mul_of_nonneg_right ha h'R,show a*(R+2)<1/2 from hl]
      have htV: C.S.a b < x/8:= hx'
      obtain ⟨htb,hσ⟩:= radius_paid C j p; have htb:x≤ 1:= htb
      refine ⟨hu,hv',ha,hK,hi,h_J,hj,htP,hc,hb,?_,hη,hv,hh₀,hh,hp.le,?_,?_,?_,?_⟩
      · intro u ho f hx ht_; rw [show r i*η/2=η/2*r i by ring] at hx ⊢; refine hk p _ f ?_ (fun j m hm x hx=>?_) hx
        · intro w; have he:= (Ribbons.normC C (N i) p (u w)).2; have hZ: (separation (u w) 0:ℝ)≤ t':= by exact_mod_cast ((show ∀ j:V, separation (u j) 0 ≤ t' from (Finset.mem_filter.mp ho).2) w)
          exact he.trans (le_trans (mul_le_mul_of_nonneg_left hZ (mul_nonneg zero_le_two (C.S.a_pos _).le)) (le_of_eq (by ring)))
        · simpa only [one_pow,one_mul] using ht_ j _ hm x
      all_goals first|exact lt_of_lt_of_le hR' (le_trans (show (1/2:ℝ)≤1 by norm_num) hσ)| linarith only [htb,hσ,hR',htV,(show 0<a from C.S.a_pos (N i)),hx]
omit ht hm hn hQ hN hR hB
local notation "U₁"=> V
-- combine reserves without awaiting analytic iteration
lemma elder (Y:UV.Lacquer C D): ∃ B':ℕ→ℕ→ℝ,∀ (j t ℓ d:ℕ), (∀ᶠ b:ℕ in atTop, (∀ i,b ≤ i→ Pin C i d)∧ Stock.Tabs.opens C.path.levels (bumper (2*t)) j b∧ Awake D B' b d) ∧ ∃ k,∀ᶠ n in atTop,Warm C n (ℓ+1) k:=by
   obtain ⟨B,h⟩:= reserves Yc hC hG Y; refine ⟨B, fun j t ℓ d=> ?_⟩
   exact ⟨(h d t j).mono fun i hi=> ⟨hi.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2⟩,warmups (C:=C) hC Yc hG (ℓ+1)⟩
end YM.RG05Readout.Harvest
