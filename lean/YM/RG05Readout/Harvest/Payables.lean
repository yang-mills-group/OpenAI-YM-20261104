import YM.RG05Readout.Harvest.FrameReport
/-!
# Regulators scope. Rate purchases in s_m, not constant-Q claims
on close interval.U.Vore. Final Q needs precision transform invoices.
 No using larger derivatives than demanded.Run uniform after ℓ bound.
 -/
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
section rates
include hn
lemma amounts : Height C.S l T N 1:= hn.step (A!).fits.mesh
include hG hR ht hm
omit hn in
lemma unit_chart : RateIs l T r (-1):= measured_rate hG ht hm (hR.mono (fun _ hp=> hp.lit))
local notation "p!"=> fun i=> ‖premiums C s (m i) (n i+1) (r i)‖
omit [DecidableEq V] in
lemma premium_rate : RateIs l T p! 0:=by
   have hy:= amounts hn; have hx:= unit_chart hG ht hm hR -- args
   have hP (j:V) : RateIs l T (fun i=> ‖((r i:ℝ):ℂ)⁻¹^4 * gate C (m i) (n i+1) (s j)‖) 0:=by
      refine (((hx.inv.power 4).mul ((hy.mesh.power 4).mul ((hm.mesh.div hy.mesh).power (s j)))).swap (by norm_num)).congr ?_; filter_upwards [hx.1] with i hi; unfold gate; simp [Real.norm_of_nonneg hi.le,Real.norm_of_nonneg (C.S.a_pos _).le]
   refine ((RateIs.prod (S:=Finset.univ) (b:=fun _=>0) (fun i _=>hP i) ht).swap (by simp)).congr (Eventually.of_forall fun i =>(norm_prod ..).symm)
lemma gust_rate (hη:0<η) : RateIs l T (fun i=> gustCost C (N i) η (r i)) 0:=by
   exact (((RateIs.const ht (div_pos hη (show (0:ℝ)<16 by norm_num))).mul (unit_chart hG ht hm hR)).div ((amounts hn).mesh)).swap (by norm_num)
-- receive power.
local notation "x!"=>fun i=> earn s C (n i+1) o η (r i)
local notation "Y"=> (fun i=> taxLeaf C t' (m i) (n i) o s (r i) η)
local notation "V!"=> Fintype.card (Color V)
lemma x_rate (hη:0<η): RateIs l T x! 0:=by
    let c i:= gustCost C (N i) η (r i); have he:= gust_rate (C:=C) (n:=n) hG ht hn hm hR hη
    let w' i:= (C.S.a (N i)/r i)^(o+1); have h_w: RateIs l T w' 0:=(((amounts hn).mesh.div (unit_chart hG ht hm hR)).power (o+1)).swap (by norm_num); let C':=mintBase s 2 o
    have hx:0<redeem s o 2*2+1:=by linarith [redeem_pos s o 2 zero_le_two]
    have hc:0≤ C':=mul_nonneg (show 0≤ Nuclear.load V 2 from by unfold Nuclear.load; positivity) (bmint_pos s o)
    cases eq_or_lt_of_le hc with
    | inl h=>
       refine ((((RateIs.const ht hx).mul he).mul h_w).swap (by norm_num)).congr ?_
       exact Eventually.of_forall fun i=> by change _= (C'*_+_)*_; rw [←h,zero_mul,zero_add]
    | inr h=>exact ((((RateIs.const ht h).mul (he.inv.power ((∑ i:V,(s i+2))+4* Fintype.card V))).add ((RateIs.const ht hx).mul he) ht).mul h_w).swap (by norm_num)
lemma tax_rate (hη:0<η) (t' o:ℕ) : RateIs l T (fun i=> taxLeaf C t' (m i) (n i) o s (r i) η) 0:=by
    let a:ℝ:= (((Lattice.box t').card:ℕ):ℝ)^ Fintype.card V; have ht₁:0<a:=pow_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨_, Lattice.center_box _⟩)) _; have ht₂:0 < cutoffFee:= add_pos_of_pos_of_nonneg zero_lt_one ENNReal.toReal_nonneg
    exact ((((premium_rate s hG ht hn hm hR).mul (RateIs.const ht ht₁)).mul (RateIs.const ht ht₂)).mul (x_rate s hG ht hn hm hR hη)).swap (by norm_num)
noncomputable def mSeat (C:Family G) (s:V→ℕ)(B:ℝ)(m n o d t' ℓ k:ℕ)(η r:ℝ):= taxLeaf C t' m n o s r η * tender C m n d ℓ k (Fintype.card (Color V)) B
noncomputable def mBirth (C:Family G) (s:V→ℕ)(B:ℝ)(m n o d t' ℓ k:ℕ)(η r:ℝ)(j b:ℕ):= (Harvest.reimburses C n b d * (C.S.a j/C.S.a b)^4)*(taxLeaf C t' m n o s r η * thresholdC C (copperH C m n d ℓ k (Fintype.card (Color V)) B) j b n d)
local notation "Q₁"=> (fun i => mSeat C s (Q i) (m i) (n i) o d t' ℓ k η (r i))
local notation "Ω"=> (fun i => mBirth C s (Q i) (m i) (n i) o d t' ℓ k η (r i) j b)
include Yc hC hN hQ
lemma seat_rates (hB:4 < B)(hη:0 < η): RateIs l T (fun i=> rebases C (n i) (m i) d * Q₁ i) 0 ∧ RateIs l T Ω (-(d+1/3:ℝ)):=by
    obtain ⟨hE,hP,hy⟩:=paid_rates Yc hC hG ht hm hn hN hQ hR hB (k:=k) (v:=V!) (d:=d) (ℓ:=ℓ) Fintype.card_pos
    have hY:= tax_rate s hG ht hn hm hR hη t' o; have htP:RateIs l T (fun i=> rebases C (n i) (m i) d) 0:= (((amounts hn).mesh.div hm.mesh).power d).swap (by norm_num)
    have hz:= Shadow.focused ht hn hy b; refine ⟨(htP.mul (hY.mul hP)).swap (by ring),?_⟩
    have he := (RateIs.const ht (c:= (C.S.a b)^4) (pow_pos (C.S.a_pos _) _)).mul (((amounts hn).mesh.div (RateIs.const ht (C.S.a_pos b))).power d)
    exact (((he.mul (RateIs.const ht (pow_pos (div_pos (C.S.a_pos j) (C.S.a_pos b)) 4))).mul (hY.mul ((RateIs.const ht (Real.exp_pos (baseT C j b d))).div hz))).swap (by ring)) -- syntax parentheses
end rates
end YM.RG05Readout.Harvest
