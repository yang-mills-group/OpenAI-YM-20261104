import YM.Contacts.Allium.Beacon
import YM.Contacts.Bounty.Sequin
/-! # Caps timeline post charges. levels purchase flight as rOrder & thresholds only.
     Balancing roots not presumed globally, this stage ledger uniform in text resolution. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Allium
open Function Filter Finset Lattice Gauge RG Matrix Wilson Milling Pulse Loom Flux Revest PhysicalNext.Repeat Pressure Precision UVNext.CouplingReset
open Push.Uniform Pulse Spine Garf Steam House Exterior Model Arbor Province.Costing PertExtension.Series Radial
open Lintel Lintel.Angle Lintel.Plata Loom Junction Junction.Current Junction.Buyer Junction.Provision ConnectedActivityE6 Blaze Blaze.March Coat Meter Capture YM.Stationary Cove Lumen
open Resetter Sienna Next.Scheduling Barrage Barrage.Reserve Push.AbsoluteSums AnalyticBridge VerifiedReset Push.Uniform
open Tree Planned.JetPort
open scoped Topology ContDiff Classical NNReal BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {i j k n r:ℕ}{c c':Side} {X:G.ColorIndex} {a l σ C v Λ μ:ℝ}{t:Clip}
namespace Grant
open Clock Outlay
variable {Q:ℝ→ℝ} {A:Teller G} (X)
-- Package attain.Mask. use P≠ Tower.Pace. Weight combination.
variable (T:Patch) (z:ConnectedActivityE6.Target G A) (B: ConnectedActivityE6.Target.Order G v) (O: ChartRatio G)
variable (b b': Stage) (k n j:ℕ) (hO:LocalRatio O)
local notation "L" => T.L
abbrev padP (b:ℕ)(x:ℝ) :ℝ:= (Trio.most b x:ℝ)^4
def hearty (ℓ:ℝ) :ℝ:= -(ℓ+3)
abbrev Choiced (k:ℕ)(l:ℝ):Prop:= 2 ≤ k∧ 2 ≤ l ∧ race * (k+1) < hearty l ∧ 1+stashp*(k+3) < hearty l
-- Sesame.after.p0.price must correlate top U/.cover cleverly Stage param order. Need knobs Level.L.S.
open Bookend Item
structure Tenor (o:ℕ)(H:Before G b'.width b'.paths T.J A.bind (n+3))(j m r:ℕ)(R x l:ℝ):Prop where
   bench (U: StagePort G A O X k T.L b'.width b'.paths (H.tables b'.clip T) n)(hu: x=U.pearlRide) : Bookend.Rung T z B H U R b.width b.paths r (fun x=> Trio.paySide G T.L o x) → ∀ v', Bookend.Buys T z B U R (hearty l) v' -- z orders pre thresholds.O.Name
   lush (C:Item G) (hc:C.x=x)(Z: ℝ)(H':inBand x Z): Item.Bounded X b.clip b.width b.paths m j k n (padP o) C → Lens G T.L X x (hearty l) b.clip k n C Z
variable (hg:G.Simple)(hk:Choiced k l)(hn:k≤n)(hp:0 < μ)
include hg hO hk hn hp
lemma sponsors (o:ℕ) (H:Before G b'.width b'.paths T.J A.bind (n+3)) : ∃ r m,∀ᶠ x:ℝ in atTop, Tenor X T z B O b b' k n o H j m r μ x l:= by
   have hx:hearty l<0:= (by unfold hearty; linarith only [hk.2.1]); let Y:= (H.tables b'.clip T); let F(x):ℝ:=Trio.paySide G L o x; have hl:0< (k+1:ℝ):= (by positivity); obtain ⟨d,hρ,hv⟩:= exists_between hk.2.2.1; let q:= d/(k+1:ℝ); have hq : q*((k:ℝ)+1)= d:= by unfold q; field_simp;
   obtain ⟨d',he,hθ⟩:= exists_between hv; let p:= b.width; obtain ⟨r,hr⟩:= Bookend.commission (O:=O) (n:=n) (τ:=q) (v:=d') (a:=hearty l) (Q:=F) (M:= Y) (X:=X) T z B H hp hk.1 hn (Trio.circles ..) hg hO ((lt_div_iff₀ hl).mpr hρ) (div_neg_of_neg_of_pos (hv.trans hx) hl) (hq ▸ he) (hθ.trans hx) hθ b.paths (Classical.choice (BareRates.offered G b.width b.paths (n+3))) -- path
   have ht: Flat G (padP o):= Province.Costing.raised (Trio.rows G 1 o).2.2.2.uses 4 -- clarify
   obtain ⟨m,hm⟩:= Grant.flare k n X b.width b.paths b.clip T.L hk.1 hn hg ht hk.2.2.2 j -- args order
   refine ⟨r,m,(hr.and hm).mono fun x hx=>?_⟩; exact ⟨hx.1,fun c h x hz ht=> hx.2 c h ht x hz⟩
-- combines.Catalog true station. Pay needs monotone System lower x/y; choose after way. C.Contour.
omit hg hO hk hn hp
structure Arboric (m j r i o k n :ℕ)(x:ℝ)(ε:ℝ):Prop where -- some heights unneeded; combines estimates
    there: Province.System b x G (j+1) i
    market: Province.System b' (betaF G x T.L) G (j+1) i
    char : (i+1:ℝ)⁻¹ ≤ Tucks.ε₀
    bank : let y:= betaF G x T.L; lush x^ j ≤ y^((r+1:ℝ)⁻¹)
    added : m≤ i∧r≤ i∧ n+3≤ i
    horizon : Anthem.Steady G b x i k i ∧ Anthem.Steady G b' (betaF G x T.L) i k i
    sun : x≥1
    bait (β): β∈ Set.Icc (betaF G x T.L / 2) (2*betaF G x T.L) → inBand x β
    sale : x^(hearty ε) + (betaF G x T.L)^(hearty ε) ≤ Bounty.Trophy.Lore.veil ε (betaF G x T.L) -- placeholder formula
include hg hk
lemma clears (m r o:ℕ): ∃ i, ∀ᶠ x:ℝ in atTop, Arboric (G:=G) T b b' m j r i o k n x l:= by
    let i:=m+r+(n+3)+40; have he:(i+1:ℝ)⁻¹≤ Tucks.ε₀:= by unfold Tucks.ε₀; rw [one_div]; refine inv_anti₀ (by norm_num : (0:ℝ)<40) ?_; unfold i; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) m,Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) n]
    let d:=G.slopeConstant*Real.log (T.L.val:ℝ); let Y(x:ℝ):=betaF G x L; let e:= (r+1:ℝ)⁻¹; have hr:0<e:= (by unfold e; positivity); have hx(x:ℝ): x≤ Y x:= le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G L)
    have h:∀ᶠ x:ℝ in atTop,lush x^j≤ Y x^e:= by filter_upwards [faster (G:=G) (raised (lushPrice G) j) hr,eventually_ge_atTop (0:ℝ)] with x hv hm using (le_abs_self _).trans (hv.trans (Real.rpow_le_rpow hm (hx x) hr.le))
    have hY:= YM.Work.E09.betaF_growth G L; let β:=hearty l; let C:= (2:ℝ)^(-β); have hc:0<C:=Real.rpow_pos_of_pos zero_lt_two _; have hb:β<0:= by unfold β hearty; linarith only [hk.2.1]
    refine ⟨i,?_⟩
    filter_upwards [h, Province.revenue hg (j+1) i b, hY.eventually (Province.revenue hg (j+1) i b'), (Anthem.registry G k b), hY.eventually (Anthem.registry G k b'),eventually_gt_atTop d,eventually_gt_atTop (max 1 (1+C))] with x h hp hP hs hs' ht hh
    have hz:x≥1:= (le_max_left ..).trans hh.le; have h₀:0<x:= zero_lt_one.trans_le hz; let v:=Y x; have hv:0<v:= h₀.trans_le (hx x); have hv':0 ≤ v^β:= Real.rpow_nonneg hv.le _; have hA:v≤2*x:= (by change x+d ≤ _; linarith only [ht]); refine ⟨hp,hP,he,h,⟨by unfold i;omega,by unfold i; omega,by unfold i; omega⟩,⟨hs i i,hs' i i⟩,hz, fun β hp=> ⟨by linarith only [hp.1,hx x,h₀],by linarith only [hp.2,hA]⟩,?_⟩
    have hk:x^β ≤ v^β*C:= by
        have hx : v * (2:ℝ)⁻¹ ≤ x:= by norm_num; linarith only [hA]
        have ht:= Real.rpow_le_rpow_of_nonpos (mul_pos hv (inv_pos.mpr zero_lt_two)) hx hb.le; unfold C; rw [Real.rpow_neg_eq_inv_rpow]; exact ht.trans_eq (Real.mul_rpow hv.le (by positivity))
    have hM:C+1≤ x:= (by linarith only [lt_of_le_of_lt (le_max_right ..) hh]); change x^β+ v^β ≤ v ^ (-(l+2):ℝ); rw [show -(l+2)=β+1 from (by unfold β hearty; ring),Real.rpow_add hv,Real.rpow_one]; nlinarith only [hk, mul_le_mul_of_nonneg_left (hM.trans (hx x)) hv']
end Grant
end YM.Contacts.Allium
