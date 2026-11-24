import YM.SignedWilsonExpansion.Purchase.China
import YM.ForFlash.MS.Layout

/-!
# Epoch geometry

Coordinates in probing length and `PayD` polynomial in β (`B`); separated
by a uniform gap also in probing length. No tightening the Side after choosing
the layout: use the signed Epoch size. The collar estimate below is the
geometric part for charging the polynomial-layout F9 estimator.
Adapted from Purchase/{HalfRoof,China}.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.HalfRoof
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa UVClock Schedules Metric Laurent
open XSpace XSpace.Cirrus XSpace.Expense
open scoped Topology Classical BigOperators
variable {G:Gauge} {M: Levels G}{n l c m k:ℕ}{i j:Fin n}{ι:Type*}
variable {x':Points n}{t d b:ℝ}{x:Fin n→Cover}{Z:Set (Points n)}

/-- No arbitrary growing mesh-period interchange. This is the power-bounded
    extension of the analyst's `pad` request. -/
structure InWidth (d b:ℝ)(x:Points n):Prop where
   gap : spaced d x
   far : ∀ i:Fin n, ‖WithLp.ofLp (x i)‖≤ b

variable {l c w:ι→ℕ}{ρ B:ι→ℝ} {pF : ι→Points n} {L:Filter ι}
def InBWidth (d a:ℝ)(B:ι→ℝ)(x:ι→Points n)(L:Filter ι):Prop :=
    ∀ᶠ i in L, InWidth d (payD B a i) (x i)
structure MovesIn (L:Filter ι)(B:ι→ℝ)(x:ι→Points n):Prop where
    places : ∃ a d:ℝ, 0<a ∧ 0<d ∧ InBWidth d a B x L

lemma MovesIn.comp {J:Type*}{F:Filter J}{f:J→ι}(p:MovesIn L B pF)(hf:Tendsto f F L) : MovesIn F (B∘f) (pF∘f):=by
    obtain ⟨a,d,v,u,h⟩:=p.places; exact ⟨a,d,v,u,hf.eventually h⟩
lemma MovesIn.tee {z:ι→Points n} (p:MovesIn L B pF)(ht:pF=ᶠ[L] z): MovesIn L B z:=by
    obtain ⟨a,d,v,u,h⟩:= p.places; exact ⟨a,d,v,u,(h.and ht).mono fun i hi=> hi.2▸ hi.1⟩
lemma InWidth.salon {x:Points n}(p:InWidth d b x) : Salon {x} b:= by
    rintro t h y j; rw [mem_singleton_iff.mp h]; exact (norm_le_pi_norm _ j).trans (p.far y)
lemma InWidth.charter {x:Points n}(p:InWidth d b x) : Charter {x} d:= fun t h=> mem_singleton_iff.mp h ▸ p.gap -- check dir
lemma InWidth.all (h:Salon Z b)(hp:Charter Z d){x:Points n}(v:x∈Z): InWidth d b x := by
    refine ⟨hp _ v, fun i=>?_⟩; let f:=WithLp.ofLp (x i); exact (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans (h x v i (0:Axis)))).mpr fun j=> h _ v _ _

lemma InWidth.more {x:Points n}{u v:ℝ}(p:InWidth d b x) (q:u≤d)(r:b≤v): InWidth u v x := ⟨fun i j h=> q.trans (p.gap i j h), fun i=> (p.far i).trans r⟩
lemma InBWidth.compact (L0:Rise B L)(c:IsCompact Z)(v:Z⊆conf n)(p:∀ᶠ i in L,pF i∈ Z)(a:ℝ)(w:0<a):∃ d:ℝ,0<d ∧ InBWidth d a B pF L:=by
    obtain ⟨b,d,hb,hd,c,h⟩:= money_split c v; exact ⟨d,hd,(p.and ((payD_looms L0 w).eventually_ge_atTop b)).mono fun i hi=> ( InWidth.all c h hi.1 ).more le_rfl hi.2 ⟩
lemma InWidth.fitsForFlash (f:Sample n)(p:welcome f)(v:InWidth d (b*f.F.spacing⁻¹^k) (familiar f)): FVA2.Arrival.Schedule.FitsWidthForFlash d b k f:=
    ⟨p, fun x y h=> by simpa only [spaced,cubedist,dist_eq_norm] using! v.gap x y h, fun x=> v.far x⟩

variable (u:Rise B L)
include u
local notation "pD"=>payD B
lemma Eclipse.forFlash {x:ι→ℝ}(v:Eclipse L B x)(a:ℝ)(c:ℝ) : ∀ᶠ i in L,c*payD B a i < x i:=by
   let k:= payD B (a+1); filter_upwards [v.tall (a+1),(payD_looms u zero_lt_one).eventually_gt_atTop c] with i hi hv
   refine lt_of_lt_of_le ?_ hi; rw [ payD_add,Pi.mul_apply,mul_comm c ]; exact mul_lt_mul_of_pos_left hv (pay_pos ..)

open Stair StationA WardBin Labels
variable (v:∀ i,0<ρ i)(hw:l ≤ᶠ[L] c)(p:Stretched L (fun i=> roof M (l i) (c i) (ρ i) (v i)))
   (U0:Eclipse L B (fun i=> (roof M (l i) (c i) (ρ i) (v i)).size))
local notation "cosy"=>(fun i=> roof M (l i) (c i) (ρ i) (v i))
include p v hw U0
variable {W':Initialize G}(R:∀ h,Rays G h W'.hol)(F:Frames G) {h_:ℕ}
-- Adapted from China.Cape.pearl
set_option maxHeartbeats 620000 in
lemma Cape.pearlForFlash (x:ι→Fin (n+1)→Cover)(u':MovesIn L B (fun i=>Garden (hereD M ρ c i) (x i)))(q:h_≤k): ∀ᶠ i in L,∃ b:ℕ,Stair.ReservesA (W'.tree (cosy i).p) F W'.surveys R h_ k b (fun j=> summit M (l i) (c i)+ x i j) :=by
    obtain ⟨a,d,ha,hd,pw⟩:= u'.places; let Q:= (StationA.casingP R h_).choose; let T':= (StationA.light_cap W'.surveys R F h_ k q).choose; let K:= 2*Q+T'
    let f(i):= (orbitP M.S (l i) ( c i )).side; let Y:= fun i=> f i |>.val; have hx: Tendsto Y L atTop:=tendsto_atTop.mpr fun k=> (p.horizon.eventually_ge_atTop (k:ℝ)).mono fun i t=> Nat.cast_le.mp t; have ht:Tendsto (fun i=>d/ hereD M ρ c i ) L atTop:= ( (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨p.endpt, Eventually.of_forall fun i=>(cosy i).positive⟩)).const_mul_atTop hd )
    filter_upwards [hx.eventually_ge_atTop ( 4*(K+1)),ht.eventually_gt_atTop (K:ℝ), Eclipse.forFlash u U0 a 32,hw,pw] with i hv hξ hu hl hx0
    have hs : Q ≤ Y i:=by unfold K at hv; omega
    have he (j z):K < separation ((plait M (l i) (c i)) (x i j)) (-(plait M (l i) ( c i ) (x i z))):= by have hp:= farS ( v i ) hl hx0.salon (mem_singleton _) hu j z; change _≤ _ at hv; exact lt_of_lt_of_le (b:=Y i/4) ( Nat.lt_iff_add_one_le.mpr ( Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by linarith) )) hp
    refine ⟨Q,reserves_bill _ _ _ _ _ q ( (StationA.casingP ..).choose_spec Q le_rfl _ hs ) (?_) (?_)⟩
    · intro j; exact lt_of_le_of_lt (Nat.le_add_right ..) (he j j)
    intro j k hk; have hk' : Q+T' ≤ K:=by unfold K; omega
    exact ⟨lt_of_le_of_lt hk' (Nat.cast_lt.mp ( lt_of_lt_of_le hξ ( twinS (v i) hl hx0.salon (mem_singleton _) hu hx0.charter hd hk ) )), lt_of_le_of_lt hk' (he j k)⟩
end YM.SignedWilsonExpansion.Purchases.HalfRoof
end
