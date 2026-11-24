import YM.SignedWilsonExpansion.Purchase.HalfRoof
import YM.SignedWilsonExpansion.F9.Pictures
/-! # Audited panel aperture in ***physical*** scale, not on step-index mesh. -/
set_option autoImplicit false
set_option maxHeartbeats 690000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases.HalfRoof
open Wilson Gauge RG Asymptotics Lattice Set Filter Function Real Next.Rank Perch Commission WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer.Xa UVClock Schedules Metric Laurent
open XSpace XSpace.Cirrus XSpace.Expense
open scoped Topology Classical BigOperators
variable {G:Gauge} {M: Levels G}{n l c m k:ℕ}{i j:Fin n}{ι:Type*}
variable {x':Points n}{t d b:ℝ}{x:Fin n→Cover}{Z:Set (Points n)}
abbrev Garden (t:ℝ)(x: Fin n→Cover): Points n:= Extraction.tag t x
def Salon (F:Set (Points n))(b:ℝ):= ∀ x∈F,∀ i j, |x i j|≤ b
def Charter (F:Set (Points n))(d:ℝ):=∀ x∈F,spaced d x
lemma Salon.yield (F:IsCompact Z):∃ b:ℝ,1≤b ∧ Salon Z b:= by
    obtain ⟨b,hb⟩:= F.isBounded.subset_closedBall (0 : Points n); refine ⟨max b 1,le_max_right .., fun x hx i j=>?_⟩; exact (PiLp.norm_apply_le (x i) j).trans ((PiLp.norm_apply_le x i).trans ((mem_closedBall_zero_iff.mp (hb hx)).trans (le_max_left ..)))
lemma Charter.pivot (F:IsCompact Z)(W:Z⊆ conf n):∃ d:ℝ,0<d ∧ Charter Z d:=by
    rcases Z.eq_empty_or_nonempty with h|H; · rw [h]; exact ⟨1,zero_lt_one, fun x hx=>False.elim hx⟩
    have hc (i j:Fin n)(p:i≠j):∃ x∈Z, ∀ y∈Z,cubedist (x i) (x j) ≤ cubedist (y i) (y j):=by
        obtain ⟨x,v,w⟩:= F.exists_isMinOn H (f:=fun x : Points n=> cubedist (x i) (x j)) ( Continuous.continuousOn ( show Continuous (fun x: Points n=>cubedist (x i) (x j)) by unfold cubedist; fun_prop )); exact ⟨x,v,fun i hi=> w hi⟩
    have hq (i j:Fin n)(p:i≠ j){x:Points n}(hv:x∈Z):0<cubedist ( x i ) ( x j ):= dist_pos.mpr fun y=> p ((W hv) (( WithLp.equiv 2 _).injective y))
    let u: Filter ℝ:=𝓝[>] 0; have he :∀ᶠ d in u,∀ i j:Fin n,i≠j→ ∀ y∈Z,d≤cubedist (y i) (y j):= by
        refine eventually_all.mpr fun i=>eventually_all.mpr fun j=>?_ ; by_cases h:i=j; · subst i; simp
        obtain ⟨x,hx,hmin⟩:= hc i j h; exact ( eventually_nhdsWithin_of_eventually_nhds ( eventually_le_nhds ( hq i j h hx ) ) ).mono fun d hd _ z hz=> hd.trans (hmin z hz)
    exact ( he.and (self_mem_nhdsWithin) ).exists.imp (fun d ⟨p,t⟩=>⟨t,fun x hx i j q=> p i j q x hx⟩)
lemma money_split (F:IsCompact Z)(p:Z⊆ conf n): ∃ b d:ℝ,1≤b∧ 0<d ∧ Salon Z b∧ Charter Z d:= let ⟨b,h,k⟩:= Salon.yield F; let ⟨d,z,t⟩:=Charter.pivot F p; ⟨b,d,h,z,k,t⟩
lemma photon_off (u:0<t)(a:Axis): |Garden t x i a- Garden t x j a|= t* (( (x i-x j) a).natAbs:ℕ):=by
    change |t*(x i a:ℝ)-t*(x j a:ℝ)|=_; simp only [← mul_sub,abs_mul,abs_of_pos u]; congr 1; rw [← Int.cast_sub]; rw [Pi.sub_apply,←Int.cast_abs, ←Int.natCast_natAbs, Int.cast_natCast]
lemma axisLong (p:spaced d (Garden t x))(q:i≠j)(ht:0<t)(z:0<d) : ∃ a:Axis,d/t≤ (( (x i - x j) a ).natAbs : ℕ) :=by
    by_contra! u; apply not_lt.mpr (p i j q); apply (dist_pi_lt_iff z).mpr; intro a; rw [Real.dist_eq]; rw [photon_off ht]; rw [mul_comm]; exact (lt_div_iff₀ ht).mp (u a)
lemma angle_far (p: Charter Z d)(u:x'=Garden t x)(v:x'∈Z)(q:i≠j)(ht:0<t)(z:0<d) : d/t≤ ( Bank.terrain.gap (x i) (x j):ℝ):=by
    subst x'; obtain ⟨a,ha⟩:= axisLong (p _ v) q ht z; rw [Bank.terrain.swap]; exact le_trans ha (Nat.cast_le.mpr (Finset.single_le_sum (f:=fun l:Axis=> ((x i-x j) l).natAbs) (fun _ _=> Nat.zero_le _) ( Finset.mem_univ a )))
lemma seating (t:ℝ)(u:0<t)(h: m ≤ c)(z:0<d)(V:Charter Z d)(p:Garden (sizeT M t m) x∈ Z): Cowrie M m c (fun i=> pine M.S m i x) (SpanR M t d):=by
    refine ⟨fun i _ _=>reprClear M u z,fun i p _=>pine_next x p,fun i h q a b v=>?_⟩; exact angle_far V (stamp_pine x t u h).symm p v ( sizeT_pos _ u _ ) z
-- paid distances on orbitF from each other & self հայ
section orbit
local notation "Ω"=> roof M l c t
-- proof notation next issue
abbrev plait (M:Levels G)(l c:ℕ)(x:Cover): (orbitP M.S l c).Sites:= wrap (orbitP M.S l c).side (summit M l c+x)
lemma sourceL (u:0<t)(z: Salon Z b)(p:Garden (sizeT M t c) x∈ Z)(q:32*b< (roof M l c t u).size)(i:Fin n) (a:Axis): let n':Side:= (orbitP M.S l c).side; (32:ℤ)*|((x i a):ℤ)| < n'.val:=by
    intro n'; let F:=roof M l c t u; have h:=z (Garden ..) p i a; change |F.spacing * (x i a:ℝ)|≤ b at h; rw [abs_mul, abs_of_pos F.positive] at h
    exact_mod_cast (show 32 * |(x i a:ℝ)| < (n'.val:ℝ) from (lt_of_mul_lt_mul_left (a:=F.spacing) (b:=32*|(x i a:ℝ)|) (c:=(n'.val:ℝ)) (by change _ < F.size; nlinarith [F.positive]) F.positive.le)) -- method names test nlinarith [q] needs unfold
lemma plaitLift (u:0<t)(p: l ≤ c)(z: Salon Z b)(V: Garden (sizeT M t c) x ∈ Z)(h:32*b < (roof M l c t u).size) : lift (plait M l c (x i)-plait M l c (x j))= x i-x j ∧ lift (plait M l c (x i)- (-(plait M l c (x j))))= summit M l c+x i+ ( summit M l c+x j):=by
    constructor
    · refine lift_eq_iff.mpr ⟨(?_),fun a=>?_⟩; · unfold plait; rw [← map_sub,add_sub_add_left_eq_sub]
      have h1:=sourceL (i:=i) u z V h a; have h2:=sourceL (i:=j) u z V h a; change 32*|x i a| < ( (orbitP M.S l c).side.val:ℤ ) at h1; change 32*|x j a| < ( (orbitP M.S l c).side.val:ℤ ) at h2
      rw [Pi.sub_apply]; have L₀:= (orbitP M.S l c).side.pos; have hK(q:ℤ): |q|=max q (-q):=abs_eq_max_neg; rw [hK] at h1 h2; omega
    refine lift_eq_iff.mpr ⟨by unfold plait; rw [ sub_neg_eq_add, ← map_add ],fun a=>?_⟩; have h1:=sourceL (i:=i) u z V h a; have h2:=sourceL (i:=j) u z V h a; change 32*_ < (↑ (16*parcel M.S l c):ℤ) at h1 h2; let n':ℕ:= parcel M.S l c; have ht:0<n':= gain_pos ..; rw [Int.natCast_mul] at h1 h2; push_cast at h1 h2; simp only [ Pi.add_apply ]; rw [ summit, Pi.smul_apply ]; change -(↑(16*n'):ℤ)<2*(n' • (3:ℤ) + x i a + (n' • (3:ℤ)+x j a)) ∧ _
    have h': n' • (3:ℤ)=(n':ℤ)*3:= nsmul_eq_mul ..
    change _ ∧ 2*( n' • (3:ℤ)+x i a+(n' • (3:ℤ)+x j a))≤ (↑(16*n'):ℤ); simp_rw [h']; push_cast; change 32* _<16*(n':ℤ) at h1 h2; rw [abs_eq_max_neg] at h1 h2; omega
lemma twinS (u:0<t)(p: l ≤ c)(z: Salon Z b)(V: Garden (sizeT M t c) x ∈ Z)(h:32*b < (roof M l c t u).size) (x':Charter Z d)(p':0<d) (e:i≠j): d/(sizeT M t c) ≤ (separation (plait M l c (x i)) (plait M l c (x j)):ℝ):=by
    let P:=plait M l c ∘ x; obtain ⟨a,ha⟩:= axisLong (x' _ V) e ( sizeT_pos _ u _ ) p'; apply ha.trans (Nat.cast_le.mpr ?_); rw [← (plaitLift (i:=i) (j:=j) u p z V h).1]; exact Lattice.component_le _ _
lemma farS (u:0<t)(p: l ≤ c)(z: Salon Z b)(V: Garden (sizeT M t c) x ∈ Z)(h:32*b < (roof M l c t u).size) (i j:Fin n): (orbitP M.S l c).side.val/4≤ separation (plait M l c (x i)) (-plait M l c (x j)):=by
    let n':ℕ:= parcel M.S l c; let a:Axis:= 0; have h1:=sourceL (i:=i) u z V h a; have h2:=sourceL (i:=j) u z V h a; have hv:0<n':=gain_pos ..; let W(i):=plait M l c (x i); have ht:=Lattice.component_le (W i- -(W j)) a; rw [show lift _= _ from ( plaitLift u p z V h ).2] at ht; apply le_trans _ ht; change (16*n')/4≤ _; change 32*_ < (↑ (16*n'):ℤ) at h1 h2; push_cast at h1 h2; simp only [ Pi.add_apply ]; rw [summit, Pi.smul_apply]; change _≤ Int.natAbs ( n' • (3:ℤ)+x i a+(n' • (3:ℤ)+x j a)); simp_rw [nsmul_eq_mul]; rw [abs_eq_max_neg] at h1 h2; omega
end orbit
open Stair StationA WardBin
variable {l c:ι→ℕ}{ρ B:ι→ℝ} {Ω₁ μ_: Set (Points (n+1))} {L:Filter ι} {W':Initialize G}{T:Set (Points n)}
variable (v:∀ i,0<ρ i)(hw:l ≤ᶠ[L] c)(p:Stretched L (fun i=> roof M (l i) (c i) (ρ i) (v i)))
local notation "cosy"=>(fun i=> roof M (l i) (c i) (ρ i) (v i))
include p v hw
open Labels
variable (Ω:IsCompact Ω₁)(t':Ω₁ ⊆ conf _)(R:∀ h,Rays G h W'.hol)(F:Frames G)
variable {h_:ℕ}
include Ω t'
lemma Cape.pearl (x:ι→Fin (n+1)→Cover)(u:∀ᶠ i in L, Garden (hereD M ρ c i) (x i) ∈ Ω₁)(q:h_≤k): ∀ᶠ i in L,∃ b:ℕ,Stair.ReservesA (W'.tree (cosy i).p) F W'.surveys R h_ k b (fun j=> summit M (l i) (c i)+ x i j) :=by
    obtain ⟨b,d,bh,hd,hb,dd⟩:= money_split Ω t'; let τ := 32*b; let Q:= (StationA.casingP R h_).choose; let T':= (StationA.light_cap W'.surveys R F h_ k q).choose; let K:= 2*Q+T'
    let Y' := cosy; let f(i):= (orbitP M.S (l i) ( c i )).side; let Y:= fun i=> f i |>.val; have hx: Tendsto Y L atTop:=tendsto_atTop.mpr fun k=> (p.horizon.eventually_ge_atTop (k:ℝ)).mono fun i t=> Nat.cast_le.mp t; have ht:Tendsto (fun i=>d/ hereD M ρ c i ) L atTop:= ( (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨p.endpt, Eventually.of_forall fun i=>(cosy i).positive⟩)).const_mul_atTop hd ) -- lemma
    filter_upwards [hx.eventually_ge_atTop ( 4*(K+1)),ht.eventually_gt_atTop (K:ℝ), p.width.eventually_gt_atTop τ,hw,u] with i hv hξ hu hl hx0
    have hs : Q ≤ Y i:=by unfold K at hv; omega
    have he (j z):K < separation ((plait M (l i) (c i)) (x i j)) (-(plait M (l i) ( c i ) (x i z))):= by have hp:= farS ( v i ) hl hb hx0 hu j z; change _≤ _ at hv; exact lt_of_lt_of_le (b:=Y i/4) ( Nat.lt_iff_add_one_le.mpr ( Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by linarith) )) hp
    refine ⟨Q,reserves_bill _ _ _ _ _ q ( (StationA.casingP ..).choose_spec Q le_rfl _ hs ) (?_) (?_)⟩
    · intro j; exact lt_of_le_of_lt (Nat.le_add_right ..) (he j j)
    intro j k hk; have hk' : Q+T' ≤ K:=by unfold K; omega
    exact ⟨lt_of_le_of_lt hk' (Nat.cast_lt.mp ( lt_of_lt_of_le hξ ( twinS (v i) hl hb hx0 hu dd hd hk ) )), lt_of_le_of_lt hk' (he j k)⟩
end YM.SignedWilsonExpansion.Purchases.HalfRoof
