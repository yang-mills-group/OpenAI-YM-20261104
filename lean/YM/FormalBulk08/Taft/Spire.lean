import YM.FormalBulk08.Taft.Shift
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Taft
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Avenue Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{I:Type}{W:Lab G K I}{ρ:ChartRatio G}{E e r d D R n:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
variable (q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)
abbrev viaduct (K:KernelChoices)(W:Lab G K I)(a:hue G)(F:Frame G d)(ρ:ChartRatio G)(T:SectionData F)(hv:d+1≤D)(x:I)(m:ℕ): Matrix (Letter F) (Letter F) ℝ:= fun i j=> aura fun n=> bridge K W a F ρ T hv x n m i j
lemma mob_found {Z:Matrix (Letter F) (Letter F) ℝ} (h:Mob F Z): Found (slots F) (Pose.weight F) (tag Z) 1:= by
    refine ⟨fun i j z=>?_,fun _=>one_pos,fun i j he hz=>?_⟩
    · rw [show coeff 0 (tag Z i j)=Z i j from coeff_zero_C _]; by_contra hx; have hv:= h.raiseS i j hx (fun he=> Nat.lt_irrefl _ (he ▸ z));omega
    rw [show coeff 0 (tag Z i j)=Z i j from coeff_zero_C _]; by_cases hp:i=j
    · subst i; rw [if_pos rfl,h.unit];rfl
    rw [if_neg hp]; exact Classical.byContradiction fun ht=> hz.not_gt (h.raiseS _ _ ht hp).2
include q u h a hs ht hb hr
lemma health (i j:Letter F): Pact (aurum W) (purseR targetPower) (fun x=>bridge K W a F ρ T q.horizon x.a x.top x.b i j) (fun x=>bridge K W a F ρ T q.horizon x.a x.summit x.b i j):= by
    exact (tracing (q.shift (Dove.Lab.Test.x (W:=W))) (W.observed u _) h a hs ht hb hr (Dove.Lab.Test.ND W) (Dove.Lab.Test.MD W) (Dove.Lab.Test.next) i j).link meshPoint.role
lemma harmony_pay (i j:Letter F): let Z:=viaduct K W a F ρ T q.horizon
    Pact (aurum W) (purseR targetPower) (fun x=>bridge K W a F ρ T q.horizon x.a x.top x.b i j) (fun x=>Z x.a x.b i j) ∧ ∀ x:Leaf W.scrolls, Ends (fun n=>bridge K W a F ρ T q.horizon x.a n x.b i j) (Z x.a x.b i j):= by
    intro Z; let f(x:Leaf W.scrolls)(n):=bridge K W a F ρ T q.horizon x.a n x.b i j; let τ:=chron W.scrolls
    obtain ⟨hz,hP,B,⟨K,r,b,H⟩,k,Y⟩:= health q u h a hs ht hb hr i j; obtain ⟨U,p,X,hU⟩:=hz; let q':=fun x=> K*(τ.day x)^r; have he(x:Leaf W.scrolls)(n)(hx:x.b≤n)(m)(hm:n ≤ m): |f x n-f x m| ≤ q' x *North.fare_n x n:= by let i':meshPoint W:=⟨x,n,m,hx,hm⟩; exact (Y i').trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (H i')) (ratioR_pos ..).le)
    have hv x: Ends (f x) (aura (f x)):= aura_pays (f x) (fun n=>q' x*fare_n x n) (North.fare_fin_lt x (q' x)) ((eventually_ge_atTop x.b).mono fun n hn=>he x n hn); refine ⟨⟨⟨U,p,X,hU⟩,⟨U,p,X, fun x=>?_⟩,⟨_,(soft_coin _ K).times ((soft_day (aurum W)).pows r),fun x=>mul_nonneg b (pow_nonneg ((aurum W).good _) _),fun x=>?_⟩⟩,hv⟩
    · exact le_of_tendsto ((hv x.toLeaf).abs) ((eventually_ge_atTop x.b).mono fun k hk=> hU (⟨x.toLeaf,k,k,hk,le_refl k⟩:meshPoint W))
    exact le_of_tendsto ((tendsto_const_nhds.sub (hv x.toLeaf)).abs) ((eventually_ge_atTop x.top).mono fun i hi=> he x.toLeaf x.top x.wing i hi)
lemma phases (x:Leaf W.scrolls): Mob F (viaduct K W a F ρ T q.horizon x.a x.b):= by
    let A:= viaduct K W a F ρ T q.horizon x.a x.b; refine ⟨fun i=> ?_,fun i j he hz=>?_⟩
    · exact tendsto_nhds_unique ((harmony_pay q u h a hs ht hb hr i i).2 x) (tendsto_const_nhds.congr' ((eventually_ge_atTop x.b).mono fun k hk=> ((laden q h a hs ht hb _ _ _ x.zone hk).unit i).symm))
    obtain ⟨Z,hz'⟩:= ((((harmony_pay q u h a hs ht hb hr i j).2 x).eventually_ne he).and (eventually_ge_atTop x.b)).exists
    exact (laden q h a hs ht hb _ _ Z x.zone hz'.2).raiseS _ _ hz'.1 hz
lemma back_bill (i j:Letter F): Pact (aurum W) (purseR targetPower) (fun x=>(bridge K W a F ρ T q.horizon x.a x.top x.b)⁻¹ i j) (fun x=>(viaduct K W a F ρ T q.horizon x.a x.b)⁻¹ i j):= by
    have he (z:meshPoint W):= mob_found (laden q h a hs ht hb _ _ _ z.zone z.wing); have hx (z:meshPoint W):= mob_found (phases q u h a hs ht hb hr z.toLeaf)
    have hp(i j:Letter F):Priced (aurum W) (purseR targetPower) (fun z=>tag (bridge K W a F ρ T q.horizon z.a z.top z.b) i j) (fun z=> tag (viaduct K W a F ρ T q.horizon z.a z.b) i j) 0:= by
       intro t ht'; replace ht':t=0:=by omega
       subst t; simp_rw [tag, RingHom.mapMatrix_apply, Matrix.map_apply, coeff_zero_C]; exact (harmony_pay q u h a hs ht hb hr i j).1
    have ht:= prize_back he hx (fun i=>soft_coin _ (1:ℝ)⁻¹) hp i j 0 (Nat.zero_le _); simp_rw [←(tagBack (he _)).2,← (tagBack (hx _)).2,tag,RingHom.mapMatrix_apply,Matrix.map_apply,coeff_zero_C] at ht; exact ht
end YM.FormalBulk08.Taft
