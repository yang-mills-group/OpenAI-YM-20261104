import YM.FVA2.Anti
/-! # DR and position sign coherence. Flipping connection and ghost-pole variables. -/
noncomputable section
set_option autoImplicit false
namespace YM.MS.Reed
open Filter Topology Set Function MeasureTheory Finset Arc
open Plane Lifting Landau Landau.Detect Koszul Book Book.Convolve Book.Program Dock
open Pearl Train Outlook Mach Arts Arts.Spin Halo Garment Hem Rock Rock.Path Alps Rock.Oceans
open Plane.Wire Arts.Pilot Color Flux Shine Hem.Mell Garment.Wick
open scoped Topology Classical ContDiff
variable {G:Gauge} {n h:ℕ}{t r:ℤ}{z:ℂ} {U:Rip G} {K H:Mob G} {X Y: Flats G} {b:Bool}
variable {A P:Type*}{k ℓ:ℕ}
lemma Ψpulls (l:Legs (Shore G h))(m:ℕ)(he:h ≤ m)(X:Rack G m): J _ ℂ (pulls he X) l=pulls he (J _ ℂ X) l:= by rw [rite,pulls,pulls,rite,List.length_map ] -- lift unfolds
lemma Γloop (hi:h≤n)(he:Form0 b K)(hp:Knot b U)(x:SectorP h): J _ ℂ (Wtr n U K x)= Wtr n U ( χ G K ) x:= by
   let H (K:Mob G) (he: Form0 b K): Wtr n U K x=pulls hi (trc (U n) (Left hi x) ( K n )):= funext fun _=> tallyN he.token hp.token hi; rw [H _ he,funext (fun l=> Ψpulls l n hi (trc (U n) (Left hi x) ( K n ))),loop,H _ (coverJ he)]; rfl -- let binder syntax
lemma Γdim (z:ℂ)(he:Form0 b K)(hp:Knot b U)(x:SectorP n): J _ ℂ ( Wtr z U K x )= Wtr z U (χ G K ) x:= by rw [combo z n,map_add,map_smul,map_sub, Γloop le_rfl he hp, Γloop (Nat.le_succ _) he hp,combo z n]; -- order
lemma incoming (w:Legs (Shore G n))(z:ℂ)(he:Form0 b K)(hp:Knot b U): Path.wing z U (χ G K) (ray w)=(ϕ w.length:ℂ) • Path.wing z U K ( ray w ):= by
    funext ⟨⟨p,r⟩,t⟩; unfold Path.wing; rw [ ← Γdim z he hp,rite ]; congr 1; simp [Arts.lift,sail]
lemma cycleJ (z:ℂ)(he:Form0 b K)(hp:Knot b U): ocean z U (χ G K)=χ G (ocean z U K):= by
    ext m l; rw [reels]; let x:=Path.wing z U K (ray l); change coreC _ _ (carpet (Px m) _ ) _ =_* coreC _ _ (carpet (Px m) x ) _; rw [incoming _ z he hp, show carpet (Px m) ((ϕ l.length:ℂ) • x)= (ϕ l.length:ℂ) • carpet (Px m) x from funext (fun ⟨a,b⟩=> by simp only [carpet, Pi.smul_apply, integral_smul ] ),core_m (carpet_test he.price hp.price _ z) ]; rfl
abbrev LJ (G:Gauge):= Train.tapeL (fun _:ℂ=>χ G)
abbrev fj (G:Gauge):= blast 0 (LJ G)
lemma fee (F: Flats G)(n:ℕ): fj G F n=LJ G ( F n ):= blade ..
lemma sl (F:Coat G)(n:ℕ): fj G (.single n F)= .single n (LJ G F):= blast_sl ..
lemma cap_q (he:ClockD b t r X) : Pact (fj G (step0 G X)) (step0 G (fj G X)):= by
    have hp (i:ℕ)(x:Flats G): step0 G x (i+1)=swamp (A0 G 0) (x i):= blade ..
    intro n; rcases n with _|n; · rw [fee, show ∀ F,step0 G F 0=0 from fun F=> bland zero_lt_one _ F,show step0 G _ 0=0 from bland zero_lt_one _ _,map_zero] -- ok
    rw [fee,hp,hp,fee]; let U:= A0 G 0; let y: Coat G:= X n; let v:= LJ G y; let hV: Knot b U:= c_bo 0; let F(x:ℂ):= swamp U v x;
    have hQ : ∀ᶠ i:ℂ in dotty, Form0 b (y i):= sunny (he n).fine.tune; filter_upwards [high0,hQ] with i hi hx; change χ G ( swamp U y i )= swamp U v i; rw [swamp_spec hV hx hi,swamp_spec hV (coverJ hx) hi,map_smul, ← cycleJ i hx hV]; rfl
lemma Jquake (X Y:Flats G) : fj G (TreeN U X Y)=TreeN U (fj G X) (fj G Y):= by
   induction X using Finsupp.induction_linear generalizing Y with
   | zero=>simp
   | add x y H T=> rw [map_add,LinearMap.add_apply,map_add,map_add,map_add,LinearMap.add_apply,H,T]
   | single a x=> induction Y using Finsupp.induction_linear with
     | zero=> simp
     | add x y hT hQ=> rw [map_add,map_add,map_add,map_add,hT,hQ]
     | single m p=>
       have hc (i j:ℕ)(f g:Coat G): TreeN U (.single i f) (.single j g)= .single (j+i) (tapeB (squad U) f g):= by rw [TreeN,explode,Finsupp.lsum_single]; exact blast_sl ..
       rw [hc,sl,sl,sl,hc]; exact congr_arg _ (funext fun i=>funext fun j=> joins (U j) _ (x i j) (p i j))
-- projection plow family
lemma plow_j (K:Mob G)(z:ℂ)(y:ℝ): plow z y ( χ G K )= χ G (plow z y K):= by ext n l; rw [reels,plow,reels,plow]; unfold sr; rw [List.length_map,mul_left_comm]
lemma saves (he:Mell.Trail H K z): Mell.Trail (χ G H) (χ G K) z:= by constructor; intro v n l; simp_rw [ plow_j,reels ]; exact (he.derive v n l).const_mul _
lemma buys (h:ℕ)(Y:Flats G)(y x:ℝ): LJ G (Parade Y h y x)= Parade (fj G Y) h y x:= by
   induction Y using Finsupp.induction_linear with
   | zero=> rw [map_zero,pageZ,map_zero]
   | add x y hx hy=> rw [map_add,page_add,page_add,map_add,hx,hy]
   | single i f=> rw [ sl ]; ext1 t; change χ G _=_; rw [page_sl,page_sl,hikeP,hikeP,map_smul, ← plow_j ]; rfl
variable {P Q: Coat G}
lemma screens (H:Joint h X Y P Q) : Joint h (fj G X) (fj G Y) ( LJ G P ) (LJ G Q):= by
    refine ⟨?_,?_,fun i=>?_,coolC ( χ G ) H.ice, mer_leaf H.worth,(fun z i=> (plow_j ..).trans (congr_arg _ (H.back z i))),?_⟩
    · filter_upwards [H.advance] with i hp n; rw [fee,fee]; exact saves (hp n)
    · intro i p; rw [ ← buys ]; obtain ⟨L,hL⟩:= H.toll i p; exact ⟨ _, loop_mer hL⟩
    · rw [fee ]; exact mer_leaf ( H.wet i )
    filter_upwards [H.sip] with x hx; rw [ fee, ← map_add ]; intro m l; change Tendsto (fun t:ℝ=> plow _ t ( χ G (Y 0 x) ) m l) atBot (𝓝 ((χ G ((P+Q) x)) m l)); simp_rw [ plow_j,reels ]; exact Tendsto.const_mul _ (hx ..)
lemma ranks {D:Prop}(e:ℕ)(H:sings b t h P D X Y Q) : sings b t h ((ϕ e:ℂ) • LJ G P) D ((ϕ e:ℂ) • fj G X) ((ϕ e:ℂ) • fj G Y) ((ϕ e:ℂ) • LJ G Q):= by
    obtain ⟨⟨r,hT,hR,hQ⟩,hP⟩:=H; refine ⟨ ⟨ r,?_,?_,(Jfin hQ).smul (by simp only [ϕ,star_pow,star_neg,star_one])⟩,fun hx=>by rw [ hP hx,map_zero,smul_zero ]⟩
    · have hp:= screens hT; rw [map_add ] at hp; rw [map_smul, ← smul_add ]; exact (hp.via (common (fun _=> EventuallyEq.rfl) (cap_q hR))).scale _
    intro i; rw [Finsupp.smul_apply,fee ]; exact ( Jfin ( hR i ) ).smul (by simp only [ϕ,star_pow,star_neg,star_one])
variable {W V:T (Flats G)}{F H S:T (Coat G)}
abbrev νp (m:ℕ)(F:T (Flats G))(k:ℕ): Flats G:= (ϕ (m+k):ℂ) • fj G (F k)
abbrev νc (m:ℕ)(S:T (Coat G))(k:ℕ): Coat G:= (ϕ (m+k):ℂ) • LJ G (S k)
private lemma presents (h:ℕ) (x y:ℕ)(hv:x+y=k): drive0 G (νp 0 W x) (νp h V y)= (ϕ (h+k):ℂ) • fj G (drive0 G ( W x ) (V y)):= by unfold νp drive0; rw [Jquake,map_smul,map_smul,LinearMap.smul_apply, smul_smul]; congr 1; unfold ϕ; rw [← pow_add]; congr 1; omega
lemma stands (H:leader G W F S): leader G (νp 0 W) (νc 0 F) (νc 0 S):= by
    intro i; obtain ⟨L,M⟩:= H i; unfold PathD; rw [show program G i ( νp 0 W )=(ϕ (0+i):ℂ) • fj G (program G i W) from ?_]; exact ranks (0+i) (H i)
    unfold program; rw [map_smul,smul_comm _ ((2:ℂ)⁻¹),map_sum ];  apply congr_arg ((2:ℂ)⁻¹ • ·); rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun v hv=> presents _ _ _ (mem_antidiagonal.mp (mem_filter.mp hv|>.1)))
lemma runsJ (m:ℕ)(hp:comet h t W F V S): comet h t (νp 0 W) (νc m F) (νp m V) (νc m S):= by
    intro i; obtain ⟨L,M⟩:= hp i; unfold PathD; rw [show platform (νp 0 W) i (νp m V)=(ϕ (m+i):ℂ) • fj G (platform W i V) from ?_]; exact ranks (m+i) (hp i)
    unfold platform; rw [ map_sum,Finset.smul_sum ]; exact Finset.sum_congr rfl fun v hv=> presents _ _ _ (mem_antidiagonal.mp (mem_filter.mp hv|>.1))
end YM.MS.Reed
