import YM.FVA2.LeanPole
/-!
# DR Wick covariance held before projection for angularly transformed marks

Keep not only the continued Mellin weight but also normalization and undetermined value behind dotty.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.ArchTurn
open Filter Topology Set Function MeasureTheory MS MS.Logarithm Arc
open MS.Plane MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Convolve MS.Book.Program MS.Dock
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Arts MS.Arts.Spin MS.Halo MS.Arc MS.Garment MS.Hem MS.Rock MS.Rock.Path MS.Alps
open MS.Plane.Wire MS.Arts.Pilot MS.Rock.Oceans MS.Color MS.Shine MS.Hem.Mell
open scoped Topology Classical ContDiff
variable {G:Gauge} (s:Signed) {m n h:ℕ} (u:m≤n) {z:ℂ} {t r:ℤ} {f g:Coat G}
open MS.Garment.Wick
variable     {U:Rip G} {K H:Mob G} {X Y F: Flats G}
private lemma rent_α (k:Cfield G n) : wfield (remote s k)=wfield k:= by rcases k with ⟨⟨_|k,_|_⟩,c⟩ <;> rfl
private lemma rent_m (l: Legs (Shore G n)) : mass (l.map (remode s))=mass l:= by induction l with| nil=>rfl| cons i l ih=> rw [List.map_cons, Price_cons,Price_cons, ih]; exact congr_arg (· + mass l) (rent_α s i.1)
private lemma rent_v (l: Legs (Shore G n))(y:ℝ) : sr y (l.map (remode s))=(sr y l).map (remode s):= by simp only [sr, List.map_map]; congr! 1; funext i; exact Prod.ext rfl ((map_smul _ _ _).symm)
private lemma stem_y (l:Legs (Shore G n))(y:ℝ): stem s (sr y l)=stem s l:=by unfold stem sr; rw [List.map_map]; rfl
lemma plow_c (K: Mob G)(z:ℂ)(y:ℝ): plow z y (canto s K)= canto s (plow z y K) := by ext n l; rw [rush,plow, plow,rent_m, rush,stem_y,rent_v,mul_left_comm ]
lemma renting (ha:Mell.Trail H K z): Mell.Trail (canto s H) (canto s K) z:= by constructor; intro v n l; simp_rw [plow_c,rush]; exact (ha.derive v n (l.map (remode s))).const_mul _
lemma houses (hx:Home K h): Home (canto s K) h:= fun i=> (plow_c s K _ i).trans (congr_arg _ (hx i))

lemma sturdyK (h:Form0 false K) : Form0 false (canto s K):= ⟨ fells s h.price, sturdy_s s _ h.token⟩
-- trc dimensional extension, test with any hub. Mark does NOT impose momentum.
lemma sky_left (p:SectorP m) : (arcS n s).turn (Left u p)= Left u ((arcS m s).turn p):= by unfold arcS crane; rw [forward u,arch_on]
lemma sky_right (p:Momentum ( Apart m n )) : (arcS n s).turn (Right u p)=Right u p:= by unfold arcS crane; rw [forward u,arch_identity]
lemma sky_slide (p: SectorP m)(r:ℝ)(hv:m<n): slideA hv ((arcS m s).turn p,r)=(arcS n s).turn (slideA hv (p,r)):= by rw [Path.path,Path.path,map_add,sky_left,map_smul, hatch,← send_spray,sky_right] -- rewrite Step both
lemma h_pulls (V:Rack G n) : whorl m s (pulls u V)=pulls u (whorl n s V):= by funext l; unfold pulls whorl arcS crane; rw [forward u (hand s), Spin.telescopeS ]
lemma bow_wave (k:ℕ)(i:n≤k)(he:Form0 false K)(hp:Knot true U)(x:SectorP n): Wtr k U (canto s K) x= whorl n s (Wtr k U K ((arcS n s).turn x)):= by
   let v:= (arcS k s).turn; let V:=v (Left i x); have ht: V=Left i ((arcS n s).turn x):= sky_left s i x; let R:= whorl k (G:=G) s
   have Hₗ {p:SectorP n}{F:Mob G}(hm: Sturdy false F): Wtr k U F p=pulls i (Flux.trc (U k) (Left i p) (F k)):= funext fun l=> tallyN hm hp.clearer.token i; rw [Hₗ (sturdyK s he).token, Hₗ he.token, ← ht,h_pulls, show R (Flux.trc (U k) V (K k)) =_ from (hp.token.turn k (arcS k s) (fun v=>Bool.noConfusion v)).shuttle0 (Left i x) (K k) ]; rfl
lemma health (he:Form0 false K)(hp:Knot true U)(x:SectorP n) : Wtr z U (canto s K) x=whorl n s ( Wtr z U K ((arcS n s).turn x) ):= by rw [combo z n,combo z n,map_add,map_smul,map_sub, bow_wave s n (le_refl n), bow_wave s (n+1) (by omega) ]; all_goals assumption
lemma windship (w: Legs ( Shore G n))(he: Form0 false K) (hp:Knot true U): Path.wing z U (canto s K) (ray w) = stem s w • fun (x:(SectorP n× ℝ)×ℝ)=> Path.wing z U K ( ray (w.map (remode s)) ) (((arcS n s).turn x.1.1,x.1.2),x.2):= by
   funext ⟨⟨p,r⟩,t⟩; let u:=sail (ray w) t; have heS {k:ℝ}(p : SectorP n):= sky_slide s p k (Nat.lt_succ_self n); unfold Path.wing; rw [Pi.smul_apply]; dsimp only; rw [health s he hp, ← sky_slide, show whorl (n+1) s _ (Arts.lift _ u) = _ from congr_fun (Eq.symm (h_pulls s (Nat.le_succ n) (Wtr z U K (slideA (Nat.lt_succ_self n) ((arcS n s).turn p,r))))) u ]; -- unfold pulls, sprint
   rw [sprint]; have hu: u.map (remode s)=sail ( ray (w.map (remode s)) ) t:= by unfold u ray sail; simp only [ List.map_map ]; congr! 1; funext i; exact Prod.ext rfl (map_smul (arcS n s).turn t i.2)
   rw [hu]; have hX:stem s u=stem s w:= by unfold u sail ray stem; rw [List.map_map,List.map_map]; rfl
   rw [hX]; rfl
lemma cycleC (he:Form0 false K)(hp:Knot true U): canto s (ocean z U K)=ocean z U (canto s K):= by
   ext m l; rw [rush]; let V:= arcS m s; let x:= Path.wing z U K (ray (l.map ( remode s ))); let y:= Path.wing z U (canto s K) (ray l); let p:= stem s l; let F:= carpet (Px m) x;
   have hy: carpet (Px m) y = p • F:= by
       ext1 ⟨a,b⟩; unfold carpet y; rw [windship s l he hp]; simp_rw [ Pi.smul_apply, integral_smul ]; congr 1; exact V.volume.integral_comp V.turn.toHomeomorph.measurableEmbedding (fun r=> x ((r,a),b)) -- maybe mem
   change p * coreC _ m F 1= coreC _ m (carpet (Px m) y) 1; rw [hy,core_m (carpet_test he.price hp.price _ z) ]; rfl
-- exact Tree through, no smooth need. Flat
lemma treeC (he:Knot true U){b:Bool}(ht:closedF U b)(K H:Mob G): canto s (arbor U K H)=arbor U (canto s K) (canto s H):= funext fun i=> (he.token.turn i (arcS i s) (fun h=>Bool.noConfusion h)).gatherR _ _ (ht i) (ht i)
abbrev tickW := Train.tapeL (fun _:ℂ=>canto (G:=G) s)
abbrev flatQ := blast 0 (tickW s (G:=G))
lemma dose (F: Flats G)(i:ℕ) : flatQ s F i=tickW s ( F i ):= blade ..
lemma single_h (f:Coat G)(n:ℕ) : flatQ s (.single n f)= .single n (tickW s f):= blast_sl ..
lemma step_h (he:ClockD false t r X) : Pact (step0 G (flatQ s X)) (flatQ s (step0 G X)):= by
   have hv (n:ℕ)(F: Flats G): step0 G F (n+1)=swamp (A0 G 0) (F n):= blade ..
   intro n; rcases n with _|n; · rw [dose, show ∀ X,step0 G X 0=0 from fun X=> bland zero_lt_one _ X,show step0 G X 0=0 from bland zero_lt_one _ X, map_zero ]
   rw [dose,hv,hv,dose ]; let U:= A0 G 0; let k:= swamp U; let p:Knot true U:= c_bo 0; let y:Coat G:= X n; let v:= tickW s y; have he: ∀ᶠ i in dotty, Form0 false (y i):= sunny ((he n).fine.tune);
   filter_upwards [high0,he] with i hi he; change swamp U v i = canto s ( swamp U y i ); rw [swamp_spec p.clearer he hi,swamp_spec p.clearer (sturdyK s he) hi,map_smul, cycleC s he p]; rfl -- elaboration v
lemma P_tx (he:Knot true U){b:Bool}(ht:closedF U b)(X Y:Flats G): flatQ s (TreeN U X Y)= TreeN U (flatQ s X) (flatQ s Y) := by
   induction X using Finsupp.induction_linear generalizing Y with
   | zero=>simp
   | add x y H T=> rw [map_add,LinearMap.add_apply,map_add,map_add,map_add,LinearMap.add_apply,H,T]
   | single a x=> induction Y using Finsupp.induction_linear with
     | zero=> simp
     | add x y hT hQ=> rw [map_add,map_add,map_add,map_add,hT,hQ]
     | single m p=>
       have hc (i j:ℕ)(f g:Coat G): TreeN U (.single i f) (.single j g)= .single (j+i) (tapeB (squad U) f g):= by rw [TreeN,explode,Finsupp.lsum_single]; exact blast_sl ..
       rw [hc,single_h,single_h,single_h,hc]; exact congr_arg _ (funext (fun i=>treeC s he ht (x i) (p i))) -- dependent order
lemma at_bulk (H: Gang true h t X): Pact X (flatQ s X):= by obtain ⟨n,hT⟩:=H.price; intro i; rw [dose ]; exact (sunny (hT i).fine.tune).mono (fun _ hp=> ( kForm s hp.token ).symm)
lemma drives {B q:T (Coat G)}{Y V:T (Flats G)} (H:leader G Y B q): ∀ i:ℕ,Pact (flatQ s (platform Y i V)) (platform Y i (fun i=> flatQ s ( V i ))):= by
   intro i; unfold platform drive0; rw [map_sum ]; simp_rw [ P_tx s (c_bo (b:=true) 0) (cl_a G 0)]; refine pact_sum _ (fun i _=> pair_pact _ (pact_sym (at_bulk s (Dock.gang (H i.1)))) (fun i=>EventuallyEq.rfl) )
lemma parade_h (h:ℕ)(Y:Flats G)(y x:ℝ): tickW s (Parade Y h y x )= Parade (flatQ s Y) h y x:= by
   induction Y using Finsupp.induction_linear with
   | zero=> rw [map_zero,pageZ,map_zero]
   | add x y hx hy=> rw [map_add,page_add,page_add,map_add,hx,hy]
   | single i f=> rw [single_h]; ext1 t; change canto s _= _; rw [page_sl,page_sl,hikeP,hikeP,map_smul,← plow_c ]; rfl
lemma Lines (he:Joint h X Y f g) : Joint h (flatQ s X) (flatQ s Y) (tickW s f) (tickW s g):= by
   refine ⟨ ?_, ?_, fun i=> ?_,coolC (canto s) he.ice,vibrant s he.worth,(fun i=> houses s (he.back i)),?_ ⟩
   · filter_upwards [ he.advance ] with i hp n; rw [dose,dose]; exact renting s (hp n)
   · intro i p; rw [ ← parade_h ]; obtain ⟨H,h⟩:= he.toll i p; exact ⟨_,limb s h⟩
   · rw [ dose ]; exact vibrant s ( he.wet i )
   filter_upwards [he.sip] with x hx; rw [dose,← map_add ]; intro m l; change Tendsto (fun t:ℝ=> plow _ t ( canto s (Y 0 x) ) m l) atBot (𝓝 ((canto s ((f+g) x)) m l)); simp_rw [ plow_c,rush ]; exact Tendsto.const_mul _ (hx ..) -- order?
lemma Bob_h (he:Bob false h t r X Y f g) : Bob false h t r (flatQ s X) (flatQ s Y) (tickW s f) (tickW s g) := by
   refine ⟨?_,fun i=> ?_,pole_cap s he.2.2 ⟩; obtain hh:= Lines s he.1; rw [map_add ] at hh; exact hh.via (common (fun _=> EventuallyEq.rfl) (pact_sym (step_h s he.2.1 )))
   rw [dose ]; exact pole_cap s (he.2.1 i)
theorem comet_h {X Y: T (Flats G)}{B f g q:T (Coat G)}(hB: leader G X B q)(hx: comet h t X f Y g) : comet h t X (fun i=>tickW s (f i)) (fun i=>flatQ s (Y i)) (fun i=> tickW s (g i)) := by
   intro i; obtain ⟨⟨r,he⟩,H⟩:= hx i; apply Dock.sings.via (Y:=flatQ s (Y i)) _ ( drives s hB (V:=Y) i); exact ⟨ ⟨ r,Bob_h s he⟩,fun x=>False.elim x⟩
end YM.FVA2.ArchTurn
