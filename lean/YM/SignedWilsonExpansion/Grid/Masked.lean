import YM.SignedWilsonExpansion.MaskFoot
import YM.SignedWilsonExpansion.Grid.Duet
namespace YM.SignedWilsonExpansion.Overlap.Duet
/-! # valence mask for MIXED oriented field pair. Insert *both* L0 and L2 terms. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake MS.Theater
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open MS.Puff MS.Osc MS.Osc.Snap MS.Latch MS.Latch.Job MS.Rake.Geo MS.Rake MS.Rock MS.Rock.Path MS.Breeze MS.Vane
open FVA2 TreeView HighRank HighScale MarkRows MassShift MarkShift Walk TreeLine
open Align PhasePair
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {F H V A:Law G}
local notation "Φ" => (PlanetD G)
local notation "μ" => covMeasure Axis
local notation "Ψ" => field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
variable {Y:Edge G}
variable {K:Booked (Press.portDeck G)}(M:MS_Data G K)(x:Fin 2→QP)(hx:Injective x) (zero one:Bool)
local notation "η₀" => Energy.called (degreeX zero) 2 G
local notation "η₁" => Energy.called (degreeX one) 2 G
local notation "Ξ" => Energy.plane
local notation "E" => Energy.plane (degreeX zero) 2 G 0
local notation "E'" => Energy.plane (degreeX one) 2 G 0
local notation "Hκ" => MarkRows.packet M (Energy.called (degreeX zero) 2 G)
local notation "K'" => MarkRows.packet M (Energy.called (degreeX one) 2 G)
local notation "U0" => Duet.extract M x zero one
local notation "β" => Archive 4 M.bulk
local notation "X" => x 1-x 0
lemma initialD (s:Clock ℝ) : similar (Hκ 0 s) E:= fun w h=> by rw [MarkRows.starts M η₀ s w h,Energy.found]
lemma source0D (s:Clock ℝ) : freight M x zero one 0 s=Cabin (X) (Φ s.2) μ E' E:= by
    unfold freight pack_source queue; rw [show Domain.paths 0 0=∅ from rfl,Finset.sum_empty, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, zero_add]; exact psim _ (initialD M one s) (initialD M zero s)
lemma zeros2D (s:Clock ℝ)(w:Legs (Lane4 G))(he:w.length>2): freight M x zero one 0 s w=0:= by
    rw [ source0D ]; have he1: Limit E 2:=fun v h=> Walk.ranked_N _ (by rw [mod_int]; omega)
    have he2: Limit E' 2:=fun v h=> Walk.ranked_N _ (by rw [mod_int];omega)
    exact capjoin he2 he1 _ _ _ w (by omega)
include hx
lemma anatomyD (e:ℕ)(t:ℝ) : descent (F:=fun s=> U0 e (t,s)) (fun s=> freight M x zero one e (t,s)):= ⟨tote M x hx zero one e t,fun s w=> pace_X M x hx zero one e (t,s) w,fun w=> provisionalX M x hx zero one e w t⟩
lemma ground_upD (s:Clock ℝ)(w:Legs (Lane4 G))(he:w.length>2) : U0 0 s w=0:= scrap (anatomyD M x hx zero one 0 s.1) (fun i=> i>2) (fun i h=> by omega) (fun i=> zeros2D M x zero one (s.1,i) ) _ he _ _ rfl

lemma descent2D (v t:ℝ)(n:ℕ) :
    descent (F:=fun s=>leap v (U0 n) (t,s)) (fun s=>leap v (freight M x zero one n) (t,s)):= by
   obtain ⟨⟨k,hp⟩,he,h⟩:= anatomyD M x hx zero one n (t+v); obtain ⟨⟨j,hv⟩,ht,hT⟩:= anatomyD M x hx zero one n t
   refine ⟨⟨k+j,fun s w hz=> sub_eq_zero.mpr ((hp s w (by omega)).trans ((hv s w (by omega)).symm)) ⟩,fun s w=>?_,fun w=>?_⟩
   · obtain hz:= (he s w).sub (ht s w); have hs : cycle (Φ s) μ ( leap v ( U0 n ) (t,s) ) = cycle (Φ s) μ ( U0 n (t+v,s) )- cycle (Φ s) μ ( U0 n (t,s) ):= by
        funext w; exact of_subc ( b:=false ) (fun w _=> Wallet.cour ( worthwhile M x hx zero one _ _ ) s w) (fun w _=> Wallet.cour ( worthwhile M x hx zero one _ _ ) s w) (fun i=> Bool.noConfusion i)
     rw [ hs ]; convert! hz using 1; all_goals first| rfl| dsimp only; simp only [leap,MassShift.bump,Pi.sub_apply,add_sub_add_comm]; try rfl
   convert! (h w).sub (hT w) using 1; all_goals first| rfl| simp only [sub_self]
lemma all_delta0D (v:ℝ) (s:Clock ℝ): leap v (U0 0) s=0:= by
   funext w; apply scrap ( descent2D M x hx zero one v s.1 0 ) (fun _=>True) (fun _ _=> trivial) ?_ w.length trivial _ w rfl
   intro i w _; unfold leap MassShift.bump; simp only [Pi.sub_apply, source0D, sub_self]
variable (simple:G.Simple)
include simple
omit hx in
lemma h_QD (s:Clock ℝ)(v:ℝ)(i:ℕ)(h:i≤1)(n:ℕ)(ht:n≤1) :
    leap v (fun s=>Cabin (X) (Φ s.2) μ (K' i s) (Hκ n s) ) s=0:= by
   apply sub_eq_zero.mpr; have hp(s0:Bool)(i:ℕ)(ht:i≤1) : similar (MarkRows.packet M (Energy.called (degreeX s0) 2 G) i (s.1+v,s.2)) (MarkRows.packet M (Energy.called (degreeX s0) 2 G) i s):= by intro j h; apply sub_eq_zero.mp; interval_cases i; exacts [ MarkShift.blank M (Energy.called (degreeX s0) 2 G) s j h v, MarkShift.first_quiet M (Energy.called (degreeX s0) 2 G) simple s j h v ]
   exact psim _ ( hp one i h ) ( hp zero n ht )
lemma source1D (s:Clock ℝ)(v:ℝ): leap v ( freight M x zero one 1 ) s=0:= by
    let s':=(s.1+v,s.2); apply sub_eq_zero.mpr; change freight M x zero one 1 s'=freight M x zero one 1 s; unfold freight queue pack_source; refine congr_arg₂ (· + ·) ?_ (Finset.sum_congr rfl fun i hi=>?_ )
    · rw [show Domain.paths 1 0={0} from rfl, sum_singleton,sum_singleton]; exact sub_eq_zero.mp ( tree_prior M x hx simple s v 0 ( U0 0 ) ( all_delta0D M x hx zero one v s ) )
    obtain hi:= Finset.mem_antidiagonal.mp hi
    exact sub_eq_zero.mp (h_QD M x zero one simple s v _ (by omega) _ (by omega))
lemma all_delta1D (v:ℝ)(s:Clock ℝ) : leap v ( U0 1 ) s=0:= by
    funext w; apply scrap (descent2D M x hx zero one v s.1 1) ( fun _=> True ) (fun _ _=> trivial) ?_ w.length trivial _ w rfl
    exact fun i w _=> congr_fun (source1D M x hx zero one simple (s.1,i) v) w
lemma source2D (v:ℝ)(s:Clock ℝ): let L:=leap v ( Hκ 2 ) s; let T:= leap v ( K' 2 ) s
      leap v ( freight M x zero one 2 ) s= Flux.tree parity (Φ s.2) (MarkShift.wall M v) ( U0 0 s ) +
         Cabin (X) (Φ s.2) μ T E + Cabin (X) (Φ s.2) μ E' L := by
   intro L T; let r:=(s.1+v,s.2)
   let z(t:Clock ℝ):= U0 0 t
   let C: Law G→ Law G→ Law G:=Cabin (X) (Φ s.2) μ; let b:= boulevard parity (Φ s.2)
   let f i (s:Clock ℝ):= Hκ i s; let g i (s:Clock ℝ):= K' i s
   have ha(q:Clock ℝ): freight M x zero one 2 q= tree parity (Φ q.2) (β 2 q) (z q)+ tree parity (Φ q.2) (β 1 q) (U0 1 q)
        +(Cabin (X) (Φ q.2) μ (g 2 q) (f 0 q)+ Cabin (X) (Φ q.2) μ (g 0 q) (f 2 q)+ Cabin (X) (Φ q.2) μ (g 1 q) (f 1 q)):= by
     rw [freight,queue,pack_source, show Domain.paths 2 0= {0,1} from rfl, show antidiagonal 2={(2,0),(0,2),(1,1)} from by decide,sum_pair (by decide),sum_insert (by decide), sum_insert (by decide),sum_singleton ]; rw [ ←add_assoc ( Cabin (X) _ _ _ _ ) ]; -- reducibility
   have hv : tree parity (Φ s.2) (β 1 r) (U0 1 r)=tree parity (Φ s.2) (β 1 s) (U0 1 s):= sub_eq_zero.mp ( tree_prior M x hx simple s v 1 _ (all_delta1D M x hx zero one simple v s) )
   have ht : z r=z s:= sub_eq_zero.mp ( all_delta0D M x hx zero one v s )
   have hm : b (β 2 r-β 2 s) (z s)=b ( MarkShift.wall M v ) (z s):=MarkShift.compare_context _ (fun w p h=> MarkShift.token M simple v s w p h) (fun _ _=>rfl)
   have hs: C (g 1 r) (f 1 r)=C (g 1 s) (f 1 s):= sub_eq_zero.mp ( h_QD M x zero one simple s v 1 (by norm_num) 1 (by norm_num) )
   have he t(q:Clock ℝ): similar (f t q) (f t q):= fun _ _=> rfl
   have hL: C (g 2 r) (f 0 r)-C (g 2 s) (f 0 s)=C T E:= by
      have h₁ : C (g 2 r) (f 0 r)= C (g 2 r) (f 0 s):= psim _ (fun _ _=>rfl) (fun w ht=> sub_eq_zero.mp (MarkShift.blank M η₀ s w ht v))
      rw [h₁]; exact ( sift ( mark_permit s.2 (X) ( walletQ M one 2 r ) ( walletQ M zero 0 s ) ) ( mark_permit s.2 (X) ( walletQ M one 2 s ) ( walletQ M zero 0 s ) ) ).symm.trans (psim _ (fun _ _=>rfl) (initialD M zero s))
   have hR: C (g 0 r) (f 2 r)-C (g 0 s) (f 2 s)=C E' L:= by
      have h₁: C (g 0 r) (f 2 r)= C (g 0 s) (f 2 r):= psim _ (fun w ht=> sub_eq_zero.mp (MarkShift.blank M η₁ s w ht v)) (he 2 r)
      rw [h₁]; exact ( sift' ( mark_permit s.2 (X) ( walletQ M one 0 s ) ( walletQ M zero 2 r ) ) ( mark_permit s.2 (X) ( walletQ M one 0 s ) ( walletQ M zero 2 s ) ) ).symm.trans (psim _ (initialD M one s) (fun _ _=>rfl))
   change freight M x zero one 2 r - freight M x zero one 2 s=_
   rw [ha,ha, hv]; change b (β 2 r) (z r)+_+(C (g 2 r) _+ C _ (f 2 r)+ C _ _)- (b (β 2 s) _+_+(C _ _+ C _ _+ C _ _))= b _ _ + C T E + C E' L
   rw [ht,hs, ← hm, ←hL,←hR,map_sub,LinearMap.sub_apply]; abel

lemma aboveD (v:ℝ)(s:Clock ℝ) : ∀ w:Legs (Lane4 G), w.length>2 → w.length%2=0→ leap v ( U0 2 ) s w=0 := by
   let P(n:ℕ):Prop:= n>2∧ n%2=0
   intro w hu hv; refine scrap (descent2D M x hx zero one v s.1 2) P ?_ ?_ w.length ⟨hu,hv⟩ s.2 w rfl
   · rintro i ⟨hp,hq⟩; unfold P; omega
   intro u w hw; let q:Clock ℝ:=(s.1,u); rw [source2D M x hx zero one simple v (s.1,u)]; simp only [Pi.add_apply]
   let H:=U0 0 q; let L (d:Bool):= leap v ( MarkRows.packet M ( Energy.called (degreeX d) 2 G ) 2 ) q; let K:=MarkShift.wall M v
   have hp: Limit H 2:= fun w h=> ground_upD M x hx zero one q w (by omega)
   have ht: Limit K 2:= fun w h=>Book.strange _ (by omega)
   have hE(a:Bool)(w:Legs (Lane4 G))(he:w.length≠2): Ξ ( degreeX a ) 2 G 0 w=0:= ranked_N _ (by rw [mod_int];omega)
   have hc(d:Bool)(w:Legs (Lane4 G))(he:w.length%2=0)(hr:w.length>2): L d w=0:= by
      unfold L leap MassShift.bump; apply sub_eq_zero.mpr
      by_cases hz:w.length=4; · beta_reduce; rw [ MarkTop.evaluation M ( Energy.called (degreeX d) 2 G ) _ (Energy.full) _ _ hz, MarkTop.evaluation M ( Energy.called (degreeX d) 2 G ) _ Energy.full _ _ hz ];
      exact (MarkRows.level2 M ( Energy.called (degreeX d) 2 G ) _ _ (fun i=>Bool.noConfusion i) (by omega)).trans (MarkRows.level2 M ( Energy.called (degreeX d) 2 G ) _ _ (fun i=>Bool.noConfusion i) (by omega)).symm
   have he(d a:Bool)(l r:Legs (Lane4 G))(hl:l.length+r.length=w.length)(k j:Lane4 G): L d (k::l)=0∨ Ξ (degreeX a) 2 G 0 (j::r)=0:= by
      obtain ⟨ha,hv⟩:= hw; by_cases hm:r.length=1; · exact Or.inl (hc d _ (by simp [Nat.add_mod]; omega) (by simp; omega) )
      exact Or.inr (hE a _ (by simp; omega))
   have hφ (H F:Law G)(hp:∀ l r:Legs ( Lane4 G ),l.length+r.length=w.length → ∀ k j:Lane4 G,H (k::l)=0∨ F (j::r)=0): Cabin (X) (Φ u) μ H F w=0:= by
      unfold Cabin; apply Eq.trans (scatter_congr (field parity) w _ (fun _ _=>(0:ℂ)) ?_) (map_zero (allocate (field parity) w)); intro l r hv; have hℓ:= split_length hv; have hz(i j:Branch G Axis)(p:QP): meshZ (Φ u) i j H F l r p=0:= by unfold meshZ; rcases hp l r hℓ (i,p) (j,-p) with hh|hh <;> rw [hh] <;> ring
      simp_rw [hz]; simp
   rw [ hφ (L one) E (he one zero),hφ E' (L zero) (fun i j hr k l=> ( he zero one j i ((add_comm ..).trans hr) l k ).symm ), leastT ht hp (Φ u) w (by obtain ⟨hn,ht⟩:= hw; omega), add_zero, add_zero ]

-- Cabin from two singleton high inputs. If both external legs are nongauge the source is zero. Need not project ghost sectors.
omit simple hx
lemma wantedD (p:QP)(w v:Lane4 G)(f:Law G)(Left: F=E ∨ f=E)(_:ℕ) :
    Cabin p Y μ F f [w,v]= cuts p Y F f [w] [v]+cross (Ψ w) (Ψ v)*cuts p Y F f [v] [w] := by
   change scatter Ψ [w,v] ( cuts p Y F f )=_
   simp only [scatter_cons,scatter_nil, degree_cons,degree_nil,Bool.xor_false,cross_false',one_mul]; rcases Left with h|h
   · rw [h,dropL p ( F:=E ) ( l:=[w,v]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)), dropL p ( F:=E ) (l:=[]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)) ]; abel
   rw [h,dropR p ( H:=E ) ( r:=[w,v]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)), dropR p ( H:=E ) (r:=[]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)) ]; abel
lemma forgeD (p:QP)(w v:Lane4 G)(f:Law G)(Left: F=E∨ f=E)(i:ℕ)(hq:¬vector w)(hh:¬vector v):Cabin p Y μ F f [w,v]=0:= by
    rw [wantedD zero p w v f Left i]; have he(u:Lane4 G)(h:¬vector u)(j:Lane4 G): E [j,u]=0:= plane_g _ ⟨u,by simp,h⟩
    rcases Left with h|h
    · rw [h,dropL p ( F:=E ) (he w hq),dropL p ( F:=E ) ( he v hh )]; simp
    rw [h,dropR p ( H:=E ) (he v hh), dropR p ( H:= E ) (he w hq) ]; simp

include hx
lemma run_speedD (s:Clock ℝ)(w:Legs ( Lane4 G ))(hp:w.length=2):
    HasDerivAt (fun t:ℝ=> U0 0 (s.1,t) w) ( freight M x zero one 0 s w ) s.2:= by
    let h:= (anatomyD M x hx zero one 0 s.1).2.1 s.2 w; dsimp only at h; rw [ cycle_height _ _ _ w false (fun i=>Bool.noConfusion i) (fun i _ hi=>ground_upD M x hx zero one _ i (by omega)),zero_add ] at h; exact h
lemma other_headsD (w v:Lane4 G)(hu:¬vector w)(hv:¬vector v)(s:Clock ℝ): U0 0 s [w,v]=0:= by
   apply Lambda.Canvas.regression (f:=fun t:ℝ=> U0 0 (s.1,t) [w,v]) s.2; swap; · exact provisionalX M x hx zero one 0 _ s.1
   intro t; have hp:= run_speedD M x hx zero one (s.1,t) [w,v] rfl; rw [ source0D, forgeD one (F:=E') _ w v _ ( Or.inl rfl ) 0 hu hv ] at hp; exact hp

include simple
lemma leap_speedD (s:Clock ℝ)(v:ℝ)(w:Legs (Lane4 G))(hp:w.length=2):
    HasDerivAt (fun t:ℝ=>leap v (U0 2) (s.1,t) w) (leap v (freight M x zero one 2) s w) s.2:= by
    let h:= (descent2D M x hx zero one v s.1 2).2.1 s.2 w; dsimp only at h; rw [cycle_height _ _ _ w false (fun i=>Bool.noConfusion i) (fun i _ hi=> aboveD M x hx zero one simple v _ _ (by omega) (by omega)),zero_add ] at h; exact h
lemma leap_oddD (w v:Lane4 G)(hU:Bubble.wing w)(hV:Bubble.wing v)(s:Clock ℝ)(t:ℝ):
    leap t ( U0 2 ) s [w,v]=0:= by
    apply Lambda.Canvas.regression (f:=fun i:ℝ=> leap t ( U0 2 ) (s.1,i) [w,v]) s.2; swap; · exact ( descent2D M x hx zero one t s.1 2 ).2.2 _
    intro i
    obtain he:= leap_speedD M x hx zero one simple (s.1,i) t [w,v] rfl; have hH: leap t (freight M x zero one 2) (s.1,i) [w,v]=0:= by
       rw [ source2D M x hx zero one simple t _ ]; simp only [Pi.add_apply]; rw [forgeD zero _ _ _ _ ( Or.inr rfl ) 0 (Bubble.side hU) (Bubble.side hV),forgeD one _ _ _ _ ( Or.inl rfl ) 0 (Bubble.side hU) (Bubble.side hV),add_zero,add_zero ]
       -- tree. wall (prude) is ranktwo.p.line; odd ext -> partner odd required
       let q:=(s.1,i); let L:= MarkShift.wall M t; let y:=U0 0 q
       change scatter Ψ [w,v] ( attaches parity ( PlanetD G i ) L y )= _
       let f:= attaches parity ( PlanetD G i ) L y
       have hl:= Lambda.Shells.closure G ( Lambda.Shells.hot i )
       have hφ(a b:Branch G Axis)(p:QP)(ht: PlanetD G i a b p≠0) : parity b=parity a:= by
           rw [Walk.dotL] at ht; exact Lambda.Bead.since_xor (hl a b p ht)
       have ha:= Lambda.Bead.prude_solid L (( MassShift.bulk_class M simple t (0,0) ).solid ); -- P masked
       have hm(l r:Legs (Lane4 G))(h:l.length≠1) : f l r=0:= by unfold f attaches; have ht(k:Lane4 G): L (k::l)=0:=Book.strange _ (by simp; omega); simp [ht]
       have hn(w v:Lane4 G)(h:Bubble.wing w)(he:Bubble.wing v): f [w] [v]=0:= by
         unfold f; rw [Heat.convertR ( reverse_day _ )]; refine Finset.sum_eq_zero fun j _=>Finset.sum_eq_zero fun k _=> ?_
         let a:Lane4 G:=(j,-net [w]); let b: Lane4 G:=(k,net [w]); by_cases hp: PlanetD G i j k (-net [w])=0; · simp only [Heat.radius,hp,mul_zero,zero_mul]
         by_cases hz:L [a,w]=0; · unfold radius; dsimp only; rw [ show L [ ( j,-net [w] ), w ]=0 from hz ]; ring
         have hb:= ha _ ( show Course true [a,w] from fun _=>by simp [a]) hz
         have hB:Bubble.wing b:= (hφ j k _ hp).trans ( ( Lambda.Bead.since_xor hb ).trans ( show degree Ψ [w]=true from (by simp only [ degree_cons,degree_nil,Bool.xor_false ] ; exact h) ) )
         have hu:y [b,v]=0:= other_headsD M x hx zero one _ _ (Bubble.side hB) (Bubble.side he) _
         unfold radius; simp only [neg_neg]; rw [ show y [(k,net [w]),v]=0 from hu, mul_zero ]
       change scatter Ψ [w,v] f=_
       rw [scatter_cons,scatter_cons,scatter_nil]; rw [ hn w v hU hV, hn v w hV hU, hm [w,v] [] (by simp), hm [] _ (by simp) ]; simp
    rw [hH] at he; exact he

omit hx simple
lemma empty_energyD (F:Law G)(e:QP)(K:Edge G): Cabin e K μ F E []=0 ∧ Cabin e K μ E F []=0 :=
    let hZ(i:Lane4 G): E [i]=0:= ranked_N _ (by rw [mod_int]; norm_num)
    ⟨ dropR e (H:=E) (F:=F) (r:=[]) hZ [],dropL e (F:=E) (l:=[]) hZ [] ⟩
include hx
lemma ground_flow_stillD (s:Clock ℝ) :
   HasDerivAt (fun t:ℝ=> U0 0 (s.1,t) []) (cycle (Φ s.2) μ (U0 0 s) []) s.2:= by
   have he:= pace_X M x hx zero one 0 s []; unfold turnP at he; rw [source0D, Pi.add_apply, (empty_energyD zero ..).1, add_zero ] at he; exact he
include simple
lemma action_flow_stillD (s:Clock ℝ)(v:ℝ) :
    HasDerivAt (fun t=>leap v (U0 2) (s.1,t) []) (cycle (Φ s.2) μ (leap v ( U0 2 ) s) []) s.2:= by
    have h:= (descent2D M x hx zero one v s.1 2).2.1 s.2 []; dsimp only at h; rw [source2D M x hx zero one simple] at h; simp only [Pi.add_apply] at h;
    rw [ (empty_energyD zero ..).1,(empty_energyD one ..).2,tree_height _ _ _ [] false (fun i=> Bool.noConfusion i),add_zero,add_zero,add_zero ] at h; exact h;
    intro i j h; left; intro w _ hv; exact Book.strange _ (by simp at h; omega)

end
end YM.SignedWilsonExpansion.Overlap.Duet
