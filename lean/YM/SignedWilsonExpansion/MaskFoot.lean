import YM.SignedWilsonExpansion.Pair
namespace YM.SignedWilsonExpansion.PhasePair
/-! Valence truncation for response of the true independently prescribed mask.
Retains both coherent UV stories. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake MS.Theater
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open MS.Puff MS.Osc MS.Osc.Snap MS.Latch MS.Latch.Job MS.Rake.Geo MS.Rake MS.Rock MS.Rock.Path MS.Breeze MS.Vane
open FVA2 TreeView HighRank HighScale MarkRows MassShift MarkShift Walk TreeLine
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {F H V A:Law G}
local notation "Φ" => (PlanetD G)
local notation "μ" => covMeasure Axis
local notation "Ψ" => field (P:=FourP) (Landau.parity (A:=Axis) (C:=G.ColorIndex))
variable {Y:Edge G}

abbrev similar (F H:Law G): Prop:= ∀ w,0<w.length→F w=H w
lemma psim (a:QP)(hx:similar F A)(hp:similar H V): Cabin a Y μ F H=Cabin a Y μ A V:= by
    funext w; unfold Cabin; simp_rw [meshZ,hx (_::_) (by simp), hp (_::_) (by simp)]
lemma top_sim (hx:Agrees F A)(hp:similar H V): tree parity Y F H=tree parity Y A V:= compare_context Y (fun _ _ h=> hx _ h) hp

def descent {F: ℝ→Law G}(S:ℝ→Law G): Prop :=
      (∃ k:ℕ,∀ t w,k<w.length→ F t w=0) ∧
      (∀ t w,HasDerivAt (fun t=> F t w) (cycle (Φ t) μ (F t) w+S t w) t) ∧
      (∀ w,Tendsto (fun t=> F t w) atBot (𝓝 0))
lemma scrap {F H:ℝ→Law G}(h:descent (F:=F) H) (P:ℕ→Prop)
    (hp:∀ w,P w → P (w+2))(hu:∀ s w,P w.length → H s w=0) (v:ℕ)(r:P v)
    (t:ℝ) (w:Legs (Lane4 G))(he:w.length=v): F t w=0:= by
    obtain ⟨⟨k,h⟩,hx,hv⟩:= h
    suffices H:∀ x:ℕ,v + x ≥ k→∀ t w,F t w ≠ 0→w.length=v→False from by by_contra h; exact H k (by omega) t w h he
    -- easier strongInduction on distance.M
    clear he w; intro n hb; induction n using Nat.strong_induction_on generalizing v with
    | h n ih=>
       intro t w hn hl; by_cases he:k<w.length
       · exact hn (h _ _ he)
       have hD(t:ℝ): HasDerivAt (fun t=> F t w) 0 t:= by
         obtain h_t:= hx t w; rw [ hu t w (hl.symm ▸ r),add_zero, cycle_height _ _ _ w false (fun a=> Bool.noConfusion a) ] at h_t; exact h_t
         intro w' _ hj; by_contra! ne; by_cases hr:k<w'.length; · exact ne (h t w' hr)
         exact ih (n-1) (by omega) (v+2) (hp v r) (by omega) t w' ne (by omega)
       exact hn (tendsto_nhds_unique tendsto_const_nhds ((hv w).congr fun s=> is_const_of_deriv_eq_zero (fun t=>(hD t).differentiableAt) (fun t=>(hD t).deriv) s t))
variable {K:Booked (Press.portDeck G)}(M:MS_Data G K)(x:Fin 2→QP)(hx:Injective x)
local notation "η" => Energy.called 1 2 G
local notation "E" => Energy.plane 1 2 G 0
local notation "Hκ" => MarkRows.packet M η
local notation "U0" => PhasePair.read M x η
local notation "β" => Archive 4 M.bulk
local notation "X" => x 1-x 0
lemma initial (s:Clock ℝ) : similar (Hκ 0 s) E:= fun w h=> by rw [MarkRows.starts M η s w h,Energy.found]
lemma source0 (s:Clock ℝ) : source M x 0 s=Cabin (X) (Φ s.2) μ E E:= by
    unfold source pack_source queue; rw [show Domain.paths 0 0=∅ from rfl,Finset.sum_empty, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, zero_add]; exact psim _ (initial M s) (initial M s)
lemma zeros2 (s:Clock ℝ)(w:Legs (Lane4 G))(he:w.length>2): source M x 0 s w=0:= by
    rw [ source0 ]; have he1: Limit E 2:=fun v h=> Walk.ranked_N _ (by rw [mod_int]; omega)
    exact capjoin he1 he1 _ _ _ w (by omega)
include hx
lemma anatomy (e:ℕ)(t:ℝ) : descent (F:=fun s=> U0 e (t,s)) (fun s=> source M x e (t,s)):= ⟨bag M x hx e t,fun s w=> pace_E M x hx e (t,s) w,fun w=> provisional M x hx e w t⟩
lemma ground_up (s:Clock ℝ)(w:Legs (Lane4 G))(he:w.length>2) : U0 0 s w=0:= scrap (anatomy M x hx 0 s.1) (fun i=> i>2) (fun i h=> by omega) (fun i=> zeros2 M x (s.1,i) ) _ he _ _ rfl
local notation "Q" => triggerP M x
lemma descent2 (v t:ℝ)(n:ℕ) :
    descent (F:=fun s=>leap v (U0 n) (t,s)) (fun s=>leap v (source M x n) (t,s)):= by
   obtain ⟨⟨k,hp⟩,he,h⟩:= anatomy M x hx n (t+v); obtain ⟨⟨j,hv⟩,ht,hT⟩:= anatomy M x hx n t
   refine ⟨⟨k+j,fun s w hz=> sub_eq_zero.mpr ((hp s w (by omega)).trans ((hv s w (by omega)).symm)) ⟩,fun s w=>?_,fun w=>?_⟩
   · obtain hz:= (he s w).sub (ht s w); have hs : cycle (Φ s) μ ( leap v ( U0 n ) (t,s) ) = cycle (Φ s) μ ( U0 n (t+v,s) )- cycle (Φ s) μ ( U0 n (t,s) ):= by
        funext w; exact of_subc ( b:=false ) (fun w _=> Wallet.cour ( afford_E M x hx _ _ ) s w) (fun w _=> Wallet.cour ( afford_E M x hx _ _ ) s w) (fun i=> Bool.noConfusion i)
     rw [ hs ]; convert! hz using 1; all_goals first| rfl| dsimp only; simp only [leap,MassShift.bump,Pi.sub_apply,add_sub_add_comm]; try rfl
   convert! (h w).sub (hT w) using 1; all_goals first| rfl| simp only [sub_self]
lemma all_delta0 (v:ℝ) (s:Clock ℝ): leap v (U0 0) s=0:= by
   funext w; apply scrap ( descent2 M x hx v s.1 0 ) (fun _=>True) (fun _ _=> trivial) ?_ w.length trivial _ w rfl
   intro i w _; unfold leap MassShift.bump; simp only [Pi.sub_apply, source0, sub_self]
omit hx in
lemma netP (v:ℝ)(s:Clock ℝ)(n:ℕ)(H:leap v (U0 n) s=0) : U0 n (s.1+v,s.2)=U0 n s:= sub_eq_zero.mp H
variable (simple:G.Simple)
include simple
lemma h_Q (s:Clock ℝ)(v:ℝ)(i:ℕ)(h:i≤1)(n:ℕ)(ht:n≤1) :
    leap v (fun s=>Cabin (X) (Φ s.2) μ (Hκ i s) (Hκ n s) ) s=0:= by
   apply sub_eq_zero.mpr; have hp(i:ℕ)(ht:i≤1) : similar (Hκ i (s.1+v,s.2)) (Hκ i s):= by intro j h; apply sub_eq_zero.mp; interval_cases i; exacts [ MarkShift.blank M η s j h v, MarkShift.first_quiet M η simple s j h v ]
   exact psim _ ( hp i h ) ( hp n ht )
lemma tree_prior (s:Clock ℝ)(v:ℝ) (n:ℕ)(F:Reading G)(hp:leap v F s=0):
    leap v (fun s=> Flux.tree parity ( Φ s.2 ) ( β 1 s ) ( F s ) ) s=0:= by
   let s':=(s.1+v,s.2); apply sub_eq_zero.mpr
   apply compare_context <;> (intro i he; first| exact ( fun z=>( BulkTop.paid1 M simple s' i he z ).trans ( BulkTop.paid1 M simple s i he z ).symm )| exact congr_fun ( sub_eq_zero.mp hp ) i )
lemma source1 (s:Clock ℝ)(v:ℝ): leap v ( source M x 1 ) s=0:= by
    let s':=(s.1+v,s.2); apply sub_eq_zero.mpr; change source M x 1 s'=source M x 1 s; unfold source queue pack_source; refine congr_arg₂ (· + ·) ?_ (Finset.sum_congr rfl fun i hi=>?_ )
    · rw [show Domain.paths 1 0={0} from rfl, sum_singleton,sum_singleton]; exact sub_eq_zero.mp ( tree_prior M x hx simple s v 0 ( U0 0 ) ( all_delta0 M x hx v s ) )
    obtain hi:= Finset.mem_antidiagonal.mp hi
    exact sub_eq_zero.mp (h_Q M x hx simple s v _ (by omega) _ (by omega))
lemma all_delta1 (v:ℝ)(s:Clock ℝ) : leap v ( U0 1 ) s=0:= by
    funext w; apply scrap (descent2 M x hx v s.1 1) ( fun _=> True ) (fun _ _=> trivial) ?_ w.length trivial _ w rfl
    exact fun i w _=> congr_fun (source1 M x hx simple (s.1,i) v) w
lemma source2 (v:ℝ)(s:Clock ℝ): let L:=leap v ( Hκ 2 ) s
      leap v ( source M x 2 ) s= Flux.tree parity (Φ s.2) (MarkShift.wall M v) ( U0 0 s ) +
         Cabin (X) (Φ s.2) μ L E + Cabin (X) (Φ s.2) μ E L := by
   intro L; let r:=(s.1+v,s.2)
   let z(t:Clock ℝ):= U0 0 t
   let C: Law G→ Law G→ Law G:=Cabin (X) (Φ s.2) μ; let b:= boulevard parity (Φ s.2)
   let f i (s:Clock ℝ):= Hκ i s
   have ha(q:Clock ℝ): source M x 2 q= tree parity (Φ q.2) (β 2 q) (z q)+ tree parity (Φ q.2) (β 1 q) (U0 1 q)
        +(Cabin (X) (Φ q.2) μ (f 2 q) (f 0 q)+ Cabin (X) (Φ q.2) μ (f 0 q) (f 2 q)+ Cabin (X) (Φ q.2) μ (f 1 q) (f 1 q)):= by
     rw [source,queue,pack_source, show Domain.paths 2 0= {0,1} from rfl, show antidiagonal 2={(2,0),(0,2),(1,1)} from by decide,sum_pair (by decide),sum_insert (by decide), sum_insert (by decide),sum_singleton ]; rw [ ←add_assoc ( Cabin (X) _ _ _ _ ) ]; -- reducibility
   have hv : tree parity (Φ s.2) (β 1 r) (U0 1 r)=tree parity (Φ s.2) (β 1 s) (U0 1 s):= sub_eq_zero.mp ( tree_prior M x hx simple s v 1 _ (all_delta1 M x hx simple v s) )
   have ht : z r=z s:= sub_eq_zero.mp ( all_delta0 M x hx v s )
   have hm : b (β 2 r-β 2 s) (z s)=b ( MarkShift.wall M v ) (z s):=MarkShift.compare_context _ (fun w p h=> MarkShift.token M simple v s w p h) (fun _ _=>rfl)
   have hs: C (f 1 r) (f 1 r)=C (f 1 s) (f 1 s):= sub_eq_zero.mp ( h_Q M x hx simple s v 1 (by norm_num) 1 (by norm_num) )
   have he t(q:Clock ℝ): similar (f t q) (f t q):= fun _ _=> rfl
   have hL: C (f 2 r) (f 0 r)-C (f 2 s) (f 0 s)=C L E:= by
      have h₁ : C (f 2 r) (f 0 r)= C (f 2 r) (f 0 s):= psim _ (he 2 r) (fun w ht=> sub_eq_zero.mp (MarkShift.blank M η s w ht v))
      rw [h₁]; exact ( sift ( mark_permit s.2 (X) ( wallet_marker M 2 r ) ( wallet_marker M 0 s ) ) ( mark_permit s.2 (X) ( wallet_marker M 2 s ) ( wallet_marker M 0 s ) ) ).symm.trans (psim _ (fun _ _=>rfl) (initial M s))
   have hR: C (f 0 r) (f 2 r)-C (f 0 s) (f 2 s)=C E L:= by
      have h₁: C (f 0 r) (f 2 r)= C (f 0 s) (f 2 r):= psim _ (fun w ht=> sub_eq_zero.mp (MarkShift.blank M η s w ht v)) (he 2 r)
      rw [h₁]; exact ( sift' ( mark_permit s.2 (X) ( wallet_marker M 0 s ) ( wallet_marker M 2 r ) ) ( mark_permit s.2 (X) ( wallet_marker M 0 s ) ( wallet_marker M 2 s ) ) ).symm.trans (psim _ (initial M s) (fun _ _=>rfl))
   change source M x 2 r - source M x 2 s=_
   rw [ha,ha, hv]; change b (β 2 r) (z r)+_+(C (f 2 r) _+ C _ (f 2 r)+ C _ _)- (b (β 2 s) _+_+(C _ _+ C _ _+ C _ _))= b _ _ + C L E + C E L
   rw [ht,hs, ← hm, ←hL,←hR,map_sub,LinearMap.sub_apply]; abel

lemma above (v:ℝ)(s:Clock ℝ) : ∀ w:Legs (Lane4 G), w.length>2 → w.length%2=0→ leap v ( U0 2 ) s w=0 := by
   let P(n:ℕ):Prop:= n>2∧ n%2=0
   intro w hu hv; refine scrap (descent2 M x hx v s.1 2) P ?_ ?_ w.length ⟨hu,hv⟩ s.2 w rfl
   · rintro i ⟨hp,hq⟩; unfold P; omega
   intro u w hw; let q:Clock ℝ:=(s.1,u); rw [source2 M x hx simple v (s.1,u)]; simp only [Pi.add_apply]
   let H:=U0 0 q; let L:= leap v ( Hκ 2 ) q; let K:=MarkShift.wall M v
   have hp: Limit H 2:= fun w h=> ground_up M x hx q w (by omega)
   have ht: Limit K 2:= fun w h=>Book.strange _ (by omega)
   have hE(w:Legs (Lane4 G))(he:w.length≠2): E w=0:= ranked_N _ (by rw [mod_int];omega)
   have hc(w:Legs (Lane4 G))(he:w.length%2=0)(hr:w.length>2): L w=0:= by
      unfold L leap MassShift.bump; apply sub_eq_zero.mpr
      by_cases hz:w.length=4; · beta_reduce; rw [ MarkTop.evaluation M η _ (Energy.full) _ _ hz, MarkTop.evaluation M η _ Energy.full _ _ hz ];
      exact (MarkRows.level2 M η _ _ (fun i=>Bool.noConfusion i) (by omega)).trans (MarkRows.level2 M η _ _ (fun i=>Bool.noConfusion i) (by omega)).symm
   have he(l r:Legs (Lane4 G))(hl:l.length+r.length=w.length)(k j:Lane4 G): L (k::l)=0∨ E (j::r)=0:= by
      obtain ⟨ha,hv⟩:= hw; by_cases hm:r.length=1; · exact Or.inl (hc _ (by simp [Nat.add_mod]; omega) (by simp; omega) )
      exact Or.inr (hE _ (by simp; omega))
   have hφ (H F:Law G)(hp:∀ l r:Legs ( Lane4 G ),l.length+r.length=w.length → ∀ k j:Lane4 G,H (k::l)=0∨ F (j::r)=0): Cabin (X) (Φ u) μ H F w=0:= by
      unfold Cabin; apply Eq.trans (scatter_congr (field parity) w _ (fun _ _=>(0:ℂ)) ?_) (map_zero (allocate (field parity) w)); intro l r hv; have hℓ:= split_length hv; have hz(i j:Branch G Axis)(p:QP): meshZ (Φ u) i j H F l r p=0:= by unfold meshZ; rcases hp l r hℓ (i,p) (j,-p) with hh|hh <;> rw [hh] <;> ring
      simp_rw [hz]; simp
   rw [ hφ L E he,hφ E L (fun i j hr k l=> ( he j i ((add_comm ..).trans hr) l k ).symm ), leastT ht hp (Φ u) w (by obtain ⟨hn,ht⟩:= hw; omega), add_zero, add_zero ]

-- Cabin from two singleton high inputs. If both external legs are nongauge the source is zero. Need not project ghost sectors.
omit simple hx
def cuts (a:QP)(K:Edge G)(F H:Law G)(l r:Legs (Lane4 G)):ℂ:= Tone.bill a (net l)*(∑ i:Branch G Axis,∑ j:Branch G Axis,∫ q,Tone.bill a q*meshZ K i j F H l r q∂covMeasure Axis)
lemma dims_q (w:Legs (Lane4 G))(a b:Edge G): True:= trivial -- remove
lemma dropL (p:QP){l:Legs (Lane4 G)}(hp:∀ i,F (i::l)=0)(r:Legs (Lane4 G)) : cuts p Y F H l r=0:= by unfold cuts; simp_rw [meshZ,hp]; simp
lemma dropR (p:QP){r:Legs (Lane4 G)}(hp:∀ i,H (i::r)=0)(l:Legs (Lane4 G)) : cuts p Y F H l r=0:= by unfold cuts; simp_rw [meshZ,hp]; simp
lemma wanted (p:QP)(w v:Lane4 G)(f:Law G)(Left: F=E ∨ f=E)(i:ℕ) :
    Cabin p Y μ F f [w,v]= cuts p Y F f [w] [v]+cross (Ψ w) (Ψ v)*cuts p Y F f [v] [w] := by
   change scatter Ψ [w,v] ( cuts p Y F f )=_
   simp only [scatter_cons,scatter_nil, degree_cons,degree_nil,Bool.xor_false,cross_false',one_mul]; rcases Left with h|h
   · rw [h,dropL p ( F:=E ) ( l:=[w,v]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)), dropL p ( F:=E ) (l:=[]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)) ]; abel
   rw [h,dropR p ( H:=E ) ( r:=[w,v]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)), dropR p ( H:=E ) (r:=[]) (fun i=>ranked_N _ (by rw [mod_int];norm_num)) ]; abel
lemma forge (p:QP)(w v:Lane4 G)(f:Law G)(Left: F=E∨ f=E)(i:ℕ)(hq:¬vector w)(hh:¬vector v):Cabin p Y μ F f [w,v]=0:= by
    rw [wanted p w v f Left i]; have he(u:Lane4 G)(h:¬vector u)(j:Lane4 G): E [j,u]=0:= plane_g _ ⟨u,by simp,h⟩
    rcases Left with h|h
    · rw [h,dropL p ( F:=E ) (he w hq),dropL p ( F:=E ) ( he v hh )]; simp
    rw [h,dropR p ( H:=E ) (he v hh), dropR p ( H:= E ) (he w hq) ]; simp

include hx
lemma run_speed (s:Clock ℝ)(w:Legs ( Lane4 G ))(hp:w.length=2):
    HasDerivAt (fun t:ℝ=> U0 0 (s.1,t) w) ( source M x 0 s w ) s.2:= by
    let h:= (anatomy M x hx 0 s.1).2.1 s.2 w; dsimp only at h; rw [ cycle_height _ _ _ w false (fun i=>Bool.noConfusion i) (fun i _ hi=>ground_up M x hx _ i (by omega)),zero_add ] at h; exact h
lemma other_heads (w v:Lane4 G)(hu:¬vector w)(hv:¬vector v)(s:Clock ℝ): U0 0 s [w,v]=0:= by
   apply Lambda.Canvas.regression (f:=fun t:ℝ=> U0 0 (s.1,t) [w,v]) s.2; swap; · exact provisional M x hx 0 _ s.1
   intro t; have hp:= run_speed M x hx (s.1,t) [w,v] rfl; rw [ source0, forge (F:=E) _ w v _ ( Or.inl rfl ) 0 hu hv ] at hp; exact hp

include simple
lemma leap_speed (s:Clock ℝ)(v:ℝ)(w:Legs (Lane4 G))(hp:w.length=2):
    HasDerivAt (fun t:ℝ=>leap v (U0 2) (s.1,t) w) (leap v (source M x 2) s w) s.2:= by
    let h:= (descent2 M x hx v s.1 2).2.1 s.2 w; dsimp only at h; rw [cycle_height _ _ _ w false (fun i=>Bool.noConfusion i) (fun i _ hi=> above M x hx simple v _ _ (by omega) (by omega)),zero_add ] at h; exact h
lemma leap_odd (w v:Lane4 G)(hU:Bubble.wing w)(hV:Bubble.wing v)(s:Clock ℝ)(t:ℝ):
    leap t ( U0 2 ) s [w,v]=0:= by
    apply Lambda.Canvas.regression (f:=fun i:ℝ=> leap t ( U0 2 ) (s.1,i) [w,v]) s.2; swap; · exact ( descent2 M x hx t s.1 2 ).2.2 _
    intro i
    obtain he:= leap_speed M x hx simple (s.1,i) t [w,v] rfl; have hH: leap t (source M x 2) (s.1,i) [w,v]=0:= by
       rw [ source2 M x hx simple t _ ]; simp only [Pi.add_apply]; rw [forge _ _ _ _ ( Or.inr rfl ) 0 (Bubble.side hU) (Bubble.side hV),forge _ _ _ _ ( Or.inl rfl ) 0 (Bubble.side hU) (Bubble.side hV),add_zero,add_zero ]
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
         have hB:Bubble.wing b:= (hφ j k _ hp).trans ( ( Lambda.Bead.since_xor hb ).trans ( show degree Ψ [w]=true from (by simp only [ degree_cons,degree_nil,Bool.xor_false,h ] ; exact h) ) )
         have hu:y [b,v]=0:= other_heads M x hx _ _ (Bubble.side hB) (Bubble.side he) _
         unfold radius; simp only [neg_neg]; rw [ show y [(k,net [w]),v]=0 from hu, mul_zero ]
       change scatter Ψ [w,v] f=_
       rw [scatter_cons,scatter_cons,scatter_nil]; rw [ hn w v hU hV, hn v w hV hU, hm [w,v] [] (by simp), hm [] _ (by simp) ]; simp
    rw [hH] at he; exact he

omit hx simple
lemma empty_energy (F:Law G)(e:QP)(K:Edge G): Cabin e K μ F E []=0 ∧ Cabin e K μ E F []=0 :=
    let hZ(i:Lane4 G): E [i]=0:= ranked_N _ (by rw [mod_int]; norm_num)
    ⟨ dropR e (H:=E) (F:=F) (r:=[]) hZ [],dropL e (F:=E) (l:=[]) hZ [] ⟩
include hx
lemma ground_flow_still (s:Clock ℝ) :
   HasDerivAt (fun t:ℝ=> U0 0 (s.1,t) []) (cycle (Φ s.2) μ (U0 0 s) []) s.2:= by
   have he:= pace_E M x hx 0 s []; unfold triggerP at he; rw [source0, Pi.add_apply, (empty_energy ..).1, add_zero ] at he; exact he
include simple
lemma action_flow_still (s:Clock ℝ)(v:ℝ) :
    HasDerivAt (fun t=>leap v (U0 2) (s.1,t) []) (cycle (Φ s.2) μ (leap v ( U0 2 ) s) []) s.2:= by
    have h:= (descent2 M x hx v s.1 2).2.1 s.2 []; dsimp only at h; rw [source2 M x hx simple] at h; simp only [Pi.add_apply] at h;
    rw [ (empty_energy ..).1,(empty_energy ..).2,tree_height _ _ _ [] false (fun i=> Bool.noConfusion i),add_zero,add_zero,add_zero ] at h; exact h;
    intro i j h; left; intro w _ hv; exact Book.strange _ (by simp at h; omega)

end
end YM.SignedWilsonExpansion.PhasePair
