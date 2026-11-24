import YM.FVA2.PolyJet
/-!
# How the implicit signal supplies flow with *polynomial* (logarithmic) dependence

 Height step interpolation; no asserted derivative wrt picture until using log law.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace YM.FVA2.Legacy
open Function Filter Set MeasureTheory Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode Ember Pic Forge
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide MS.Book MS.Book.Program MS.Book.Convolve Clock
open Hop
open scoped Topology ContDiff Classical
variable {G:Gauge} {F: Labels.Frames G} {v:ℝ} {d m:ℕ}
section panel
variable (Z: ℝ→ Word ( Bank F d )){u:Bank F d} (A:ℝ→ Word (Buffer F d))
-- basis or profile.
def Bud := ∀ p:Pert.Position.Section F d, polynomial (fun t=> lookie F p ∘ Z t)
variable (h: Bud Z)(v:Section F d)(D:Detector F d)(p:Test m)
local notation "T"=> Rail.Target D.rail
include h
lemma exposes : polynomial (fun t=> expose F p ∘ Z t):= fun i=> WearPi (fun k=> h ⟨ _,baring F d∘k,p ⟩ i)
lemma interests : polynomial (fun t=> D.read ∘ Z t):= fun i=> WearPi (fun k=> exposes Z h ( D.rail.reachedV k|>.f ) i)
lemma presents (hp:∀t,Z t 0=pureBank F d) : polynomial fun t=> D.report (Z t):= progress ( z:=D.read (pureBank F d) ) (interests Z h D) (fun i=>congr_arg D.read (hp i)) _ (Jet.pick_nice (lucid D))
lemma paints (he:polynomial A)(hu:∀t, Z t 0=u)(ha:∀t,Stable (A t)): Bud (fun t=> predMarket ( A t ) ( Z t )):= by
    intro p i; simp_rw [Function.comp_apply, Ribbon.all_tips (s:=p) ]; exact progress (z:=(expose F p.f u,0)) ( both ( exposes Z h p.f ) he ) ( fun t=> Prod.ext ( congr_arg (expose F p.f) ( hu t ) ) (ha t)) _ ((cross_smooth _ p.p).contDiffAt) i -- code? projected Def
end panel
section grip
variable (D:Detector F d) (A:ℝ→ Word ( Buffer F d ))
lemma guarding (h:polynomial A)(he:∀t:ℝ,Stable ( A t )): polynomial fun t=> Verne.undo ( A t ) D:= by
    let V:= just (pureBank F d); let X(t):=predMarket (A t) V;
    refine presents X ?_ D (fun i=> Verne.dawn (A i) V ( he i ) (if_pos (rfl:(0:ℕ)=0))) -- fix.
    exact paints (fun (_:ℝ)=> V) A (fun _ k=> Ready.const _) h (u:=V 0) (fun _=>rfl) he
variable {r:ℝ}(Bz:ℝ→ Word ( Bank F 6 ))(R:Booth r F)
lemma brightness (hp:Bud Bz)(hv:∀t, Bz t 0=pureBank F 6): polynomial fun t=> metricT R ( Bz t ):= by
    let f:= Board7 F R.r1; let u(t):= Wanted R.r1 ( Bz t );
    have hn : polynomial ( fun t=>f ∘ Bz t ):= fun i=> WearPi ( fun k=> hp _ i );
    have ht : polynomial u:= progress hn (z:= f (pureBank F 6)) ( fun i=> congr_arg f (hv i) ) _ rank_smooth.contDiffAt;
    intro i; rcases Nat.eq_zero_or_pos i with hi|hi; · subst i; simp_rw [ show ∀t, metricT R (Bz t) 0=0 from fun _=> metric_zero .. ]; exact Ready.const _
    have hm (s): metricT R ( Bz s ) i= R.normalC⁻¹ • ( u s i ).re:= by unfold u metricT Bend.haze; simp [ just,Nat.pos_iff_ne_zero.mp hi ];
    simp_rw [hm]; exact Ready.scale_p ( Ready.linear ( ht _ ) ( Complex.reCLM.toLinearMap )) _
lemma wen {u:ℝ→ Word (Buffer F d)}(hu:polynomial u)(hv:∀t,Stable ( u t ))(h:polynomial A)(he:∀t,Stable ( A t )): polynomial fun t=> luxury ( u t ) ( A t ):= progress (z:=( (0,0): Buffer F d×Buffer F d)) ( both hu h ) ( fun t=> Prod.ext ( hv t ) (he t)) _ (Ribbon.settled_diff.contDiffAt)
def habit (U:ℝ→Hop F): Prop:= (∀ d,polynomial fun v=> ( U v ).Z.wire d ) ∧ polynomial fun v=>(U v).f
variable {T K:ℝ→Hop F}(hx:habit T)
include hx
lemma habit_mul (hp:habit K): habit (fun v=> T v*K v):= by
    unfold habit; simp_rw [walkZ,walkF, pay, resume_wire ]; exact ⟨ fun d=> wen _ ( rename (hx.1 d) _ hp.2 ) ( fun t=> Verne.fast ( ( T t ).Z.wire d ) ((T t).tangent _) ( K t ).rooted ) (hp.1 d) (fun t=> (K t).tangent _ ), rename hx.2 _ hp.2⟩ -- args
lemma stead (D:∀i,Detector F i) : habit (fun t=> undoV ( T t ) D):= by
    have he:= inverseM hx.2 (fun i=> ( T i ).loved) (fun i=> ( T i ).primary); refine ⟨ fun i=> ?_,he⟩; exact rename (guarding (D i) (fun t=> ( T t ).Z.wire i ) (hx.1 i) (fun t=>(T t).tangent i)) _ he
lemma flowμ (p: Polynomial ℝ): habit (fun t=> T (p.eval t)):= ⟨ fun i k=> Ember.poly_rot p (hx.1 i k), fun k=> Ember.poly_rot p (hx.2 k) ⟩
omit hx
lemma constantV (U:Hop F): habit (fun _ :ℝ=>U):=⟨ fun _ _=> Ready.const _, fun _=>Ready.const _ ⟩
end grip
section install
variable (V : Warehouse G) (h:G.Simple) {O:Booked (wings G)}(M: MS_Data G O) {r:ℝ} (R:Booth r V.F) (Sx:Pic.pass V h M R)
local notation "Tφ"=> nested V.F h (BoxOffice.warehouse V)
local notation "η"=> Pic.marked V M
lemma sales (d:ℕ) : Bud ( fun t=> Spring.ms V M t d ):= by
    intro p k; let m:=p.r; let S:= sameAxis V.F d; let a(t:ℝ):= Spring.ms V M t d;
    have he(i:Fin m→ BasisIx G d): Ready (fun t:ℝ=> a t k m p.f ( S ∘ i )):= by
       obtain ⟨n,hN⟩:= time_marked V M k (w:=i); let x(t:ℝ)(y:Points m):= PayAll.taste ( ( η t ).off d y ) ( S∘i ) k; let s p:=(p:ℕ); let u(t:ℝ):= a t k m p.f (S ∘ i);
       have ht(t:ℝ): u t=p.f.applyTo (x t):= by unfold u a; rw [← Pic.payMark V M t d ]; exact Panel.newly _ _ _ _ ( clearMark V M t )
       have hw (t:ℝ) : p.f.applyTo (x t)= p.f.applyTo ( fun y=>∑ j∈Finset.range n,(Logarithm.plate n j).eval t • (x j y) ):= by
          apply Test.apply_eq; intro a ha; unfold x
          have hh:= congr_fun ( interpret hN t ) (show Polyp m from ⟨ a,ha ⟩ ); unfold Logarithm.evaluate at hh; rw [ Finset.sum_apply ] at hh; simp_rw [ Panel.sees _ ha ]; exact hh -- indexes rw eta
       convert eval_ready n u using 1; funext t; change u t=_; rw [ht,hw ]; unfold Logarithm.evaluate; simp_rw [ht,Test.applyTo,Complex.real_smul, Finset.mul_sum, mul_left_comm ( p.f _ ) ( _ :ℂ ) ]; rw [ MeasureTheory.integral_finsetSum ]; simp_rw [ integral_const_mul ]; exact fun i hi=> (p.f.smearing ( Pic.clearMark V M i _ _ k ( S∘_) )).const_mul _
    let c(i:Fin m→ BasisIx G d):ℂ:= ∏ j,S.coord ( i j ) ( p.p j ); let U(t:ℝ)(i:Fin m→ BasisIx G d):= c i * ( a t k m p.f ( S ∘ i )); have hr(t:ℝ) : lookie V.F p (a t k)= ∑ i:Fin m→ BasisIx G d,U t i:= WorldJet.countr V.F S ( a t k m p.f ) p.p
    change Ready fun t=> lookie V.F p ( a t k ); simp_rw [hr]; exact MS.FV2Mod.latSum _ ( fun i _=> Ready.pair (LinearMap.mul ℝ ℂ) ( Ready.const _ ) (he i))
include Sx
lemma L_poly (d:ℕ): polynomial (fun t:ℝ=> (Forge.Pay V M R Sx t).Z.wire d) ∧ polynomial (fun t:ℝ=>(Forge.Pay V M R Sx t).f):= by
    let a(y:ℝ)(i:ℕ):= Spring.ms V M y i; let P(t:ℝ):=( Tφ 6 ).report ( a t 6 ); have hx₀(z:ℕ): polynomial (fun t:ℝ=> (Tφ z).report ( a t z )):= presents _ ( sales V M z ) ( Tφ z ) ( fun t=> Spring.vintage_ms .. ); let p(t):= Elegant.ξ h V M t R; have H:Bud ( fun t=> predMarket ( P t ) ( a t 6 ) ):= paints _ _ ( sales V M 6 ) (hx₀ 6) ( u:=pureBank V.F 6 ) ( fun t=> Spring.vintage_ms .. ) ( fun t=>Elegant.reports0 .. );
    have ht : polynomial p:= brightness _ R H ( fun t=> Elegant.preserves .. ); have hx:= inverseM ht Sx.lens Sx.lane; exact ⟨ rename (hx₀ d) _ hx,hx ⟩
lemma debut_m (v:ℝ) : habit (fun t:ℝ=> Forge.diffuse V M R t v Sx):= by
    let P:= Forge.Pay V M R Sx; have he: habit P:=⟨ fun i=> (L_poly V h M R Sx i).1,( L_poly V h M R Sx 0 ).2⟩ ; let p:Polynomial ℝ:= Polynomial.C v-Polynomial.X;
    have hp:habit (fun t=>undoV ( P (v-t) ) Tφ):= by convert stead ( flowμ he p ) Tφ using 1; ext1 t; simp [p] -- args
    exact habit_mul (constantV ( P v )) hp
end install
end YM.FVA2.Legacy
