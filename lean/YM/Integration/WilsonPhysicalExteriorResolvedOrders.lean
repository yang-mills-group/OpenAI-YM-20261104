import YM.Integration.WilsonPhysicalExteriorResolvedFlow

/-! The original temporal and marked-subword recursions (Vane.Peel,
Akin and North) on well-separated inputs with no upper radius. Their
true middle- and late-time tariffs apply to the same signed story. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorResolved
open Set Function Filter Finset Metric MeasureTheory Real
open YM.MS
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City Vane Land Menus
open scoped Topology ContDiff Interval Classical

section
variable { I E J:Type}{G: Gauge}[ LinearOrder J ]{s:Finset J}{P:Geo I}{R: J→ℕ}{x:Position J I}
 {K L: Planet G I} {b:Bool} {X: Site G I}{A:J→Site G I}{Y: Dance G I J}{n k d:ℕ}{F H: Glade G I}{μ:I→Measure QP}
local notation "Ϋ"=> Gulf P
local notation "m0"=> (fun (_:I)=>planeF)
variable (h: Source K L P x b X A R)(hx: Fields x (fun _=>planeF) K L X A Y)(hu:Arch ( Gulf P ) K L X A R)
include h hu
lemma germS (_hp:2≤s.card)(n:ℕ)(hv:∀ t⊂ s,t.Nonempty→∀ i,Here false false Ϋ ( Y t i ) ( rateS Ϋ ( charge R t )))(hK:∀ i<n,Bud P (charge R s) 0 (Y s i)): Bud P (charge R s) 0 (Src x (fun _=>planeF) K L X Y s n):= by
    intro k; refine Lease.plus ?l ?r
    · exact He_here (K:=Gulf P) (Domain.paths n 0) (fun i hi=> ( shines Ϋ hu.main ( hu.states (n-i) (by obtain hp: i<n:= ( Finset.mem_Ico.mp hi ).2; omega)) (( hK i ( Finset.mem_Ico.mp hi|>.2 ) k ).highp) (raised P 0 (charge R s) k) )) ( raised _ _ _ _ ) -- unfold Src site.Actor ∑ & Λ
    · --  -- issue state after plus Lean metavars
      refine He_here (K:=Gulf P) _ (fun i hi=> He_here (K:=Gulf P) _ (fun k hk=> ?_) ( raised _ _ _ _ )) ( raised _ _ _ _ )
      obtain ⟨ Q,hg,H,hJ⟩:= n_small hi; rw [← toll_charge R Q.le]; exact lighting hu.χ ( WilsonPhysicalExteriorUVStory.split h.plot hi ) ((hv i Q hg k.1).highp) (( hv _ hJ H k.2 ).highp) _
include hx
lemma moon (hs:s.Nonempty)(n:ℕ): Here false false Ϋ ( Y s n ) ( rateS Ϋ (charge R s) ) ∧ ( s.card≥2→ Bud P (charge R s) 0 ( Y s n )) := by
    induction s using Finset.strongInductionOn generalizing n with| _ s ih=>
       by_cases hp:s.card≥2; swap; · obtain ⟨k,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain hx:= Finset.card_pos.mpr hs; omega); refine ⟨?_,fun h=>False.elim (hp h)⟩; rw [hx.2.1]; simpa only [charge,Finset.sum_singleton] using hu.first k n -- `first` gives ∀ t≥ all.
       induction n using Nat.strong_induction_on with | h n hM=>
          suffices he: Bud P (charge R s) 0 ( Y s n ) from ⟨ more he,fun _=> he⟩; intro k; let F:= Y s n; let H:= Src x (fun _=>planeF) K L X Y s n; let Q:=charge R s; let N:=k+Q+1; let V:=Gulf P; let p:= life P Q N 0; have he:= Fits.positiveR (P:=P) (motion h hx hs n); have hU:= emerged h hx hp n; have hi : 0<( N-Q-(0:ℝ) ):= by unfold N; push_cast; linarith
          have hc:Bud P Q 0 H:= germS h hu hp n (fun t ht hs n=> (ih t ht hs n).1) (fun i hi=> (hM i hi).2 hp );
          apply Lease.sticks (S:=V.price) (f:=plug F) _ (tilt (P:=P) ( x:=0 ) ( h:=Q ) (show k≤ N from by unfold N; omega)); refine marching (εGulf P) ( raised _ _ _ _ ) ( winter h hx hs n|>.walk ) he ( Midland hi.le b ( hU.1.pick N )) ( aboveC V false hU.2 ) ?_
          intro r hr hF E _ _ _ w hw ht; obtain ⟨ε,hε,hS⟩:= fertile (P:=P) hi E w ht (fun h=> Bool.noConfusion h); have hW := penny hF ( raised _ _ _ _) hu.χ ( fun i=> zero_le_one ) (Tall V.price 5 (by omega)) (fun E _=> tom V.price 5 (by omega) ); rw [one_mul] at hW; exact ⟨_,_,hε, Lens.plus hW ( pinch ( hc N ) hr ) E w hw ht, hS⟩
end

section
variable { I W:Type}{G:Gauge} [LinearOrder W] {P: Geo I}{F H:Glade G I}{x: Position W I} {c:Bool}{m k n:ℕ} {K L: Planet G I}
    {X Y: Site G I}{A : W→ Site G I}{U:Dance G I W}{J : Finset W}{R: W→ℕ}{Y':I→QP}
local notation "Ϋ"=> West P
variable (h: Source K L P x c X A R)
variable (he:Arch ( Gulf P ) K L X A R)(hu:Arch (West P) K L X A R)(ht: Fields x (fun _=>planeF) K L X A U)
local notation "ι0"=> (fun (_:I)=>planeF)
include hu
lemma berth (_hs:J.Nonempty)(n:ℕ)(hx:∀ v⊂ J,v.Nonempty→ ∀ i, mail P ( charge R v) 0 ( U v i ))(hp:∀ i<n,mail P ( charge R J) 0 ( U J i )): Fed P (charge R J) 0 (Src x ι0 K L X U J n ):= by
    refine Lease.plus ?l ?r
    · exact He_here (K:=West P) (Domain.paths n 0) (fun i hi=> shines Ϋ hu.main ( hu.states (n-i) ( by obtain hv:i<n:=( Finset.mem_Ico.mp hi).2; omega )) ( hp i ( Finset.mem_Ico.mp hi |>.2 )) ( FarBasis _ _ _ )) ( FarBasis _ _ _ )
    refine He_here (K:= West P ) _ (fun i hi=> He_here (K:=West P) _ (fun k hk=> ?_) ( FarBasis _ _ _ )) ( FarBasis _ _ _ ); obtain ⟨H,hV,hZ,hT⟩:= n_small hi; rw [ ← toll_charge R H.le ]; apply Lease.sticks ( fossil hu.χ ( hx _ H hV _ ) ( hx _ hT hZ _ ) (FarBasis _ _ _) ( FarBasis _ _ _ ) (fun i=> zero_le_one) ); exact fun i=> by simp only [ Pi.mul_apply, Pi.one_apply,one_mul]; simpa using tax_far (x:=0) (y:=0) ( charge R _ ) ( charge R _ ) i -- placeholders `_` fail
include h ht he
lemma farther (hs:J.Nonempty)(n:ℕ): mail P (charge R J) 0 ( U J n ):= by
    induction J using Finset.strongInductionOn generalizing n with| _ J ih=>
      induction n using Nat.strong_induction_on with| h n hz=>
        have hx:= berth (x:=x) hu hs n ih hz; obtain hF:= motion h ht hs n; obtain hm:= moon h ht he hs n|>.1; rw [dotzero] at hm; refine marching ( εWest P ) (FarBasis _ _ _) hF.stroll ( Wharf hF ) (hop hm ) ( aboveC Ϋ false ( founded h ht hs n |>.1 )) ?_
        intro r hv hp E _ _ _ w hw hk; have hs:= LensC hu.χ hp ( FarBasis _ _ _ ); obtain ⟨ α,hα,hJ⟩:= broken ( P:=P ) (h:=charge R J) (x:=0) E w hk (hw ▸ hv); exact ⟨ _,α,hα, Lens.plus hs ( pinch hx (fun x=>Bool.noConfusion x)) E w hw hk, hJ ⟩
lemma recall (hs:J.Nonempty)(n:ℕ): Fed P (charge R J) 0 ( rhs x ι0 K L X U J n ):= by refine Lease.plus ?cycle ( berth (x:=x) hu hs n (fun i hi hs n=> farther h he hu ht hs n) (fun _ _=>farther h he hu ht hs _) ); exact poses (fun i _=> LensC hu.χ ( pinch (farther h he hu ht hs n) (fun _=> by omega) ) ( FarBasis _ _ _ )) -- order
end

section

variable {I : Type} {G : Gauge} {P : Geo I} {L L' : Planet G I}
  {F H X Y:Glade G I} {ξ:I→QP} {d r : ℕ}
local notation "Ϋ"=> Gulf P
lemma boats (hc: Pair P ξ)(he:Flow Ϋ L 1)(hf: Flow Ϋ (L-L') (chips (Gulf P))) (hu: Here false true Ϋ F (rateS Ϋ d))(hH:Here false true Ϋ H ( rateS Ϋ d )) (hp: Here false true Ϋ ( F-H ) (chips Ϋ*rateS Ϋ d ))( hv: Here false true Ϋ Y (rateS Ϋ r))( ht: Here false true Ϋ ( X-Y ) (chips Ϋ*rateS Ϋ r)) (hw:Warm H false)(hw':Warm F false)(hV:Warm X false)(hV': Warm Y false)(hb: BackF L)(hh:BackF L'): Bud P (d+r) eps_gain ( regionC (fun _=>planeF) ξ L F X-regionC (fun _=>planeF) ξ L' H Y )  := by
  obtain ⟨t,hpos,hsep⟩ := hc
  intro k
  exact WilsonPhysicalExteriorUVStory.constant_price (pow_pos hpos k)
    (WilsonPhysicalExteriorUVJoin.signed he hf hu hH hp hv ht hw hw' hV hV' hb hh
       (fun _=>t) (fun _=>hpos.le) hsep k)
end

section
variable { I W:Type}{G:Gauge}[LinearOrder W] {P: Geo I}{x: Position W I}{R:W→ℕ}{K L K' L':Planet G I}{F H:Glade G I}
  {c b:Bool} {A B: Site G I}{X Y: W→ Site G I}{U V: Dance G I W}{n h:ℕ}
local notation "Ϋ"=> Gulf P
-- combine proof both.Now nested budgets.Source & Arch.
structure History (P:Geo I) (x:Position W I) (μ: I→Measure QP)(R:W→ℕ)(b:Bool)(K L:Planet G I)(A:Site G I)(X: W→ Site G I)(U:Dance G I W): Prop where
   tour : Source K L P x b A X R
   fields : Fields x μ K L A X U
variable (T: History P x (fun _=>planeF) R b K L A X U)(T': History P x (fun _=>planeF) R c K' L' B Y V)(M: Arch (Gulf P) K L A X R)(N: Arch (Gulf P) K' L' B Y R)(J: ArcS (Gulf P) K L K' L' A B X Y R)
include T T' M N J
lemma tissue (S:Finset W)(n:ℕ)(hs:S.Nonempty)(hz:∀ v⊂ S,v.Nonempty→∀ k, Here false false Ϋ (U v k-V v k) (chips Ϋ*rateS Ϋ (charge R v)))(hf:∀ i<n,Bud P ( charge R S) eps_gain ( U S i-V S i ))(hp:2≤ S.card): Bud P (charge R S) eps_gain ( Src x (fun _=>planeF) K L A U S n - Src x (fun _=>planeF) K' L' B V S n ):= by
   let W0 i:= life P ( charge R S ) i eps_gain; intro k; unfold Src multi lonely; rw [ add_sub_add_comm,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; apply Lease.plus
   · refine He_here (K:=Gulf P) _ (fun i hi=>?_) ( raised _ _ _ _ ); obtain he:i<n:= Finset.mem_Ico.mp hi |>.2; obtain hK : n-i>0:= by omega; -- change.S
     have hv:= hf i he k; rw [ show life P _ k eps_gain =_ from alter P ( charge R S ) k ] at hv ⊢; exact Trees M.main J.main ( N.states _ hK ) ( M.states _ hK ) ( J.states _ hK ) ( ( (moon T'.tour T'.fields N hs i).2 hp k ).highp ) hv.highp ( raised _ _ _ _ ) cul
   · refine He_here ( K:=Gulf P ) _ (fun i hi=>?_) ( raised _ _ _ _ ); obtain ⟨H,hx,h,h'⟩:= n_small hi; rw [← Finset.sum_sub_distrib, ← toll_charge R H.le]; refine He_here (K:= Gulf P) _ ( fun j hj=>?_ ) ( raised _ _ _ _ ); --
     exact boats (WilsonPhysicalExteriorUVStory.split T.tour.plot hi) M.χ J.χ ( (moon T.tour T.fields M hx j.1).1.highp ) ( ( moon T'.tour T'.fields N hx j.1).1.highp ) ( (hz _ H hx j.1).highp ) ( ( moon T'.tour T'.fields N h j.2).1.highp ) ( (hz _ h' h j.2).highp ) ( founded T'.tour T'.fields hx _|>.2 ) (founded T.tour T.fields hx _|>.2 ) ( founded T.tour T.fields h _|>.2 ) ( founded T'.tour T'.fields h _|>.2 ) T.tour.ground.pool T'.tour.ground.pool k
lemma tokens (S:Finset W)(n:ℕ)(hs:S.Nonempty): Here false false Ϋ ( U S n-V S n ) (chips Ϋ*rateS Ϋ (charge R S)) ∧ ( S.card≥2→ Bud P (charge R S) eps_gain ( U S n-V S n ) ) := by
   induction S using Finset.strongInductionOn generalizing n with| _ S ih=>
      by_cases hu:2≤ S.card; swap; · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show S.card=1 from by obtain he:= Finset.card_pos.mpr hs; omega); refine ⟨?_,fun h=>False.elim ( hu h )⟩; rw [ T.fields.2.1, T'.fields.2.1, mul_comm, charge, Finset.sum_singleton ]; exact J.first i n
      induction n using Nat.strong_induction_on with| h n hx=>
        suffices he: Bud P (charge R S) eps_gain ( U S n-V S n ) from ⟨ marketing he,fun _=> he⟩; intro k; let r:=charge R S; let ℓ:= k+r+1; have hK : 0<( ℓ-r-eps_gain:ℝ):= by change 0< (( (k+r+1:ℕ):ℝ) - _ - 1/2 ); push_cast; linarith
        let X0:= Src x (fun _=>planeF) K L A U S n; let Y0:= Src x (fun _=>planeF) K' L' B V S n; let F:= sailP (fun _=>planeF) L; let G:= sailP (fun _=>planeF) L'; let Jw:=U S n; let H:=V S n; let D:= Jw-H; let W:=( F Jw-G H )+(X0-Y0); obtain hx':Here false false Ϋ (X0-Y0) ( life P r ℓ eps_gain ) := tissue T T' M N J S n hs (fun i hi hp k=>( ih i hi k hp ).1) (fun j hj=>(hx j hj).2 hu ) hu ℓ; -- ih order?
        have hB: Fits false D W:= by unfold W; rw [← add_sub_add_comm]; exact Fits.subFit (motion T.tour T.fields hs n) (motion T'.tour T'.fields hs n); -- parser
        have hu' := emerged T.tour T.fields hu n; have hv:= emerged T'.tour T'.fields hu n;
        apply Lease.sticks (f:=plug D) _ (tilt (P:=P) ( m:=k) (n:=ℓ) (x:=eps_gain) ( h:=r ) (by unfold ℓ; omega)); refine marching (εGulf P) (raised _ _ _ _ ) hB.stroll ( Fits.positiveR hB ) ( Lease.minus (Midland hK.le b (hu'.1.pick ℓ)) (Midland hK.le c (hv.1.pick ℓ)) ) (aboveC Ϋ false ( combine hu'.2 hv.2 )) ?_; intro i hi hF E _ _ _ w hw ht; obtain ⟨ε,hε,hS⟩:= fertile (P:=P) hK E w ht (fun p=> Bool.noConfusion p); refine ⟨ _,_,hε, ?_,hS⟩;
        refine Lens.plus (F:=plug (F Jw-G H)) ?_ ( pinch hx' hi ) E w hw ht; rw [show life P r ℓ eps_gain= _ from alter P r ℓ] at *; exact LensD M.χ J.χ hF (pinch ( (moon T'.tour T'.fields N hs n).2 hu ℓ ) (fun x=> Bool.noConfusion x)) hu'.1.mood hv.1.mood T.tour.ground.pool T'.tour.ground.pool cul ( raised P 0 r ℓ )
end

end YM.Integration.WilsonPhysicalExteriorResolved
