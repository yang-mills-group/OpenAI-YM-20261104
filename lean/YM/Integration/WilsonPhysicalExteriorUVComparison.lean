import YM.Integration.WilsonPhysicalExteriorResolvedOrders

/-! The genuine original all-orders finite-cover MS/Lit subtraction on
separated interior operators and far probes with unbounded outer radius.
The entire signed difference is estimated before applying a Gram inverse. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorResolved
open Set Function Filter Finset Metric MeasureTheory Real
open YM.MS
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City Vane Land Menus
open scoped Topology ContDiff Interval Classical

section
variable { I W:Type}{G:Gauge}[LinearOrder W]{P:Geo I}{x:Position W I}{R:W→ℕ}{K L K' L':Planet G I}{F H D N:Glade G I}
  {ξ:I→QP}{c b:Bool}{X Y:Site G I}{A B: W→ Site G I}{U V:Dance G I W}{n h k:ℕ}
local notation "Ϋ"=> West P
local notation "Θ"=> coinZ P
variable (T: History P x (fun _=>planeF) R b K L X A U)(T':History P x (fun _=>planeF) R c K' L' Y B V)
  (Z: ArcS (Gulf P) K L K' L' X Y A B R)(M:Arch ( Gulf P) K L X A R)(M': Arch ( Gulf P ) K' L' Y B R)
  (W0: Arch ( West P ) K L X A R)(W1: Arch ( West P ) K' L' Y B R)(Z0: ArcS ( West P ) K L K' L' X Y A B R)
include Z0
include W0
omit [LinearOrder W] in
lemma blast (hv:mail P h 0 F)(hv':mail P h 0 H)(hD:mail P h eps_gain ( F-H ))(ht:mail P k 0 N)( ht':mail P k eps_gain ( D-N )) (hw:Warm H false)(hF:Warm F false)(hN:Warm N false)(ha:Warm D false): BackF L→BackF L'→ Fed P (h+k) eps_gain (regionC (fun _=>planeF) ξ L F D - regionC (fun _=>planeF) ξ L' H N):= by
   intro hL hM; unfold mail at hD ht'; rw [zeta] at hD ht'; refine parkD hv hv' hD ht ht' hw hF ha hN hL hM (fun _=>Coherent) ?_ ?_ ?_; all_goals intro x y h1 h2
   · rw [← zeta] at h2; apply Lease.sticks ( fossil W0.χ h1 h2 (FarBasis _ _ _) ( FarBasis _ _ _ ) (fun i=>zero_le_one) ); exact fun i=>( by simpa using tax_far (x:=0) (y:=eps_gain) h k i )
   · rw [← zeta] at h1; apply Lease.sticks ( fossil W0.χ h1 h2 (FarBasis _ _ _) ( FarBasis _ _ _ ) (fun i=>zero_le_one) ); exact fun i=> ( by simpa using tax_far (x:=eps_gain) (y:=0) h k i )
   apply Lease.sticks ( fossil ( globX Z0 ) h1 h2 ( FarBasis _ _ _ ) ( FarBasis _ _ _ ) γ_non ); rw [zeta]; exact fun i=> mul_le_mul_of_nonneg_left (by simpa using tax_far (x:=0) ( y:=0 ) h k i ) ( γ_non i ) -- side Coord
include M M' W1 T T'
local notation "m0"=> (fun (_:I)=>planeF)
lemma beam (S:Finset W)(hs:S.Nonempty)(hv:∀ t⊂ S,t.Nonempty→∀ i, mail P (charge R t) eps_gain ( U t i-V t i ))(hN:∀ i<n,mail P (charge R S) eps_gain ( U S i-V S i )): Fed P (charge R S) eps_gain ( Src x m0 K L X U S n-Src x m0 K' L' Y V S n ):= by
   unfold Src multi lonely; rw [ add_sub_add_comm,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; refine Lease.plus ?l ?r
   · refine He_here (K:=West P) _ (fun i hi=>?_) ( FarBasis _ _ _ ); obtain hK:i<n:= Finset.mem_Ico.mp hi|>.2; obtain hu:n-i>0:=(by omega); have hV:= hN i hK; unfold mail at hV; rw [ zeta ] at hV ⊢; exact Trees W0.main ( γK Z0 ) ( W1.states _ hu ) ( W0.states _ hu ) ( Vψ Z0 _ hu ) ( farther T'.tour M' W1 T'.fields hs i ) hV ( FarBasis P _ _ ) γ_non
   refine He_here (K:=West P) _ (fun i hi=> ?_ ) ( FarBasis _ _ _ ); obtain ⟨Q,hP,hU,hM⟩:= n_small hi; rw [← Finset.sum_sub_distrib, ← toll_charge R Q.le]; refine He_here (K:=West P ) _ (fun k hk=> blast W0 Z0 ( farther T.tour M W0 T.fields hP k.1 ) (farther T'.tour M' W1 T'.fields hP k.1) (hv i Q hP k.1 ) (farther T'.tour M' W1 T'.fields hU k.2) (hv _ hM hU k.2) ( founded T'.tour T'.fields hP k.1 |>.2 ) ( founded T.tour T.fields hP k.1 |>.2 ) ( founded T'.tour T'.fields hU k.2 |>.2 ) ( founded T.tour T.fields hU k.2|>.2 ) T.tour.ground.pool T'.tour.ground.pool ) ( FarBasis _ _ _ ) -- order blast.
include Z
lemma heights (S:Finset W)(n:ℕ)(he:S.Nonempty): mail P ( charge R S) eps_gain ( U S n-V S n ):= by
   induction S using Finset.strongInductionOn generalizing n with | _ S hi=>
      induction n using Nat.strong_induction_on with | h n hv=>
        have hp:= beam T T' M M' W0 W1 Z0 S he (fun i h hP k=>hi i h k hP) hv; let D:= rhs x m0 K L X U S n-rhs x m0 K' L' Y V S n
        have hm: Fits false ( U S n-V S n ) D:= ( motion T.tour T.fields he n ).subFit (motion T'.tour T'.fields he n ); have hh := tokens T T' M M' Z S n he|>.1; rw [ dotzero, ← alter ] at hh; obtain ⟨hA,hP⟩:= founded T.tour T.fields he n; obtain ⟨hY,hM⟩:= founded T'.tour T'.fields he n
        refine marching (εWest _) ( FarBasis _ _ _ ) hm.stroll (Wharf hm) (hop hh) ( aboveC Ϋ false ( combine hA hY ) ) ?_; intro r hr h E _ _ _ w hw ht; obtain ⟨α,hα,hL⟩:= broken (P:=P) (h:=charge R S) (x:=eps_gain) E w ht (hw ▸ hr); refine ⟨ _,_,hα,?_,hL⟩; -- delta.Lens
        unfold D rhs; rw [ add_sub_add_comm ]; have hx := pinch hp ( r:=r ) (fun h=>Bool.noConfusion h); apply Lens.plus _ hx E w hw ht; rw [zeta] at *; exact LensD W0.χ (globX Z0) h ( pinch (farther T'.tour M' W1 T'.fields he n) (fun _=> by omega) ) hP hM T.tour.ground.pool T'.tour.ground.pool γ_non (FarBasis _ _ _ ) -- dot
lemma economics (S:Finset W)(hp:S.Nonempty)(n:ℕ): Fed P ( charge R S ) eps_gain ( rhs x m0 K L X U S n-rhs x m0 K' L' Y V S n ):= by
    unfold rhs; rw [add_sub_add_comm]; obtain hv:= heights T T' Z M M' W0 W1 Z0; refine Lease.plus ?p ( beam T T' M M' W0 W1 Z0 S hp (fun i hi he k=> hv i k he) (fun i j=>hv _ i hp) ); apply Job.poses; intro r he; obtain hx:= hv S n hp; unfold mail at hx; rw [zeta] at hx ⊢; exact LensD W0.χ (globX Z0) ( pinch hx (fun _=>by omega) ) (pinch ( farther T'.tour M' W1 T'.fields hp n ) (fun _=>by omega) ) ( founded T.tour T.fields hp n|>.2 ) ( founded T'.tour T'.fields hp n|>.2 ) T.tour.ground.pool T'.tour.ground.pool γ_non (FarBasis _ _ _ ) -- ensure $plug unify
end

section
variable { I W:Type}{G:Gauge}{P:Geo I}
variable { J:Type}[LinearOrder W]{x:Position W I}{c b:Bool}{K L K' L':Planet G I}{B B': Site G I}{A A':W→Site G I}{R:W→ℕ}{p:ℝ}{U V:Dance G I W}{S:Finset W}{v:I→ℝ}
local notation "m0"=> (fun (_:I)=>planeF)
variable (h₂:Source K L P x b B A R)(hx:Source K' L' P x c B' A' R)
    (M: Arch ( Gulf P ) K L B A R) (M':Arch ( Gulf P ) K' L' B' A' R)(N:Arch (West P) K L B A R)(N': Arch ( West P ) K' L' B' A' R)(Z:ArcS ( Gulf P ) K L K' L' B B' A A' R)(Z':ArcS ( West P ) K L K' L' B B' A A' R)
include h₂ M N
lemma closure (H:Fields x m0 K L B A U)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) 0 ( U S n ):= by
    obtain he:= motion h₂ H hp n; obtain hu:= recall h₂ M N H hp n; obtain ⟨hv,hz⟩:= saleable he hu; have H':= moon h₂ H M hp n|>.1; rw [dotzero] at H'; exact ⟨ hv,hz,titel H' hu he ⟩
include hx M' N' Z Z'
lemma trade (H:Fields x m0 K L B A U) (H': Fields x m0 K' L' B' A' V)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) eps_gain ( U S n-V S n ):= by
   let T:History P x m0 R b K L B A U:= ⟨ h₂,H ⟩; let T':History P x m0 R c K' L' B' A' V:= ⟨ hx,H' ⟩; obtain hm:= economics T T' Z M M' N N' Z' S hp n; obtain ht:= tokens T T' M M' Z S n hp|>.1; rw [dotzero, ← alter] at ht; have hv:= Fits.subFit ( motion h₂ H hp n ) ( motion hx H' hp n ); obtain ⟨ hU,hW⟩:= saleable hv hm; exact ⟨ hU,hW,titel ht hm hv ⟩
end

section
variable {I W : Type} [LinearOrder W] {G : Gauge} {B : Local.Physical.Deck G} {O : Land.Booked B}
  {x : Position W I} {P : Geo I}
variable (M : Land.MS_Data G O) (V : LitBook B) (T : Prescription B) (u : W→Label B)
abbrev lattice := story x (fun _=>planeF) (constantP G I (LowP G))
    (constantP G I (PlanetL G)) (initials P T) (rowK V P T ∘ u)
abbrev dimensional := story x (fun _=>planeF) (constantP G I (PlanetD G))
    (constantP G I (PlanetD G)) (approach P M) (rowM P M ∘ u)

/-- The original signed terminal cover quantities at every separated
independent set of positions, own bare and MS data, true spectrum, and
prescribed engineering charge. The independently moving far positions
contribute no upper-radius factor to the ultraviolet bound. -/
theorem comparison (hG : G.Simple) (hx : WilsonPhysicalExteriorUVStory.Resolved P x)
    (ht : TaylorOK M V T) (s : Finset W) (hs : s.Nonempty) (k : ℕ) :
    let d:=charge (Label.h ∘ u) s
    let F:=lattice (x:=x) (P:=P) V T u s k
    let H:=dimensional (x:=x) (P:=P) M u s k
    Verdict P d 0 F ∧ Verdict P d 0 H ∧ Verdict P d eps_gain (F-H) ∧
      title P eps_gain d (blade F-blade H) := by
  have L : Source (constantP G I (LowP G)) (constantP G I (PlanetL G)) P x true
      (initials P T) (rowK V P T ∘ u) (Label.h ∘ u) :=
    ⟨hx,Geo.masterL ..,fun k _=>tagL P T k,fun i k=>tagX V P T (u i) k,
      fun i=>lightL V P T hG (u i)⟩
  have D : Source (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) P x false
      (approach P M) (rowM P M ∘ u) (Label.h ∘ u) :=
    ⟨hx,Geo.masterD ..,fun k _=>tagD P M k,fun i k=>tagF P M (u i) k,
      fun i=>VeniceD P M (u i)⟩
  obtain ⟨⟨hD,_⟩,⟨hL,_⟩⟩ := WilsonPhysicalExteriorUVStory.installed M V T u hx
  obtain ⟨l₁,d₁,z₁⟩ := offers V M T u ht (gulfG (P:=P))
  obtain ⟨l₂,d₂,z₂⟩ := offers V M T u ht (westV (P:=P))
  have f:=closure L l₁ l₂ hL hs k
  have g:=closure D d₁ d₂ hD hs k
  have e:=trade L D l₁ d₁ l₂ d₂ z₁ z₂ hL hD hs k
  exact ⟨f,g,e,marketV f g e⟩
end

end YM.Integration.WilsonPhysicalExteriorResolved
