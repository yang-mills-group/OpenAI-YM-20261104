import YM.ForFlash.MS.Gulf
import YM.MS.Vane.Trigger
/-! Adapted from the YM modules indicated. Only lower gap hypothesis on the Mesh arguments,
see Phase for the change in the estimate itself. -/
set_option autoImplicit false
noncomputable section

/- Widening MS/Vane/North -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge} [LinearOrder W] {P: Geo I}{F H:Glade G I}{x: Position W I} {c:Bool}{m k n:ℕ} {K L: Planet G I}
    {X Y: Site G I}{A : W→ Site G I}{U:Dance G I W}{J : Finset W}{R: W→ℕ}{Y':I→QP}
local notation "Ϋ"=> West P
omit [LinearOrder W] in
lemma fossilForFlash (_h:CoverSepForFlash P Y'){u v w:Vista P→ℝ}(hk: Flow Ϋ K w)(hp: Here false true Ϋ F u)(hf: Here false true Ϋ H v)(hv:nn u)(hu:nn v)(hq:nn w): Here false false Ϋ (regionC (fun _=>planeF) Y' K F H ) ( w*(u*v) ):= by
    apply hobForFlash (P:=plug K) hk hp hf hq hv hu (beacon Ϋ) ( pea Ϋ ) (A:=fun i=>Y' i.1)
variable (h: TourForFlash K L P x c X A R)
variable (he:Arch ( Gulf P ) K L X A R)(hu:Arch (West P) K L X A R)(ht: Fields x (fun _=>planeF) K L X A U)
local notation "ι0"=> (fun (_:I)=>planeF)
include h hu
lemma berthForFlash (_hs:J.Nonempty)(n:ℕ)(hx:∀ v⊂ J,v.Nonempty→ ∀ i, mail P ( charge R v) 0 ( U v i ))(hp:∀ i<n,mail P ( charge R J) 0 ( U J i )): Fed P (charge R J) 0 (Src x ι0 K L X U J n ):= by
    refine Lease.plus ?l ?r
    · exact He_here (K:=West P) (Domain.paths n 0) (fun i hi=> shines Ϋ hu.main ( hu.states (n-i) ( by obtain hv:i<n:=( Finset.mem_Ico.mp hi).2; omega )) ( hp i ( Finset.mem_Ico.mp hi |>.2 )) ( FarBasis _ _ _ )) ( FarBasis _ _ _ )
    refine He_here (K:= West P ) _ (fun i hi=> He_here (K:=West P) _ (fun k hk=> ?_) ( FarBasis _ _ _ )) ( FarBasis _ _ _ ); obtain ⟨H,hV,hZ,hT⟩:= n_small hi; rw [ ← toll_charge R H.le ]; apply Lease.sticks ( fossilForFlash ( Rake.spaceForFlash h.plot hi ) hu.χ ( hx _ H hV _ ) ( hx _ hT hZ _ ) (FarBasis _ _ _) ( FarBasis _ _ _ ) (fun i=> zero_le_one) ); exact fun i=> by simp only [ Pi.mul_apply, Pi.one_apply,one_mul]; simpa using tax_far (x:=0) (y:=0) ( charge R _ ) ( charge R _ ) i
include ht he
lemma fartherForFlash (hs:J.Nonempty)(n:ℕ): mail P (charge R J) 0 ( U J n ):= by
    induction J using Finset.strongInductionOn generalizing n with| _ J ih=>
      induction n using Nat.strong_induction_on with| h n hz=>
        have hx:= berthForFlash h hu hs n ih hz; obtain hF:= motionForFlash h ht hs n; obtain hm:= moonForFlash h ht he hs n|>.1; rw [dotzero] at hm; refine marching ( εWest P ) (FarBasis _ _ _) hF.stroll ( Wharf hF ) (hop hm ) ( aboveC Ϋ false ( foundedForFlash h ht hs n |>.1 )) ?_
        intro r hv hp E _ _ _ w hw hk; have hs:= LensC hu.χ hp ( FarBasis _ _ _ ); obtain ⟨ α,hα,hJ⟩:= broken ( P:=P ) (h:=charge R J) (x:=0) E w hk (hw ▸ hv); exact ⟨ _,α,hα, Lens.plus hs ( pinch hx (fun x=>Bool.noConfusion x)) E w hw hk, hJ ⟩
lemma recallForFlash (hs:J.Nonempty)(n:ℕ): Fed P (charge R J) 0 ( rhs x ι0 K L X U J n ):= by refine Lease.plus ?cycle ( berthForFlash h hu hs n (fun i hi hs n=> fartherForFlash h he hu ht hs n) (fun _ _=>fartherForFlash h he hu ht hs _) ); exact poses (fun i _=> LensC hu.χ ( pinch (fartherForFlash h he hu ht hs n) (fun _=> by omega) ) ( FarBasis _ _ _ ))
end YM.MS.Vane

/- Widening MS/Vane/Zever -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}[LinearOrder W]{P:Geo I}{x:Position W I}{R:W→ℕ}{K L K' L':Planet G I}{F H D N:Glade G I}
  {ξ:I→QP}{c b:Bool}{X Y:Site G I}{A B: W→ Site G I}{U V:Dance G I W}{n h k:ℕ}
local notation "Ϋ"=> West P
local notation "Θ"=> coinZ P
variable (T: ChaseForFlash P x (fun _=>planeF) R b K L X A U)(T':ChaseForFlash P x (fun _=>planeF) R c K' L' Y B V)
  (Z: ArcS (Gulf P) K L K' L' X Y A B R)(M:Arch ( Gulf P) K L X A R)(M': Arch ( Gulf P ) K' L' Y B R)
  (W0: Arch ( West P ) K L X A R)(W1: Arch ( West P ) K' L' Y B R)(Z0: ArcS ( West P ) K L K' L' X Y A B R)
include Z0
include W0
omit [LinearOrder W] in
lemma blastForFlash (hf:CoverSepForFlash P ξ)(hv:mail P h 0 F)(hv':mail P h 0 H)(hD:mail P h eps_gain ( F-H ))(ht:mail P k 0 N)( ht':mail P k eps_gain ( D-N )) (hw:Warm H false)(hF:Warm F false)(hN:Warm N false)(ha:Warm D false): BackF L→BackF L'→ Fed P (h+k) eps_gain (regionC (fun _=>planeF) ξ L F D - regionC (fun _=>planeF) ξ L' H N):= by
   intro hL hM; unfold mail at hD ht'; rw [zeta] at hD ht'; refine parkD hv hv' hD ht ht' hw hF ha hN hL hM (fun _=>Coherent) ?_ ?_ ?_; all_goals intro x y h1 h2
   · rw [← zeta] at h2; apply Lease.sticks ( fossilForFlash hf W0.χ h1 h2 (FarBasis _ _ _) ( FarBasis _ _ _ ) (fun i=>zero_le_one) ); exact fun i=>( by simpa using tax_far (x:=0) (y:=eps_gain) h k i )
   · rw [← zeta] at h1; apply Lease.sticks ( fossilForFlash hf W0.χ h1 h2 (FarBasis _ _ _) ( FarBasis _ _ _ ) (fun i=>zero_le_one) ); exact fun i=> ( by simpa using tax_far (x:=eps_gain) (y:=0) h k i )
   apply Lease.sticks ( fossilForFlash hf ( globX Z0 ) h1 h2 ( FarBasis _ _ _ ) ( FarBasis _ _ _ ) γ_non ); rw [zeta]; exact fun i=> mul_le_mul_of_nonneg_left (by simpa using tax_far (x:=0) ( y:=0 ) h k i ) ( γ_non i )
include M M' W1 T T'
local notation "m0"=> (fun (_:I)=>planeF)
lemma beamForFlash (S:Finset W)(hs:S.Nonempty)(hv:∀ t⊂ S,t.Nonempty→∀ i, mail P (charge R t) eps_gain ( U t i-V t i ))(hN:∀ i<n,mail P (charge R S) eps_gain ( U S i-V S i )): Fed P (charge R S) eps_gain ( Src x m0 K L X U S n-Src x m0 K' L' Y V S n ):= by
   unfold Src multi lonely; rw [ add_sub_add_comm,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]; refine Lease.plus ?l ?r
   · refine He_here (K:=West P) _ (fun i hi=>?_) ( FarBasis _ _ _ ); obtain hK:i<n:= Finset.mem_Ico.mp hi|>.2; obtain hu:n-i>0:=(by omega); have hV:= hN i hK; unfold mail at hV; rw [ zeta ] at hV ⊢; exact Trees W0.main ( γK Z0 ) ( W1.states _ hu ) ( W0.states _ hu ) ( Vψ Z0 _ hu ) ( fartherForFlash T'.tour M' W1 T'.fields hs i ) hV ( FarBasis P _ _ ) γ_non
   refine He_here (K:=West P) _ (fun i hi=> ?_ ) ( FarBasis _ _ _ ); obtain ⟨Q,hP,hU,hM⟩:= n_small hi; rw [← Finset.sum_sub_distrib, ← toll_charge R Q.le]; refine He_here (K:=West P ) _ (fun k hk=> blastForFlash W0 Z0 ( Rake.spaceForFlash T.tour.plot hi ) ( fartherForFlash T.tour M W0 T.fields hP k.1 ) (fartherForFlash T'.tour M' W1 T'.fields hP k.1) (hv i Q hP k.1 ) (fartherForFlash T'.tour M' W1 T'.fields hU k.2) (hv _ hM hU k.2) ( foundedForFlash T'.tour T'.fields hP k.1 |>.2 ) ( foundedForFlash T.tour T.fields hP k.1 |>.2 ) ( foundedForFlash T'.tour T'.fields hU k.2 |>.2 ) ( foundedForFlash T.tour T.fields hU k.2|>.2 ) T.tour.ground.pool T'.tour.ground.pool ) ( FarBasis _ _ _ )
include Z
lemma heightsForFlash (S:Finset W)(n:ℕ)(he:S.Nonempty): mail P ( charge R S) eps_gain ( U S n-V S n ):= by
   induction S using Finset.strongInductionOn generalizing n with | _ S hi=>
      induction n using Nat.strong_induction_on with | h n hv=>
        have hp:= beamForFlash T T' M M' W0 W1 Z0 S he (fun i h hP k=>hi i h k hP) hv; let D:= rhs x m0 K L X U S n-rhs x m0 K' L' Y V S n
        have hm: Fits false ( U S n-V S n ) D:= ( motionForFlash T.tour T.fields he n ).subFit (motionForFlash T'.tour T'.fields he n ); have hh := tokensForFlash T T' M M' Z S n he|>.1; rw [ dotzero, ← alter ] at hh; obtain ⟨hA,hP⟩:= foundedForFlash T.tour T.fields he n; obtain ⟨hY,hM⟩:= foundedForFlash T'.tour T'.fields he n
        refine marching (εWest _) ( FarBasis _ _ _ ) hm.stroll (Wharf hm) (hop hh) ( aboveC Ϋ false ( combine hA hY ) ) ?_; intro r hr h E _ _ _ w hw ht; obtain ⟨α,hα,hL⟩:= broken (P:=P) (h:=charge R S) (x:=eps_gain) E w ht (hw ▸ hr); refine ⟨ _,_,hα,?_,hL⟩;
        unfold D rhs; rw [ add_sub_add_comm ]; have hx := pinch hp ( r:=r ) (fun h=>Bool.noConfusion h); apply Lens.plus _ hx E w hw ht; rw [zeta] at *; exact LensD W0.χ (globX Z0) h ( pinch (fartherForFlash T'.tour M' W1 T'.fields he n) (fun _=> by omega) ) hP hM T.tour.ground.pool T'.tour.ground.pool γ_non (FarBasis _ _ _ )
lemma economicsForFlash (S:Finset W)(hp:S.Nonempty)(n:ℕ): Fed P ( charge R S ) eps_gain ( rhs x m0 K L X U S n-rhs x m0 K' L' Y V S n ):= by
    unfold rhs; rw [add_sub_add_comm]; obtain hv:= heightsForFlash T T' Z M M' W0 W1 Z0; refine Lease.plus ?p ( beamForFlash T T' M M' W0 W1 Z0 S hp (fun i hi he k=> hv i k he) (fun i j=>hv _ i hp) ); apply poses; intro r he; obtain hx:= hv S n hp; unfold mail at hx; rw [zeta] at hx ⊢; exact LensD W0.χ (globX Z0) ( pinch hx (fun _=>by omega) ) (pinch ( fartherForFlash T'.tour M' W1 T'.fields hp n ) (fun _=>by omega) ) ( foundedForFlash T.tour T.fields hp n|>.2 ) ( foundedForFlash T'.tour T'.fields hp n|>.2 ) T.tour.ground.pool T'.tour.ground.pool γ_non (FarBasis _ _ _ )
end YM.MS.Vane

/- Widening MS/Vane/Trigger -/
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}{F H D: Glade G I}{X:I→ℂ}{d h:ℕ}{ζ:ℝ}
variable { J:Type}[LinearOrder W]{x:Position W I}{c b:Bool}{K L K' L':Planet G I}{B B': Site G I}{A A':W→Site G I}{R:W→ℕ}{p:ℝ}{U V:Dance G I W}{S:Finset W}{v:I→ℝ}
local notation "m0"=> (fun (_:I)=>planeF)
variable (h₂:TourForFlash K L P x b B A R)(hx:TourForFlash K' L' P x c B' A' R)
    (M: Arch ( Gulf P ) K L B A R) (M':Arch ( Gulf P ) K' L' B' A' R)(N:Arch (West P) K L B A R)(N': Arch ( West P ) K' L' B' A' R)(Z:ArcS ( Gulf P ) K L K' L' B B' A A' R)(Z':ArcS ( West P ) K L K' L' B B' A A' R)
include h₂ M N
lemma closureForFlash (H:Fields x m0 K L B A U)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) 0 ( U S n ):= by
    obtain he:= motionForFlash h₂ H hp n; obtain hu:= recallForFlash h₂ M N H hp n; obtain ⟨hv,hz⟩:= saleable he hu; have H':= moonForFlash h₂ H M hp n|>.1; rw [dotzero] at H'; exact ⟨ hv,hz,titel H' hu he ⟩
include hx M' N' Z Z'
lemma tradeForFlash (H:Fields x m0 K L B A U) (H': Fields x m0 K' L' B' A' V)(hp:S.Nonempty)(n:ℕ): Verdict P ( charge R S ) eps_gain ( U S n-V S n ):= by
   let T:ChaseForFlash P x m0 R b K L B A U:= ⟨ h₂,H ⟩; let T':ChaseForFlash P x m0 R c K' L' B' A' V:= ⟨ hx,H' ⟩; obtain hm:= economicsForFlash T T' Z M M' N N' Z' S hp n; obtain ht:= tokensForFlash T T' M M' Z S n hp|>.1; rw [dotzero, ← alter] at ht; have hv:= Fits.subFit ( motionForFlash h₂ H hp n ) ( motionForFlash hx H' hp n ); obtain ⟨ hU,hW⟩:= saleable hv hm; exact ⟨ hU,hW,titel ht hm hv ⟩
end YM.MS.Vane
