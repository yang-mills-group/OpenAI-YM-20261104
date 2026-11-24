import YM.MS.Vane.North
import YM.WiderProfiles.Vane.Peel
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Vane/North.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge} [LinearOrder W] {P: Geo I}{F H:Glade G I}{x: Position W I} {c:Bool}{m k n:ℕ} {K L: Planet G I}
    {X Y: Site G I}{A : W→ Site G I}{U:Dance G I W}{J : Finset W}{R: W→ℕ}{Y':I→QP}
local notation "Ϋ"=> West P
omit [LinearOrder W] in
lemma placeW_wide (h:WCoverSep P Y') : paid (West P).price (fun p=> ‖Y' p.1‖) ( West P ).price.length:= h.pay (West P) (fun _ => rfl) aboveV
omit [LinearOrder W] in
lemma fossil_wide (h:WCoverSep P Y'){u v w:Vista P→ℝ}(hk: Flow Ϋ K w)(hp: Here false true Ϋ F u)(hf: Here false true Ϋ H v)(hv:nn u)(hu:nn v)(hq:nn w): Here false false Ϋ (regionC (fun _=>planeF) Y' K F H ) ( w*(u*v) ):= by
    apply hob (K:=plug K) (μ:=fun _=> planeF) hk hp hf hq hv hu (beacon Ϋ) ( pea Ϋ ) (A:=fun i=>Y' i.1); intro E _ _; exact paid_at (placeW_wide h ) (fun i=> ( ( West P ).price.pos i ).le)
variable (h: WTour K L P x c X A R)
variable (he:Arch ( Gulf P ) K L X A R)(hu:Arch (West P) K L X A R)(ht: Fields x (fun _=>planeF) K L X A U)
local notation "ι0"=> (fun (_:I)=>planeF)
include h hu
lemma berth_wide (_hs:J.Nonempty)(n:ℕ)(hx:∀ v⊂ J,v.Nonempty→ ∀ i, mail P ( charge R v) 0 ( U v i ))(hp:∀ i<n,mail P ( charge R J) 0 ( U J i )): Fed P (charge R J) 0 (Src x ι0 K L X U J n ):= by
    refine Lease.plus ?l ?r
    · exact He_here (K:=West P) (Domain.paths n 0) (fun i hi=> shines Ϋ hu.main ( hu.states (n-i) ( by obtain hv:i<n:=( Finset.mem_Ico.mp hi).2; omega )) ( hp i ( Finset.mem_Ico.mp hi |>.2 )) ( FarBasis _ _ _ )) ( FarBasis _ _ _ )
    refine He_here (K:= West P ) _ (fun i hi=> He_here (K:=West P) _ (fun k hk=> ?_) ( FarBasis _ _ _ )) ( FarBasis _ _ _ ); obtain ⟨H,hV,hZ,hT⟩:= n_small hi; rw [ ← toll_charge R H.le ]; apply Lease.sticks ( fossil_wide ( Rake.space_wide h.plot hi ) hu.χ ( hx _ H hV _ ) ( hx _ hT hZ _ ) (FarBasis _ _ _) ( FarBasis _ _ _ ) (fun i=> zero_le_one) ); exact fun i=> by simp only [ Pi.mul_apply, Pi.one_apply,one_mul]; simpa using tax_far (x:=0) (y:=0) ( charge R _ ) ( charge R _ ) i
include ht he
lemma farther_wide (hs:J.Nonempty)(n:ℕ): mail P (charge R J) 0 ( U J n ):= by
    induction J using Finset.strongInductionOn generalizing n with| _ J ih=>
      induction n using Nat.strong_induction_on with| h n hz=>
        have hx:= berth_wide h hu hs n ih hz; obtain hF:= motion_wide h ht hs n; obtain hm:= moon_wide h ht he hs n|>.1; rw [dotzero] at hm; refine marching ( εWest P ) (FarBasis _ _ _) hF.stroll ( Wharf hF ) (hop hm ) ( aboveC Ϋ false ( founded_wide h ht hs n |>.1 )) ?_
        intro r hv hp E _ _ _ w hw hk; have hs:= LensC hu.χ hp ( FarBasis _ _ _ ); obtain ⟨ α,hα,hJ⟩:= broken ( P:=P ) (h:=charge R J) (x:=0) E w hk (hw ▸ hv); exact ⟨ _,α,hα, Lens.plus hs ( pinch hx (fun x=>Bool.noConfusion x)) E w hw hk, hJ ⟩
lemma recall_wide (hs:J.Nonempty)(n:ℕ): Fed P (charge R J) 0 ( rhs x ι0 K L X U J n ):= by refine Lease.plus ?cycle ( berth_wide h hu hs n (fun i hi hs n=> farther_wide h he hu ht hs n) (fun _ _=>farther_wide h he hu ht hs _) ); exact poses (fun i _=> LensC hu.χ ( pinch (farther_wide h he hu ht hs n) (fun _=> by omega) ) ( FarBasis _ _ _ )) -- order
end YM.MS.Vane
