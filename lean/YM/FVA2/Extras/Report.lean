import YM.FVA2.Extras.Origin
/-! # The `Says` convention for asserting such physical reductions

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
variable {I:Type}{G:Gauge}{b d:ℤ}{r k n:ℕ}{B:Deck G}{K:Booked B}{M:MS_Data G K}
variable {W:Type}[LinearOrder W]{a:ℝ}{x: Position W Unit}{X Y:T (localX G)}{Q:W→T (localX G)}{i j:W}{s:Finset W}{h:ℕ}{p:T (Package B h)}{v:List W}
-- All-order assertion for **every** such layout/test (impose the indicated field,
-- position and separation hypotheses).
abbrev Says (a:ℝ)(M:MS_Data G K)(p:T (Package B h)) (X:T (localX G)): Prop:=
   ∀ (W:Type)(_ : LinearOrder W)(x: Position W Unit)(Q:W→T (localX G))(i:W),
     Q i=X → Survey (Tide.frameF Unit a) M Q x → Mesh (Tide.frameF Unit a) x →
     ∀ s:Finset W, i∈s→ (∀ j∈s,Certified ( Q j ) M (logMass a) 0) →
       ∀ n, service a M Q x s n=
         ∑ k:Plaid B h, ∑ j∈Finset.range (n+1),
           (p j k:ℂ) * service a M (swapField a M i k Q) x s (n-j)
lemma speaks (he:X=many a M p+nav M (logMass a) Y)(hy:ghostly a M Y ((h:ℤ)-1)): Says a M p X:= by
    intro W _ x Q i hi hW hs s ht hS n; obtain he:= apply_one ( n:=n ) hW hs ( Finset.nodup_toList (s.erase i) ) ( by simp ) hi he hy (fun i hi=> ( hS i ( Finset.mem_of_mem_erase ( Finset.mem_toList.mp hi ) ) ).2 ); simpa only [ Finset.toList_toFinset,Finset.insert_erase ht ] using he
lemma frugal {E:Type}[AddCommGroup E] (U:T E) (i:ℕ): hold0 1 U (i+1)=U i:= by rw [ hx_holder (by omega),Nat.add_sub_cancel]
lemma headless (he:X 0=0)(hX:Forth a M X h): let U:=fun i=> X (i+1); Forth a M U h:= by
    intro U; have hx: hold0 1 U=X:= by funext i; cases i with| zero=> rw [low_hold (by omega),he]|succ n=> exact frugal U n
    let V:=helm M (logMass a); refine ⟨⟨ ⟨ fun i=> hX.1.1.life _,fun i=>?_⟩,?_⟩,fun i=> hX.2 _⟩; swap
    · let V:=nav M (logMass a);
      have ht: hold0 1 ( V U )=0:= by unfold V; rw [ ← shift_R,hx,hX.1.2 ]
      exact funext (fun i=> ( frugal ( V U ) i ).symm.trans ( congr_fun ht _ ))
    change Velocity ( X (i+1) ) ( V U i ); unfold V; rw [ ← frugal ( helm M (logMass a) U ) i,← shift_I,hx];
    exact hX.1.1.vital (i+1)
lemma speak_pos (he:X 0=0)(hX:Forth a M X h): ∃ ( p:T (Package B h) ), p 0=0∧ Says a M p X:= by
    obtain ⟨p,Y,hY,hE⟩:= cleanMultiple ( headless he hX ); let P:=hold0 1 p; have hy : X=many a M P+nav M (logMass a) ( hold0 1 Y ):= by
        let U:=fun i=>X (i+1); change U=many _ _ _+_ at hE
        rw [ show X=hold0 1 U from ?_,hE,shift_R,hold_add]; refine congr_arg (·+hold0 1 _) ?_; -- explicit many shift
        · funext i; cases i with
          | zero=> rw [ low_hold (by omega), batch (le_refl 0), Finset.sum_range_succ,Finset.sum_range_zero, zero_add, hold_1, show P 0=0 from low_hold (by omega),choice₀ ]; rfl
          | succ n=>
            rw [ frugal,batch (le_refl n), batch (le_refl (n+1)) ]; simp only [Finset.sum_apply]
            conv_rhs=> rw [Finset.sum_range_succ',show P 0=0 from low_hold (by omega), choice₀,holdZ ]
            simp_rw [show ∀ i,P (i+1)= p i from frugal p, step_s,Pi.zero_apply,add_zero]
        funext i; cases i with| zero=> rw [he,low_hold (by omega)] | succ i=> exact ( frugal U i ).symm
    exact ⟨ P,low_hold (by omega),speaks hy ⟨ shift_Response hY.1,hY.2.raise 1 ⟩⟩
end YM.FVA2.Extras
