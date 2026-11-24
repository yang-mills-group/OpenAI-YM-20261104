import YM.FVA2.TreeT.Inlet
/-!
# Tree momentum Taylor tests on highest-rank sectors

`t_bud` calculus: e.g. `torched` for the MS mark archive in 4 dimensions
(uses ranks etc. stipulated, can apply even off momentum conservation on the
hypotheses there). This is not yet a Taylor cost estimate on every physical column.
Use with `TreeT.treeOK` towards the strict-rank conclusion.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.TreeT.Data
open Function Filter Set Finset MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Heat MS.Landau MS.Landau.Detect MS.Arts MS.Arc MS.Plane.Wire MS.Rock MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Alps MS.Garment MS.Color
open _root_.YM.MS.Shine MS.Hem MS.Hem.Mell MS.Train MS.Pearl MS.Motif MS.Heat.Signal MS.Book MS.Book.Convolve MS.Garment.Wave MS.Garment.Wick MS.Dock MS.Outlook MS.Emit
open MS.Wind MS.Wind.Leading MS.Land MS.Lifting MS.Mach MS.High
open Teller Capacity Graft Lambda
open scoped Topology ContDiff Interval Classical
variable {G:Gauge}{n m k d r:ℕ}{J:T ( Flats G )}{M:T (Coat G)}{s y:ℝ}
local notation "Q"=> col
-- induction criterion at rank given
section
variable (he:leader G J (gloss (pulseX G)) M)
include he
lemma forceL (n:ℕ): Ahead (n+2) (4+1) ( program G n J+ step0 G (J n)):= by
 induction n using Nat.strong_induction_on with
 | _ n ih=>
    obtain hD:= Canvas.limited he n; refine paysA ((mint _ _ ).plus ?_ ( via_c (n:=4) (r:=n+2) (a:=0) (b:=true) _ ?_ (gang (he n) |>.dost) ));
    swap; simpa using hD; -- NatInt norm
    intro i; change Cards (n+2) (4+1) ((2:ℂ)⁻¹ • (∑ k∈ shortB n,drive0 G (J k.1) (J k.2) ) i)
    apply scales; suffices H : SeedP ( Cards ( n+2 ) (4+1)) ( ∑ k∈ shortB n,drive0 G (J k.1) (J k.2) ) from H i
    have ht(i:ℕ) (H:i<n) : Ahead (i+2) 4 (J i):= answer ( hx:= RootF ( he i ) ) (hp:= ih _ H)
    have hK(i:ℕ) : ClockD true 0 (↑(i+2):ℤ) (J i):= by simpa using Canvas.limited he i
    refine (mint _ _).sum _ (fun k hk=>?_); obtain ⟨h,h₁,h₂⟩:= Finset.mem_filter.mp hk; obtain h' := mem_antidiagonal.mp h
    exact via_tree (( RootF ( he k.1 )).wet) (( RootF ( he k.2 )).wet) ( clockCap (hK k.1)) ( clockCap (hK k.2)) (by omega) (ht k.1 h₁) (ht k.2 h₂)
lemma here_L : ∀ j≤4, restrictT (n+2) j (hereZ 4 (J n) s y)= if j=4 then spot (↑(n+2)) (pulseX G n) else 0 := fun _ hj=> dim_jet (RootF ( he n )) (forceL he _) hj _ _
lemma latitude (n:ℕ)(s t:ℝ): Graft.Above false wfield 4 (n+2) (Archive 4 J n (s,t)):= by
    obtain he' := Lift.price (live0 (y:=s) (s:=t) ((gang ( he n )).dost)); refine (above_τ he').mp ?_ 0; intro i hi; rw [here_L he ( n:=n ) i hi.le,if_neg hi.ne]; -- insert params explicit?
end
section
variable (he:leader G J (gloss (pulseX G)) M)
variable {A:Law G}{U:T ( Flats G )}{X:T ( Coat G )}{x:Motif.Literal.Box (Mob G)}(H: Ele d r A x)(hm: comet d 0 J (gloss (Motif.Literal.linear (Mob G) x)) U X)
include he H hm
lemma forceM (n:ℕ) : Ahead (r+n) (d+1) (platform J n U +step0 G ( U n )):= by
    induction n using Nat.strong_induction_on with
    | _ n ih=>
       have hx(k:ℕ): ClockD false 0 (↑(r+k):ℤ) ( U k ) := by simpa using Capacity.limited he H hm k
       have hp(k:ℕ) : ClockD true 0 (↑(k+2):ℤ) ( J k ):= by simpa using Canvas.limited he k
       refine paysA ( (mint _ _).plus ?_ ( via_c _ ( hx n ) (( gang (hm n )).dost) ) ); refine (mint _ _).sum _ (fun i hi=>?_); obtain ⟨hK,h'⟩:= Finset.mem_filter.mp hi; obtain h:= mem_antidiagonal.mp hK; exact via_tree (( RootF ( he i.1 )).wet) (( RootF ( hm i.2 )).wet) ( clockCap (hp i.1)) ( clockCap ( hx i.2 )) (by omega) (answer (RootF (he i.1)) (forceL he _) ) (answer (RootF (hm i.2)) ( ih _ h' ))
lemma here_M (s y:ℝ) (n:ℕ): ∀ j≤d, restrictT (r+n) j (hereZ d (U n) s y)= if j=d then x n else 0 := by
    intro i hi; obtain h := dim_jet (s:=s) (y:=y) ( K:=x n ) (RootF (hm n)) (forceM he H hm n) hi; rwa [spotsP (show Goods (↑(r+n)) (x n) from ?_)] at h; intro m; push_cast; exact Hazel.bornTree r d x H.1
lemma PoleC (n:ℕ)(i:ℂ): spot (↑(r+n)) (X n i)=0:= congr_fun ( no_pole ( K:= x n ) ( RootF (hm n) ) ( forceM he H hm n )) i
-- in transfer convention of passive rays, ordered label list l incl noncons multipoint.Total torch
lemma torched (j n:ℕ) (l:List (Lane4 G))(t y:ℝ)(hx:l.length=r+n)(hv:fieldDim wfield l+j≤d): torch j (Archive d U n (t,y)) l= if fieldDim wfield l+j=d then x n 0 l else 0:= by
    let i:= fieldDim wfield l+j; have hi:0≤ i:= add_nonneg (Hem.dm (m:=0) (G:=G) l) (Int.natCast_nonneg j); obtain hg:= congr_fun ( congr_fun ( here_M he H hm y t n i.toNat (by unfold i; omega) ) 0 ) l; change spot _ _ 0 l=_ at hg; rw [spotted (by omega), t_bud _ (m:=0) (G:=G) (l:=l) (j:=j) (show fieldDim wfield l+j= (i.toNat:ℤ) from Int.toNat_of_nonneg hi |>.symm)] at hg; split_ifs with ht; · rw [if_pos (by unfold i; omega : i.toNat=d ) ] at hg; exact hg
    rw [if_neg (by unfold i; omega : ¬ i.toNat=d)] at hg; exact hg
end
end YM.FVA2.TreeT.Data
