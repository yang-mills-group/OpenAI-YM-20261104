import YM.FVA2.Lambda.X
/-!
# Rank upper bound, focusing on top-rank terms for slope comparison

 No loop cutoff hypothesis. Applies to the specified continuation in unrestricted dimension
 (germ, with all k-costs); and to native heat in lattice Cover, NOT claiming decay by rank
 when clearing estimates. Not using actual functions or hypotheses on beta itself.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Local.Physical MS.Outlook MS.Halo MS.Alps MS.City
open _root_.YM.MS.Shine
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{k m i a:ℕ}
namespace Finite
variable {p:MS.Book.Program.Team}{X:Dec G} (h:PC G p X)
lemma fromSat {n:ℤ}{T:Wind.Flow G}{Q:Law G}{W:Wind.Flow G}{u:ℤ}(hA:Limit Q n)(hW:Rank W n)(hT: Sat Q T W)(hP:TouchF T)(ht:Rank T u): Rank T n:= by
 intro t; let m:=u.toNat+1; suffices h : ∀ k≤ m, ∀ w, n<w.length → w.length≥k→ T t w=0 from fun w hw=> h 0 (Nat.zero_le _) w hw (Nat.zero_le _)
 intro k hM; induction hM using Nat.decreasingInduction generalizing t with
 | self=> exact fun _ _ hv=> ht t _ (by unfold m at hv; omega)
 | of_succ j hj ih=>
     intro w hw h'; have he:= hA w hw; rw [ ← hT.1 ] at he; refine Eq.trans ?_ he; apply Wind.constancy (f:=fun t:ℝ=> T t w); intro x
     convert! hT.2 x w using 1; rw [Pi.add_apply, hW x w hw, add_zero]; change 0= Heat.orbit ( Cpu G x ) μzone (T x) w; rw [finite_cc μzone (period0 μzone cour0 ( main_f _ ) hP ) ]; unfold Ccy; have hu(y:QP): Flux.trc (Cpu G x) y (T x) w=0:= by
         rw [ Flux.at_trc ]; refine Finset.sum_eq_zero (fun i _=> Finset.sum_eq_zero (fun z _=>?_)); rw [ih x _ (by simp; omega) (by simp; omega),mul_zero]
     simp_rw [hu]; simp
include h
open MS.Native MS.Native.Wilsonian MS.Book.Program MS.City
lemma ranked (n:ℕ)(x:ℝ): Rank ( X n x ) (n+2):= by
 induction n using Nat.strong_induction_on with
 | _ n ih=>
    by_cases h0:n=0; · subst n; rw [ h.free ]; exact Rank.zero G _
    obtain ⟨q,hq⟩:= (h.owes n).pay; apply fromSat (Tone.oneRank ( style_limit p x G n )) _ ( h.recu n (Nat.pos_of_ne_zero h0) x ) ( ( h.owes n ).stay x|>.joint ) (hq x)
    have he (i:ℕ)(hi : i∈ Domain.paths n 1): Rank ( treeP G ( X (n-i) x ) ( X i x ) ) (n+2):= by
       obtain hx:= path_in hi; exact ( busy_max _ ( ih _ (by omega : n-i<n)) ( ih _ hx.2 ) ).pay (by omega)
    unfold Wind.path; rw [Pi.smul_apply, Finset.sum_apply]; exact Rank.smul ( Rank.taps _ he ) (↑(1/2:ℝ):ℂ) -- real
end Finite
namespace Canvas
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y)
-- upper MS before four specializing; applies for all orders
lemma plan (n:ℕ) : Cap0 true 0 ( ( n:ℤ )+2 ) (gloss ( pulseX G ) n):= by
 have hP (i:ℕ):Halo.Pace ( pulseX G n i ) 4 0 ((n:ℤ)+2):= by
     rcases n with _| n; rw [Up0]; exact Pace.zero; by_cases h:n=0; · subst n; exact fund_one ..
     exact ( funded .. ).taller (by omega) -- hk? implicits
 obtain ⟨u,h⟩:= ( invest G n ).stock; exact ⟨ h.fine, Eventually.of_forall fun i=> (show Issue ((n:ℤ)+2) ( pulseX G n ) from fun i=> ( hP i ).up) ⟩
include hm
lemma limited (n:ℕ): ClockD true 0 ((n:ℤ)+2) ( X n ):= by
  induction n using Nat.strong_induction_on with
  | _ n ih=>
     let ψ:= program G n X; let N:ℤ:=n+2
     have he: Coal true 4 0 N ψ:= by
        have hl(i:ℕ×ℕ)(hi:i∈shortB n) : Coal true 4 0 N (drive0 G (X i.1) (X i.2)):= by
          obtain ⟨hk,hv,hr⟩:= Finset.mem_filter.mp hi; obtain hx:= mem_antidiagonal.mp hk; obtain hm1:= ih _ hv; obtain hm2:= ih _ hr
          obtain ⟨r,hr⟩:= feed (gang (hm i.1)) (gang (hm i.2)); refine ⟨fun j=>⟨ (hr.eye j).fine, ?_ ⟩, hr.real, hr.force ⟩; convert capA (clockCap hm1) (clockCap hm2) (reverse_a G 0) j using 1; 
          rw [show ↑i.1+2+(↑i.2+2)-2=N from (by dsimp [N]; omega) ]
        apply glazer _ _ (by simp)
        suffices hu: ∀ k:Finset (ℕ×ℕ), k⊆shortB n→ Coal true 4 0 N (∑ i∈k,drive0 G (X i.1) (X i.2)) from hu _ ( Finset.Subset.refl _ ); intro k; induction k using Finset.induction_on with
        | empty=> rw [sum_empty]; exact fun _=> coal_zero ..
        | insert i k hi ih=> rw [ sum_insert hi ]; intro H; exact glow (hl i (H (mem_insert_self ..))) (ih ( Finset.Subset.trans ( subset_insert i k ) H))
     obtain ⟨x,p,hX,hP,_⟩:= factory he (invest G n).born (plan n); obtain ⟨r,hR,hT,H⟩:= (hm n).1;
     exact clockWind hP ( ( super hX hR (fun i=>EventuallyEq.rfl) EventuallyEq.rfl hP hT ).1 )
lemma fromD (n:ℕ)(s t:ℝ): Limit ((Archive 4 X n) (s,t)) ( n+2 ):= by
  obtain ht:= limited hm n; obtain hp:= (gang (hm n)).dost; exact ( valueC hp ( Moony.toast ( clockMoon ht ) ) _ need_tail ( clockCap ht ) ) 0 -- offshell
lemma opens (s:ℝ×ℝ): ∀ w:List (Lane4 G), 1<w.length→(Archive 4 X) 1 s w= pulseX G 1 0 w:= by intro w h; exact sub_eq_zero.mp (HB (y:=s.1) (s:=s.2) hm (invest G 1) (fun i=> (fund_one G i).up) 0 w (by omega))
end Canvas
end YM.FVA2.Lambda
