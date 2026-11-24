import YM.FVA2.MSBud
/-!
# Slot-count vs mark prices: sharp upper capacity in g (= shifts from ħ)

No self diagonal comparison: applies in all ranks on the arc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Reed
open Filter Topology Set Function MeasureTheory Finset
open Plane Lifting Landau Landau.Detect Koszul Book Book.Convolve Book.Program Dock
open Pearl Train Outlook Mach Arts Arts.Spin Halo Arc Garment Hem Rock Rock.Path Alps Rock.Oceans
open Plane.Wire Arts.Pilot Color Flux Shine Hem.Mell Garment.Wick Motif Motif.Literal
open scoped Topology Classical ContDiff
variable {G:Gauge}{n d m h:ℕ}{z:ℂ}
variable {F H: Flats G} {p:Mob G} {g:Coat G} {B: Prop}{b:Bool}{i j k:ℤ} (K:Box (Mob G))
private lemma footage (he:sings b i d (fun _:ℂ=>p) B F H g)(ht:Badge b (fun _=>p) d i)(h: Coal b d i j F)(hp:Issue j p): ClockD b i j H:= by
   obtain ⟨X,p,hT,hQ⟩:= factory h ht.born (bias hp (give ht).2.2); obtain ⟨k,hs,hV,hP⟩:=he.1; exact clockWind hQ.1 ( (super hT hs (fun _=>EventuallyEq.rfl) EventuallyEq.rfl hQ.1 hV ).1 )
private lemma lit (ht:Gang b h k F) (hp:Gang b 4 0 H)(hF:ClockD b k i F)(hH: ClockD b 0 j H): Coal b h k (j+i-2) (drive0 G H F):= by
    obtain ⟨ _,t⟩:= feed hp ht; have he : Coal b h k _ (drive0 G H F):= zero_add k ▸ t; exact ⟨ fun v=> ⟨(he.eye v).fine, capA (clockCap hH) (clockCap hF) (reverse_a G 0) v⟩, he.real, he.force ⟩
private lemma total {A:Type}{F:A→ Flats G}(s:Finset A)(he:∀ i∈s,Coal b d j k (F i)): Coal b d j k (∑ i∈s,F i):= by
    induction s using Finset.induction_on with| empty=>rw [sum_empty]; exact coal_zero ..| insert i t hi hT=> rw [Finset.sum_insert hi]; exact Dock.glow ( he i (by simp) ) ( hT ( fun v hv=> he v ( mem_insert_of_mem hv )) )
variable {B:Local.Physical.Deck G}{P:Land.Booked B}(M:Land.MS_Data G P) (t:Land.Plaid B d)(x:ℝ×ℝ)
private lemma qBurn (n:ℕ): Issue ((n:ℤ)+2) ( pulseX G n ):= by
    intro m l hl; rcases n with _|(_|n); rw [Up0 ]; rfl; exact fund_one G m |>.up _ hl; apply (funded _ G m).up; omega
lemma horizonL (n:ℕ): ClockD true 0 ( ( n:ℤ ) + 2) (M.bulk n):= by
    induction n using Nat.strong_induction_on with| h n ih=>
       refine footage (M.bulkOK n) ( invest G n ) ?_ ( qBurn _ ); unfold program; apply glazer _ _ (by simp); apply total; intro i hi; obtain ⟨hQ,h1,h2⟩:= Finset.mem_filter.mp hi; obtain ht:= lit (gang ( M.bulkOK i.2 )) (gang ( M.bulkOK i.1 )) (ih i.2 h2) (ih i.1 h1); apply ht.wax; obtain he:= mem_antidiagonal.mp hQ; omega
lemma trophy (n:ℕ): ClockD false 0 (( (Land.read t).grade:ℤ )+( n:ℤ )) ( M.marks d t n ):= by
    induction n using Nat.strong_induction_on with| h n ih=>
       refine footage ( M.markOK d t n ) ( Ele.grows ( P.law d t ) n ) ?_ ( BudW _ ( P.law d t ) ); unfold platform; apply total; intro i hi; obtain ⟨hQ,h1⟩:= Finset.mem_filter.mp hi; obtain hu:= horizonL M i.1; obtain ht:= lit (gang ( M.markOK d t i.2 )) (gangLo ( b:=false ) (gang ( M.bulkOK i.1 ))) (ih i.2 h1) (fun z=>⟨ ( hu z ).fine.tire,(hu z).cap⟩); apply ht.wax; obtain he:= mem_antidiagonal.mp hQ; omega
lemma ranked {s y:ℝ}(he:ClockD b i j F)(ht:Stay d F): Issue j ( hereZ d F s y ):= valueC ht (Moony.toast ( clockMoon he )) _ need_tail (clockCap he) -- same
lemma heightℓ (n:ℕ): Limit ( Archive 4 M.bulk n x ) ( (n:ℤ)+2 ):= ranked (horizonL M n) ( gang ( M.bulkOK n )|>.dost ) 0
lemma heightMark (n:ℕ): Limit ( Archive d ( M.marks d t ) n x ) (( (Land.read t).grade:ℤ )+( n:ℤ )):= ranked ( trophy M t n ) (gang ( M.markOK d t n ) |>.dost ) 0
end YM.MS.Reed
