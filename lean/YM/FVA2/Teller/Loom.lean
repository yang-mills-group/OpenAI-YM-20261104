import YM.FVA2.Teller.Hazel
/-!
 # Rank-respecting implementation. Propagate rank bounds in n (g-order not
 hbar order), on the dimensional and lattice sides. Exact connection to loop order and adj admissibility later.
 Here supports RELAXED upper rank $r+n$ for candidate frames including at $n=0$ provisionally.
 Doesn't ensure $b<r+n$ on D-adjustments yet. Nor redoing analytic proof; just `High` costs.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Teller.Capacity
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Wind.Leading MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color
open MS.Book MS.Book.Convolve MS.Book.Program MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Local.Physical MS.Outlook MS.Halo MS.Alps MS.City MS.Mach
open _root_.YM.MS.Shine
open MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Wilsonian MS.Menus
open scoped Topology ContDiff BigOperators Classical
open Lambda
variable {G:Gauge}{n d k r:ℕ}
section D
variable {A:Law G}{q:T (Coat G)}{X U:T ( Flats G )}{P:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) P)
variable {x:Motif.Literal.Box ( Mob G )} (p:Ele d r A x)(he:comet d 0 X (gloss (Motif.Literal.linear (Mob G) x)) U q)
include hm he p
lemma limited (n:ℕ) : ClockD false 0 (r+(n:ℤ)) ( U n ):= by
  induction n using Nat.strong_induction_on with
  | _ n ih=>
     let φ:= Motif.Literal.linear ( Mob G ) x; let f:= Emit.gloss φ; let ψ:= platform X n U; let N:ℤ:=r+n
     have hc: Coal false d 0 N ψ:= by
        have hl(i:ℕ×ℕ)(hi:i∈shortM n): Coal false d 0 N (drive0 G (X i.1) (U i.2)):= by
          obtain ⟨hk,hv⟩:= Finset.mem_filter.mp hi; obtain hx:= mem_antidiagonal.mp hk; obtain hm1:= Canvas.limited hm i.1; obtain hm2:= ih _ hv
          obtain ⟨v,hr⟩:= feed ( gangLo (b:=false) (gang (hm i.1))) ( gang (he i.2)); refine ⟨fun j=>⟨ (hr.eye j).fine, ?_ ⟩, hr.real, hr.force ⟩; convert capA (clockCap hm1) (clockCap hm2) (reverse_a G 0) j using 1;
          rw [show ↑i.1+2+(↑r+↑i.2)-2=N from (by dsimp [N]; omega) ]
        suffices hu: ∀ k:Finset (ℕ×ℕ), k⊆shortM n→ Coal false d 0 N (∑ i∈k,drive0 G (X i.1) (U i.2)) from hu _ ( Finset.Subset.refl _ ); intro k; induction k using Finset.induction_on with
        | empty=> rw [sum_empty]; exact fun _=> coal_zero ..
        | insert i k hi ih=> rw [ sum_insert hi ]; intro H; exact glow (hl i (H (mem_insert_self ..))) (ih ( Finset.Subset.trans ( subset_insert i k ) H))
     have hx(n:ℕ):Cap0 false 0 (r+(n:ℤ)) ( f n ):= by
        obtain ⟨v,h⟩:= ( p.grows n ).stock; exact ⟨ h.fine, Eventually.of_forall fun i m l hl=> ( Hazel.bornTree r d x p.1 ( m:=m) ( n:=n ) l (by rw [mod_int]; omega) )⟩
     obtain ⟨y,o,hX,hP,_⟩:= factory hc (p.grows n).born (hx n); obtain ⟨v,hR,hT,H⟩:= (he n).1;
     exact clockWind hP ( ( super hX hR (fun i=>EventuallyEq.rfl) EventuallyEq.rfl hP hT ).1 )
lemma RootD (n:ℕ)(s t:ℝ) : Limit (( Archive d U n ) (s,t)) (r+(n:ℤ)) := by
  obtain ht:= Capacity.limited hm p he n; obtain hp:= (gang (he n)).dost; exact ( valueC hp ( Moony.toast ( clockMoon ht ) ) _ need_tail ( clockCap ht ) ) 0
end D
section L
variable {p:Team} {B:Deck G} (V:FullBook B) {j:Glyph B d}
-- `proof` also at rank, even when it won't enter final physical pole read. Compare.
structure Located (r:ℕ)(A:Tact B d)(u:ℤ) : Prop where
   holds (i:Glyph B d) : ((r:ℤ)+u)<(i.grade:ℤ) → A.register i=0
   moves (x:ℝ): Limit ( A.proof.input x ).val (r+(u:ℤ))

def Tag (r:ℕ)(A:Acts B d) : Prop:= ∀ n:ℕ, Located r (A n) n
variable {P: Acts B d}(H:Tag r P)
include H
lemma in_length (x:ℝ)(n:ℕ) : Limit (scoreF V p P x n).val (r+(n:ℤ)):= by
    obtain h:= H n; unfold scoreF; rw [Pi.add_apply, Submodule.coe_add]; refine Limit.add ?_ ?_
    · unfold rentF; simp_rw [sum_stack]; apply Limit.sum; intro i _; refine Limit.sum _ (fun y hy=>?_); by_cases ht: i.grade≤r+y.1
      · obtain h:= Finset.mem_antidiagonal.mp hy; exact Limit.up (( Glyph.pre_costF V p i x y.2 ).smul _) (by omega)
      rw [oil, (H y.1).holds i (by omega), Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]; exact fun _ _=>rfl
    rw [sky,Submodule.coe_add,sum_stack]; refine Limit.add (Limit.up (MS.Lifting.lapLimit (( H n ).moves _)) (by omega)) ( Limit.sum _ (fun i hi=> (MS.Lifting.rootLimit (style_limit p x G i.1) ((H i.2).moves _ )).up ?_ )); obtain hm:= Finset.mem_antidiagonal.mp hi; omega
lemma RootL (n:ℕ)(x:ℝ) : Rank ( horizonF V p P n x ) (r+(n:ℤ)):= by
    induction n using Nat.strong_induction_on with
    | _ n ih=>
       let A:=horizonF V p P; let U:= skyline G p; obtain ℓ:=aquaF V p P; obtain ⟨q,hq⟩:= ( ℓ.owes n ).pay; apply Lambda.Finite.fromSat ( Tone.oneRank ( in_length V H x n ( p:=p) ) ) _ ( ℓ.recu n x ) ((( ℓ.owes n ).stay x).joint) (hq x);
       unfold Wind.path; rw [Pi.smul_apply, Finset.sum_apply ]; refine Rank.smul (Rank.taps _ (fun i hi=>?_)) (1:ℂ); obtain hl:= path_in hi; exact ( busy_max _ (Lambda.Finite.ranked ( skyPC G p ) (n-i) x ) (ih _ hl.2) ).pay (by omega)
end L
end YM.FVA2.Teller.Capacity
