import YM.FVA2.BudCap
import YM.FVA2.MixedTune
/-!
# Sharp resource use for adjusted source tadpoles, beyond Bounds. W.Poles
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Reed.Wax
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
open Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting Local.Physical
open Mach Train Pearl Emit Wind Wind.Leading Menus Program Knobs Native.Paint Native.Wilsonian Tone Momentum City
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{m n h d:ℕ}{p:Team}{B:Deck G} {i j:ℤ}(y:ℝ) {F H:Wind.Flow G}{P:Law G}
private lemma cure (r:ℤ)(he:TouchF F)(ht:∀ t,Limit ( H t ) r)(hL:∃ v,Rank F v)(hp: Sat P F H)(hV: Limit P r): Rank F r:= by
    obtain ⟨ v,hY⟩:=hL; suffices he : ∀ k:ℕ,∀ l:Legs (Lane4 G), (k:ℤ)+(l.length:ℤ)>v → (l.length:ℤ)>r→∀i,F i l=0 from fun t l hl=> he (v.toNat+1) l (by omega) hl t
    intro k; induction k with
    | zero=> intro l hl hv t; exact hY t l (by omega)
    | succ k ih=>
       intro l hl hv i; refine Eq.trans (constancy (f:=fun t=> F t l) ?_ i) ( hp.1.symm ▸ hV l hv );
       intro x; obtain hu:= hp.2 x l; convert hu using 1; symm; rw [ Pi.add_apply, ht x l hv,add_zero ]; change Heat.orbit _ _ (F x) l=0; rw [finite_cc μzone (period0 μzone cour0 (main_f _) he) ]; unfold Ccy; simp_rw [at_trc, show ∀ p t :Lane4 G,F x (p::t::l)=0 from fun p t=> ih _ (by simp; omega) (by simp; omega) x, mul_zero,Finset.sum_const_zero ]; simp
-- $ρκ$
lemma skyline_t (n:ℕ) (p:Team) : Rank ( skyline G p n y ) (n+2) := by
    induction n using Nat.strong_induction_on with| h n ih=>
       let U:= skyline G p; let L:= skyPC G p; obtain ht:= (L.owes n).stay y; by_cases H:n=0; · rw [H,L.free]; exact fun _ _ _=>rfl
       apply cure _ ht.joint _ _ (L.recu n (by omega) y) (oneRank (style_limit p y G n)); swap; · obtain ⟨v,hv⟩:=(L.owes n).pay; exact ⟨v,hv y⟩
       intro t; unfold Wind.path; simp_rw [Pi.smul_apply, Finset.sum_apply]; refine Limit.smul (↑(1/2:ℝ):ℂ) (Limit.sum _ (fun i hi=>Limit.up (Modeled.guard ( ih (n-i) ?_ t ) ( ih i ?_ t ) (Cpu G t)) ?_ )); all_goals obtain he:= path_in hi; omega -- fix Lean
variable (W:BookM B)(p:Team)(A:Acts B d)(t: Glyph B d)
def credit (n:ℕ)(x:Tact B d) : Prop:= (∀ i:Glyph B d,t.grade+n < i.grade→ x.register i=0) ∧ ∀ s:ℝ, Limit ( x.proof.input s ).val ((t.grade:ℤ)+n)
private lemma scores_b (he:∀ n,credit t n (A n)) : Limit (scoreM W p A y n).val (( t.grade:ℤ )+n):= by
   refine Limit.add ?_ ?_
   · show Limit (rentM W p A y n).val _; unfold rentM; simp_rw [Cylinder.sum_stack ]; refine Limit.sum _ fun i _=> Limit.sum (antidiagonal n) (fun j hj=>?_); obtain hx:= mem_antidiagonal.mp hj; by_cases hf:t.grade+j.1 < i.grade; · rw [oil,(he j.1).1 i hf, Polynomial.eval_zero,Complex.ofReal_zero,zero_smul ]; exact fun _ _=>rfl
     exact Limit.smul _ ( ( Glyph.pre_costM W p i y j.2 ).up (by omega) )
   show Limit (motto p A y n).val _; rw [Menus.sky ]; refine Limit.add ( ( lapLimit ((he n).2 y) ).up (by omega) ) ?_; rw [Cylinder.sum_stack ]; apply Limit.sum; intro i hi; apply ( rootLimit (style_limit p y G i.1) ((he i.2).2 y) ).up; obtain hu:= mem_antidiagonal.mp hi; omega
lemma horizon_t (he:∀ n,credit t n (A n))(n:ℕ) : Rank ( horizonM W p A n y ) ((t.grade:ℤ)+n):= by
    induction n using Nat.strong_induction_on with | h n ih=>
       obtain h := aquaM W p A; let V:=horizonM W p A; apply cure _ (((h.owes n).stay y).joint) _ _ (h.recu n y) ( oneRank ( scores_b y W p A t he ) ); swap; · obtain ⟨v,hv⟩:= ( h.owes n ).pay; exact ⟨v,hv y⟩
       intro s; unfold Wind.path; simp_rw [one_smul, Finset.sum_apply ]; apply Limit.sum; intro i hi; obtain hu:=path_in hi; change Limit (boulevard parity _ _ _) _; exact ( Modeled.guard ( skyline_t y ( n-i ) p s ) ( ih i hu.2 s ) _ ).up (by omega)
end YM.MS.Reed.Wax
