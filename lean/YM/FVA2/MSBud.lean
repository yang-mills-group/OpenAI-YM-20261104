import YM.FVA2.AntiBoot
/-!
# Slot-count vs mark prices: sharp upper capacity in g (= shifts from ħ)

No self diagonal comparison: applies in all ranks on the arc.Q.
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
local notation "ζ"=> J ( Shore G n ) ℂ
-- ρ sign without repeating marker fool.
variable (p:ℂ)
def lift_r (A:Type*) : Op A ℂ where
   toFun F l:= p^l.length*F l
   map_add' F V:= funext fun l=> mul_add (p^l.length) (F l) (V l)
   map_smul' c F:= funext fun l=> mul_left_comm _ c (F l)
local notation "Ψ"=> lift_r p
private lemma lift_prod {A:Type*}(F G:Koszul.Raw A ℂ) (X:Sector A) : Ψ A (product X F G)=product X (Ψ A F) ( Ψ A G ):= by ext L; change p^ L.length*_= _; simp_rw [scattered, collectL ]; refine scatter_congr _ _ _ _ fun i j hij=>?_ ; change p^ _*(F i*G j)=( p^_* F i )*( p^_*G j ); rw [← split_length hij,pow_add ]; ring
private lemma lift_leaf {C:Type*}{F:Raw C ℂ}(he:Book.rank 1 F): Ψ _ F= p • F := by ext l; by_cases hx:l.length=1; change p^ _*_= p*_; simp only [hx,pow_one ]; rw [Pi.smul_apply, he l (by rw [mod_int]; omega), smul_zero]; change p^l.length * F l=0; rw [he l (by rw [mod_int]; omega), mul_zero ]
private lemma lift_ψ (F H:Mield G n)(j:G.ColorIndex) : Ψ _ ( jaw G n F H j )= jaw G n ((Ψ _) ∘ F) (( Ψ _ )∘ H ) j:= by simp only [ chew,map_sum,map_smul,lift_prod ]; rfl
private lemma lift_l (i:Arts.L n) (j:G.ColorIndex): Ψ _ (A n G i j)= p • A n G i j := lift_leaf p (mon_leaf _)
private lemma ΩF (i j:Arts.L n)(c:G.ColorIndex): Ψ _ ( F₀ i j c )= p • F₀ i j c := lift_leaf p ( rank_α i j c )
private lemma Pole_point (a b:Axis)(l:List Axis)(i:G.ColorIndex): Ψ _ (Pole G n a b z l i)= p • Pole G n a b (p*z) l i:= by
   induction l generalizing i with
   | nil=>
      have he (a b:Arts.L n)(i:G.ColorIndex): Ψ _ (jaw G n (A n G a) (A n G b) i)= p • p • jaw G n ( A n G a ) ( A n G b ) i:= by rw [lift_ψ, show ((Ψ _) ∘ A n G a)= p • A n G a from funext ( lift_l p a ), show ((Ψ _) ∘ A n G b)=p • A n G b from funext ( lift_l p b ), map_smul,map_smul,LinearMap.smul_apply ]; rfl
      simp only [ Pole, cur, Pi.smul_apply,Pi.add_apply,map_smul,map_add, smul_add,ΩF, he,smul_smul ]; ring_nf -- simp multiplication
   | cons q l ih=>
      let v:= Pole G n a b; let q':=chair n q; have hQ : ((Ψ _) ∘ v z l)=p • v (p*z) l:= funext ih;
      have hu (F:Rack G n) : Ψ _ (rowP q' F)=rowP q' (Ψ _ F):= funext fun i=> mul_left_comm (p^i.length) _ ( F i );
      unfold v at hQ; unfold Pole convoke; simp only [ Pi.add_apply,LinearMap.add_apply, LinearMap.smul_apply,Pi.smul_apply,map_add,map_smul ]; rw [ lift_ψ,hQ,show ((Ψ _ ) ∘ A n G (chair n q))=p • A n G (chair n q) from funext ( lift_l p q' ), map_smul,map_smul,LinearMap.smul_apply, axisP,lock,hu,ih ]; simp only [Pi.smul_apply,lock,map_smul,smul_add,smul_smul ]; unfold q'; ring_nf -- NF *.CLI
-- using to valued extractor
variable (G) in
def tally_p : Mob G→ₗ[ℂ] Mob G where
   toFun F n:= Ψ _ (F n)
   map_add' F H:= funext fun i=>map_add (Ψ _) (F i) (H i)
   map_smul' c F:= funext fun i=>map_smul (Ψ _) c (F i)
local notation "ρ"=> tally_p G p
lemma liftMark (F:ℂ→Mob G)(he:F∈ Gallery G m d): ρ (F z)= p^m • F (p*z):= by
    have ht(m:ℕ)(T:Fin m→Plaq)(σ:Lifting.Grid G m) : ρ ( Pole.wing m T σ z )= p^m • Pole.wing m T σ (p*z) := by
        funext n; induction m with| zero=> ext v; change p^v.length * coin (1:ℂ) v= _; rcases v with _|⟨a,l⟩ <;> simp [coin,pow_zero]; all_goals rfl -- try
                                   | succ m ih=> change Ψ _ ( bite n G _ ( Pole.wing m ( T ∘ Fin.succ ) ( σ ∘ Fin.succ ) z n ))=_; rw [ lift_prod, show Ψ _ (Pole_leaf (n:=n) z ( T 0 ) ( σ 0 ))=_ from Pole_point p .., show Ψ _ ( Pole.wing m _ _ z n )=_ from ih ( T ∘ Fin.succ ) ( σ ∘ Fin.succ ) ]; simp only [ Pi.smul_apply,map_smul,LinearMap.smul_apply, smul_smul ]; rw [pow_succ ]; rfl
    refine Submodule.span_induction (p:=fun f _=> ρ ( f z )=p^m • f (p*z)) ?_ ?_ ?_ ?_ he
    · rintro F ⟨T,σ,h,rfl⟩; unfold Pole.saint; rw [ map_sum,Finset.smul_sum ]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,ht,smul_comm ]
    · simp only [Pi.zero_apply,map_zero,smul_zero]
    · intro v w _ _ hv hw; rw [Pi.add_apply,map_add,Pi.add_apply,smul_add,hv,hw]
    intro c x _ hx; change ρ ( (c:ℂ) • x z )=_; rw [map_smul,hx,smul_comm ]; rfl
variable (K: Box (Mob G)) {V:Law G}
private def story_story  (n:ℕ): Box (Mob G)→ₗ[ℂ] Box (Mob G):= Finsupp.lsum ℂ fun i:ℕ=> p^(i+n) • ( Finsupp.lsingle i )
private lemma story_single (n i:ℕ)(x:Mob G): story_story p n (.single i x)= p^(i+n) • .single i x:= Finsupp.lsum_single ..
private lemma story_live (n:ℕ): value (Mob G) z ( story_story p n K )= p^n • value (Mob G) ( p*z ) K:= by
    induction K using Finsupp.induction_linear with | zero=> simp only [map_zero,smul_zero]| add x y hx hy=> rw [map_add,map_add,map_add,hx,hy,smul_add ]| single a c=> rw [story_single,map_smul,value_sl,value_sl,pow_add,mul_smul, smul_comm (p^a) (p^n),mul_pow,mul_smul ]; -- orientation
private lemma story_wage (n:ℕ)(h:ℕ): story_story p n K h=p^(h+n) • K h:= by
    induction K using Finsupp.induction_linear with | zero=> simp | add x y hv hV=> rw [ map_add,Finsupp.add_apply,hv,hV,Finsupp.add_apply, smul_add ]| single a c=> rw [story_single,Finsupp.smul_apply]; by_cases he:a=h <;> simp [* ] -- no `split_ifs`
private lemma signBoot (hp:Ele d m V K) : ρ ( K h )= p^(h+m) • K h:= by
    have he(z:ℂ):= liftMark (z:=z) p (fun z=> value ( Mob G ) z K) hp.1; let X:= ( Boom 0 ρ ) K; let Y:= story_story p m K; have hX : X=Y:= by
        ext n m L; apply sub_eq_zero.mp; refine Motif.valuedZ ( X-Y ) (Garment.Wave.slice L) (fun u:ℂ=>?_) n; rw [map_sub, show value _ u X = value _ u Y from (linear_v ..).trans ( ( he u ).trans ( story_live p K _ ).symm ), sub_self,map_zero ]
    change _=_; rw [ ← whole (ρ) K, show (Boom 0 ρ) K = _ from hX, hiss ]; apply story_wage
-- strictly in DIM
lemma BudW (hp:Ele d m V K): Issue ( ↑m+( n:ℤ ) ) ( linear (Mob G) K n ):= by
   intro k l he; by_contra hb; obtain hx:= congr_fun (congr_fun ( signBoot (d:=d) (h:=n) 2 K hp ) k ) l; change ( ( 2:ℂ ) ^ l.length ) * _= ( 2^ (n+m) )* _ at hx; have ht := (mul_left_inj' hb).mp hx; exfalso; have hu : (2:ℝ)^ l.length=(2:ℝ)^(n+m):= by exact_mod_cast ht
   exact (ne_of_gt ( pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) ( by omega : n+m<l.length) )) hu
end YM.MS.Reed
