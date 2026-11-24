import YM.MS.Milk.Ribbon
/-!
# Recover Wick comparator. Including extent.Put each arbitrary radius fields through labelled finite-pol. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell Local.Physical
open Labels
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {W X: Type}[LinearOrder W]{G:Gauge}{p:Geo X}{x:Position W X}{B: Deck G}{Y:Rake.Dance G X W}{d n:ℕ}
def backK (v:Key G): Maxwell.Slot G→₀ℂ:= ∑ i:Fin (legDim G v.1), ( ( ( Labels.axes G v.1 ).coord v.2 ( gaugeJet ( Maxwell.frame G v.1 i ) ):ℝ ):ℂ ) • Finsupp.single ( ⟨ v.1,i ⟩ : Maxwell.Slot G ) 1
lemma γ_map : Normal.exchange ( backK ( G:=G ) )= reduceEq := by
   ext1 i; rw [ Normal.exchange_x, backK,map_sum, reduceEq,MvPolynomial.aeval_X ]; simp_rw [ map_smul, Normal.glyph,Finsupp.linearCombination_single, one_smul, MvPolynomial.C_mul' ]; rfl -- namesp
variable {z: Points n}
open Next.Rank.Configuration
local notation "M"=>perSlot (fun _:Fin n=>backK ( G:=G ) )
lemma instinct (h:z∈conf _): entry G z.ofLp (show Injective z.ofLp from h)= Normal.scope M (frameX h):= by
    apply Normal.Symmetric.ext; funext v q; rcases v with ⟨a,i⟩; rcases q with ⟨b,j⟩; let d:= generation i+generation j; let c:KeyIn G d:= ⟨i,by unfold d; omega ⟩; let x:KeyIn G d:=⟨j, by unfold d; omega ⟩; change ( if a=b then 0 else ( legKernel (Drops.slope i) (Drops.slope j) (z a-z b):ℂ))= ( currentX h G d ).cov (a,c) (b,x) -- defeq mapper?
    split_ifs with he; · rw [he,Next.Rank.Prayer.dies];
    exact (Next.Rank.Prayer.pays h a b he c x).symm
lemma Era (h:z∈conf _) (f:Fin n→ Pol G): Wick.moment G z (fun i=> Maxwell.reduceEq ( f i ))= blend ( entry G z.ofLp ( show Injective z.ofLp from h ) ) 0 ( pot Finset.univ f ):= by
   rw [ Wick_reads h ]; simp_rw [← γ_map]; change _=_; rw [ show (∏ i: Fin n,MvPolynomial.rename (fun y=>(i,y)) (Normal.exchange backK ( f i )))= Normal.exchange M ( pot Finset.univ f ) from ?_,wets, show Normal.reads M 0=0 from funext fun i=> Finsupp.linearCombination_zero_apply .., ← instinct h ]; unfold pot; rw [ map_prod ]; exact Finset.prod_congr rfl fun i _=> ( posts (fun _ : Fin n=> backK ( G:=G )) i ( f i ) ).symm
variable {t:Normal.Symmetric X}
lemma potE (L:Album X G)(p:Normal.poly X): bowl L p []= MvPolynomial.aeval (fun (_: X)=> (0:ℂ)) p:= by
    induction p using MvPolynomial.induction_on with
    | C c=> rw [t_C,MvPolynomial.aeval_C,Algebra.algebraMap_self]; rfl
    | add p q hp hq=> rw [map_add,Pi.add_apply,map_add,hp,hq]
    | mul_X p i he=> rw [t_M,t_X, scattered, scatter_nil ]; rw [ ( L.line i ) [] ( by rw [mod_int]; simp ), map_mul,MvPolynomial.aeval_X,mul_zero,mul_zero] -- simp ambiguity
lemma harvest (hp:z∈ conf _) (f:Fin n→ Pol G): Tint ( Forum G z.ofLp ) (entry G z.ofLp ( show Injective z.ofLp from hp)) ( pot Finset.univ f ) [] = Wick.moment G z (fun i=> Maxwell.reduceEq ( f i )) := by rw [ Tint,LinearMap.comp_apply,potE ]; exact ( Era hp f ).symm
end YM.MS.Milk
