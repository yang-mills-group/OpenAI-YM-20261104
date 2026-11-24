import YM.AllOrder.Fire.Cycle
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module GaussianScore
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] (A: Law Y)
    {ι:Type} [Fintype ι] (B:Basis ι ℝ Y) [MeasurableSpace Y][BorelSpace Y] (μ: Measure Y) [μ.IsAddHaarMeasure]
local notation "Ω"=>X×Y
local notation "T"=>ℝ×(X×Y)
variable {u:Book (X × Y)} (h:u 0=0) (hu:∀ n,Rank (X×Y) (n+2) (u n))
local notation "q"=> arrowR A μ u
local notation "W"=> Warm A μ u

def booked (u: Book (X×Y)) (n:ℕ): Ω→ℝ:= ∑ i∈ range (3*n+1),arrowR A μ u n i
local notation "Q"=> booked A μ u
include h hu
lemma template (n:ℕ): Rank T (3*n) (W n):= by
   let s: Book T:=plate A μ u; have hZ (n:ℕ): Rank Ω (3*n) (u n):= by by_cases hn:n=0; rw [hn,h]; exact Rank.nil _ _; exact (hu n).up (by omega)
   exact rank_log (u:=s) (fun _=> savor (rank_exp hZ h _) A μ) (funext fun i=> fix0 A μ h i) n
lemma returns (n:ℕ) (x:Ω): Warm A μ u n (1,x)= booked A μ u n x:= by
    let L:= ContinuousLinearMap.inl ℝ ℝ Ω; have hb : Rank ℝ (3*n) (view x (W n)):= by simpa [view,L] using! (template A μ h hu n).app L (0,x)
    let f:=view x (W n); change view x (W n) 1=_; rw [congr_fun (rank_taylor hb).2 1]; unfold delay booked; rw [Finset.sum_apply]; simp only [one_pow,one_smul]; rfl
lemma final_hot (n:ℕ) (x:X): booked A μ u n (x,0)=connected A μ u n x:= by
   rw [← returns A μ h hu]; change logS _ n=logS _ n; congr! 2; ext1 i -- check; simp
   change A.average μ _=A.average μ _; congr 1; ext y; simp [blow,wardrobe]
-- actual coupled rank recurrence improves cost on Ω
include B
lemma high_rank (r:ℕ) : ∀ n, Rank Ω (n+2) (q n r):= by
 induction r using Nat.strong_induction_on with
 | h r ih=>
    let hv: Clear u:= fun n=> (hu n).read
    rcases r with _|r; · intro n; rw [initial A μ h hv]; exact hu n
    rcases r with _|r; · intro n; rw [once A B μ h hv]; exact Rank.nil _ _
    intro n; rw [stepping A B μ h hv]; refine Rank.scal ((Rank.sum ?_).add (Rank.sum (fun i (_:i∈(univ:Finset ι))=> ?_))) _
    · intro k hk; apply Rank.sum; intro l hl; apply Rank.sum; intro i hi; exact (((ih l (by have he:= Finset.mem_range.mp hl; omega) k).der _).mul ((ih (r-l) (by omega) (n-k)).der _)).up (by have hh := Finset.mem_range.mp hk; omega)
    exact (((ih r (by omega) n).der _).der _).up (by omega)
lemma end_rank (n:ℕ) : Rank X (n+2) (connected A μ u n):= by rw [show connected A μ u n=booked A μ u n ∘ ContinuousLinearMap.inl ℝ X Y from funext fun x=> (final_hot A μ h hu n x).symm]; exact (Rank.sum fun k _=> high_rank A B μ h hu k n).lead _
end YM.AllOrder.Fire
