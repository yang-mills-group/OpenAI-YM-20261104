import YM.AllOrder.Fire.Plex
/-!
# The connected part as a **finite** recursion of two-leg contractions

Basis arbitrary. Two powers t for each integration edge. Zero classical terms
in connection. No cost of the left-out chart χ.
-/
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
local infix:65 " #+ " => alters
variable {u:Book (X × Y)} (hu:u 0=0) (h:Clear u)
local notation "W"=>Warm A μ u
local notation "E"=> fronds A B (Warm A μ u)
local notation "I"=> fun i:ι=>((0:X),Inv A B i)
include h hu
lemma interface (n:ℕ) (z:Ω): Warm A μ u n (0,z)=u n z:= Function.const _ (Function.const _ (Function.const _ (Function.const _ (Function.const _ (by
   change logS (swap (plate A μ u) (0,z)) n=_
   rw [show swap (plate A μ u) (0,z)= expS (swap u z) from ?_, log_expS]
   ext1 i; change A.average μ _= _; apply (@Eq.trans _ _ (A.average μ (fun _=>EXP u i z)) _) _ (average_const ..); apply congr_arg; ext; simp [blow,wardrobe]
-- even exponent expansions on all T. base term needed.
  ) (inferInstance : NormedAddCommGroup X)
  ) (inferInstance : NormedSpace ℝ X)
  ) (inferInstance : FiniteDimensional ℝ X)
  ) (h)
  ) (hu)
def arrowR (u:Book (X×Y))(n:ℕ):= beam (Warm A μ u n)
local notation "R"=> arrowR A μ u
lemma initial (n:ℕ) : arrowR A μ u n 0=u n:= by ext z; rw [arrowR,beam,someJ_zero, view]; apply interface <;> assumption
-- one-zero
omit h hu in
lemma soft_price (v:Book T) (hf:Clear v) : Clear (fronds A B v):= Function.const _ (Function.const _ (Clear.sum _ fun i _=> (Clear.prod (u:= slope (foot ((I) i)) v) (hf.step _) (Clear.step _ hf)).add (Clear.step _ (Clear.step _ hf))
  ) (inferInstance : MeasurableSpace Y)
  ) (inferInstance : BorelSpace Y)
lemma shifter (m n:ℕ): slope ((1:ℝ),(0:Ω)) W n= (fun z:T=> z.1)*(E n) := Function.const _ (by ext1 x; rw [equateF A B μ hu h,spring]; rfl
  ) (m)
include B in
lemma once (n:ℕ): arrowR A μ u n 1=0:= by ext1 x; change beam (W n) (0+1) x=_; let ht:=eventA A μ h hu n; rw [beam_step _ ht]; rw [show diff' _ (W n)= _ from shifter A B μ hu h 0 n]; simp [beam,view] -- normalization
-- after summing coupling & time grades, branch section. distinguish loop contraction and cross. Keep tensor argument basis. total2 powers.
abbrev connection (f g:Ω→ℝ) : Ω→ℝ:= ∑ i, diff' ((I) i) f * diff' (vec B i) g
lemma slate (m n:ℕ) : beam (E n) m = (∑ i∈Finset.range (n+1), ∑ j∈Finset.range (m+1), connection A B (R i j) (R (n-i) (m-j))) + infinity A B (R n m):= by
   have hh :=eventA A μ h hu; let v := W
   let f (i:ι) (n:ℕ):= diff' (foot ((I) i)) (v n)
   let g (i:ι) (n:ℕ):= diff' (foot (vec (X:=X) B i)) (v n)
   let l (i:ι) (n:ℕ):= diff' (foot ((I) i)) (g i n)
   have hf (i:ι):Clear (f i):= Clear.step _ hh; have hg (i:ι):Clear (g i):= Clear.step _ hh; have hl(i:ι):Clear (l i):=Clear.step _ (hg i)
   have he : ∀ a:ι, beam ((f a #+ g a) n) m=(∑ i∈ Finset.range (n+1), ∑ j∈ Finset.range (m+1), diff' ((I) a) (R i j)* diff' (vec B a) (R (n-i) (m-j))):= by
     intro a; rw [aligned,beam_sum _ (fun j _=>(hf a j).mul (hg a _))]; refine sum_congr rfl (fun i _=>?_); rw [beam_mul (hf a _) (hg a _),aligned]; refine sum_congr rfl (fun j _=> ?_); exact congr_arg₂ (·*·) (along ((I) a) (hh i) j).symm (along (vec (X:=X) B a) (hh (n-i)) (m-j)).symm
   let F a:= beam ((f a #+ g a) n) m
   change beam _ _=_; rw [show E n=∑ i,( (f i #+ g i) n+ l i n ) from Finset.sum_apply n _ (fun i:ι=>_)]
   rw [beam_sum (X:=Ω) _ (fun i _=> ((hf i|>.prod (hg i)) n).add (hl i _))]; simp_rw [beam_add ((hf _|>.prod (hg _)) _) (hl _ _), he]; rw [sum_add_distrib,sum_comm]; apply congr_arg₂ (·+·)
   · refine sum_congr rfl fun i _=>sum_comm
   apply sum_congr rfl; intro i _; refine (along ((I) i) (hg i _) m).symm.trans (congr_arg _ (along (vec (X:=X) B i) (hh n) m).symm)

lemma stepping (m n:ℕ) : R n (m+2)= (↑(m+2:ℕ):ℝ)⁻¹ • ((∑ i∈Finset.range (n+1), ∑ j∈Finset.range (m+1), connection A B (R i j) (R (n-i) (m-j))) + infinity A B (R n m)):= by
 rw [←slate A B μ hu h]; change beam (W n) (m+1+1)=_; rw [beam_step _ (eventA A μ h hu n), show diff' _ (W n)= _ from shifter A B μ hu h m n]; apply congr_arg; ext1 x; unfold beam; rw [show view x _= _ from (show view x ((fun p:T=>p.1)*E n)=(fun x:ℝ=> x^1)* view x (E n) from (by ext; simp [view])), jo_shift]; simp -- proof >
 exact (loc_beam _ (soft_price (X:=X) A B _ (eventA A μ h hu) n)).smooth.contDiffAt
end YM.AllOrder.Fire
