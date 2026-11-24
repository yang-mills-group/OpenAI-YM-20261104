import YM.RGLocalTaylor.Read.Register

/-!
# Compatible through ALL M. Clean reader reconstruction

No below-order label depends on which M was chosen. This is regulator
consistency on that step; not asserting a construction parametrized
the same off-trajectory observers/histories or other schemes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Read
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n j M r : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {I : Cash W s μ L Q o C T R'}
open RG01.Survive
variable (X:Match.Alliance I H 1 0) (γ : ℝ)
    (take : H.fragrances→ℕ→Prop)

variable {w : H.fragrances} in
private lemma moves' (M' : ℕ) (hp:M≤M') (g : Option (Fin w.fst)→Orders M) (ht:atGrade (z:=w) g ≤ M) :
    aliquot (Mayer.issue H χ M) w g=aliquot (Mayer.issue H χ M') w (fun i=> Fin.castLE (by omega : M+2 ≤ M'+2) (g i)):= by
  have h i:(g i).val ≤ atGrade (z:=w) g:= Finset.single_le_sum (f:=fun (i:Option (Fin w.fst))=> (g i).1) (fun _ _=>Nat.zero_le _) (mem_univ i)
  funext V; apply prod_congr rfl; intro i _
  let u : Fin (M+1) := ⟨(g i).val,Nat.lt_succ_of_le ((h i).trans ht)⟩
  exact congr_fun (Mayer.cast_issue (χ:=χ) (p:=w.2 i) u (Fin.castLE (by omega : M+1≤M'+1) u) rfl) V

lemma align (M' : ℕ) (hp:M≤M') (ht:∀ z n,take z n→ n ≤ M):
    field take (Mayer.issue H χ M)= field take (Mayer.issue H χ M'):= by
  funext w U
  unfold field; congr 1
  let f (t:Option (Fin w.fst) → Orders M) (i : Option (Fin w.fst)):= Fin.castLE (by omega : M+2 ≤ M'+2) (t i)
  let S L:= Finset.univ.filter (fun t:Option (Fin w.fst) → Orders L=> take w (atGrade t))
  have hr t:atGrade (z:=w) (f t)=atGrade (z:=w) t:=rfl
  apply Finset.sum_bij (fun t _=>f t)
  · intro t H; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp H).2⟩
  · intro t ht p hp h; exact funext fun i=> Fin.ext (congr_arg (@Fin.val (M'+2)) (congr_fun h i))
  · intro t hT
    have h i:(t i).val ≤ atGrade (z:=w) t:= Finset.single_le_sum (f:=fun (i:Option (Fin w.fst))=> (t i).1) (fun _ _=>Nat.zero_le _) (mem_univ i)
    let t' i: Fin (M+2) :=⟨(t i).1,Nat.lt_add_one_of_le ((h i).trans ((ht _ _ (mem_filter.mp hT).2).trans (Nat.le_succ _)))⟩
    refine ⟨t',mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hT).2⟩,rfl⟩
  exact fun i hi=> congr_fun (moves' M' hp _ (ht _ _ (mem_filter.mp hi).2)) U

-- Fields for a chosen thermal power don't change with calendar.
lemma horizon (M' : ℕ)(hp:M≤M') (hT:∀ z n,¬ take z n→ n≤M) :
    modeled (χ:=χ) X γ take (Mayer.issue H χ M)= modeled (χ:=χ) X γ take (Mayer.issue H χ M') := by
  unfold modeled meticulous; rw [align _ _ hp hT]
end YM.RGLocalTaylor.Read
