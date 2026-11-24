import YM.Contacts.Sentry.Tie
import YM.Integration.WilsonSeparatedLatticeStencil

/-! Finite signed sampling portfolios for the actual tie-avoiding coordinate
construction. The later coordinates can depend on each selected earlier node. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedBranchStencil
open Filter Function Set Contacts.Mat Contacts.Sensor
open scoped BigOperators Classical
variable {n m:ℕ} {H:ℝ}

structure Trial (n:ℕ) where
  sample:Type
  count:Fintype sample
  site:sample→Points n
  weight:sample→ℝ

def read (T:Trial n) (f:Points n→ℂ) : ℂ :=
  letI:=T.count
  ∑ j:T.sample,T.weight j • f (T.site j)

def bill (T:Trial n) : ℝ :=
  letI:=T.count
  ∑ j:T.sample,‖T.weight j‖

def single (X:Points n) : Trial n where
  sample:=Unit
  count:=inferInstance
  site:=fun _=>X
  weight:=fun _=>1

theorem read_single (X:Points n) (field:Points n→ℂ) : read (single X) field=field X:=by simp [read,single]
theorem bill_single (X:Points n) : bill (single X)=1:=by simp [bill,single]

def branch (U:Nodes m H) (child:Fin (m+1)→Trial n) : Trial n :=
  letI (i:Fin (m+1)):= (child i).count
  { sample:=Σ i:Fin (m+1),(child i).sample, count:=inferInstance
    site:=fun i=>(child i.1).site i.2, weight:=fun i=>bleed U.v i.1*(child i.1).weight i.2 }

theorem read_branch (U:Nodes m H) (child:Fin (m+1)→Trial n) (field:Points n→ℂ) :
    read (branch U child) field=∑ j,bleed U.v j • read (child j) field := by
  letI (i:Fin (m+1)):= (child i).count
  simp only [read,branch,Finset.smul_sum,smul_smul]
  exact Fintype.sum_sigma (fun (x:Σ i:Fin (m+1),(child i).sample)=>(bleed U.v x.1*(child x.1).weight x.2) • field ((child x.1).site x.2))

theorem bill_branch (U:Nodes m H) (child:Fin (m+1)→Trial n) {C:ℝ} (bounded:∀j,bill (child j)≤C) :
    bill (branch U child) ≤ (((m+1:ℕ):ℝ)*H^m)*C := by
  letI (i:Fin (m+1)):= (child i).count
  have sum:bill (branch U child)=∑ j,‖bleed U.v j‖*bill (child j):=by
    simp only [bill,branch,Finset.mul_sum,norm_mul]
    exact Fintype.sum_sigma (fun (x:Σ i:Fin (m+1),(child i).sample)=>‖bleed U.v x.1‖*‖(child x.1).weight x.2‖)
  rw [sum]
  calc
    _≤∑ _:Fin (m+1),H^m*C := Finset.sum_le_sum fun j _=>mul_le_mul (WilsonSeparatedLatticeStencil.weight U j) (bounded j) (by unfold bill; positivity) (pow_nonneg ((U.starts j).1.trans (U.starts j).2) _)
    _=_ := by simp [mul_assoc]

theorem issue (U:Nodes m H) (old new:Fin (m+1)→ℂ) {C:ℝ} (bounded:∀ j,‖old j-new j‖≤C) :
    ‖(∑ j,bleed U.v j • old j)-∑ j,bleed U.v j • new j‖≤ (((m+1:ℕ):ℝ)*H^m)*C := by
  rw [←Finset.sum_sub_distrib]
  calc
    _≤∑ j:Fin (m+1),‖bleed U.v j • old j-bleed U.v j • new j‖:=norm_sum_le _ _
    _≤∑ _:Fin (m+1),H^m*C := Finset.sum_le_sum fun j _=>by
      rw [←smul_sub,norm_smul]
      exact mul_le_mul (WilsonSeparatedLatticeStencil.weight U j) (bounded j) (norm_nonneg _) (pow_nonneg ((U.starts j).1.trans (U.starts j).2) _)
    _=_ := by simp [mul_assoc]

end YM.Integration.WilsonSeparatedBranchStencil
