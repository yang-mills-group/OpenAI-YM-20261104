import YM.Integration.WilsonOriginalAlternativeSelectedPage

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialWallet
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {V:Type} [DecidableEq V] [Fintype V]
  (d:V→ℕ) (N p K:ℕ) (o:V→Site (R.family.side K p)) (v:∀j,R.family.label (d j)) (a τ:ℝ)

def price (j:V):ℝ:=WilsonOriginalStarPrimaryCatalog.rent R N p K (d j) o j (v j) (fun _=>1) a

def radius (j:V):ℝ:=τ/(((Fintype.card V:ℝ)+1)*(1+|price R d N p K o v a j|))

omit [DecidableEq V] in
theorem positive (pos:0<τ) (j:V):0<radius R d N p K o v a τ j:=by
  unfold radius
  positivity

omit [DecidableEq V] [Fintype V] in
private theorem serial (w:V→ℝ) (j:V):
    WilsonOriginalStarPrimaryCatalog.rent R N p K (d j) o j (v j) w a=w j*price R d N p K o v a j:=by
  unfold price WilsonOriginalStarPrimaryCatalog.rent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [one_mul,mul_assoc]

omit [DecidableEq V] in
theorem paid (pos:0<τ):
    WilsonOriginalAlternativeSelectedGuard.rent R N p K o d v (radius R d N p K o v a τ) a ≤ τ:=by
  let b:ℝ:=(Fintype.card V:ℝ)+1
  have bp:0<b:=by dsimp [b];positivity
  have each(j:V): WilsonOriginalStarPrimaryCatalog.rent R N p K (d j) o j (v j)
       (radius R d N p K o v a τ) a ≤ τ/b:=by
    rw [serial,radius,←div_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity:0<1+|price R d N p K o v a j|)).2
    apply mul_le_mul_of_nonneg_left _ (div_pos pos bp).le
    linarith only [le_abs_self (price R d N p K o v a j)]
  refine (Finset.sum_le_sum (fun j _=>each j)).trans ?_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_div_assoc']
  exact (div_le_iff₀ bp).2 (by dsimp [b];nlinarith only [pos])

end YM.Integration.WilsonOriginalAlternativeTrialWallet
