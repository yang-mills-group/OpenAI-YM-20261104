import YM.FVA2.DerivD.Traject
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-! # Positions change first gradients and convolution coefficients together. -/
variable {G:Gauge}{T U:Cast G}{P:Staff G}{A: Album G}{g:Cn}{n:ℕ} -- n autoImplicit
-- gamma conjugation follows `savvy`
lemma transform (x:Scan G n→ Cn)(p:Scan G n)(k:ℕ)(h:U*T=1): DerivD.Γ ( altered T U P ) ( fun v=> concert T v x ) p k=∑ i:LivesP p,DerivD.Γ P ( play T p ( decode p i ) • x ) ( decode p i ) k:= by
    ext1 y; simp_rw [ DerivD.Γ,_root_.sum_apply, appears, savvy _ _ h, concert,_root_.map_smul, smul_eq_mul,map_sum, Finset.smul_sum ]; rw [ Finset.sum_comm (s:= ( Finset.univ:Finset ( LivesP p ) ) ) ]; exact Finset.sum_congr rfl fun i hi=> Finset.sum_comm .. -- `savvy` after unfold? ok
lemma markV (h:Influence P A)(ht:U*T=1): Influence (altered T U P) ( marking T A ):= by
    intro n x hx v k; simp_rw [marking]; rw [ transform ( h:=ht ) ]; unfold concert; simp_rw [map_sum]; refine HasFDerivAt.fun_sum ?_; intro i _; change HasFDerivAt ( fun x=> coeff k ((play T v ( decode v i ) • A n x) (decode v i) )) _ x; exact Shard.along ( h n x hx ) _ _ _
-- price under coupling change using FPS keeps grade
abbrev reprice (g:Cn)(T:Staff G): Staff G:= fun v i j=> ( T v i j ).subst g
lemma rebill (X:Scan G n→Cn)(u:Scan G n)(k:ℕ)(hr:Rooted g) : DerivD.Γ ( reprice g P ) ( fun v=> ( X v ).subst g ) u k=∑ i∈Finset.range (k+1), ( coeff k (g^i) ) • DerivD.Γ P X u i:= by
    have he(i j) : Raise ( reprice g P ) i j u (fun t=>(X t).subst g )= ( Raise P i j u X ).subst g:= by unfold Raise reprice; simp_rw [LinearMap.coe_mk,AddHom.coe_mk, ← PowerSeries.coe_substAlgHom ( Reg.Choice.licence g hr ),map_sum,map_mul ];
    ext1 x; simp only [ DerivD.Γ,_root_.sum_apply,_root_.smul_apply, he, appears, FPS.coeff_substituted _ ( (coeff_zero_eq_constantCoeff_apply _).symm.trans hr ),smul_eq_mul,Complex.real_smul,Finset.mul_sum ]; rw [ Finset.sum_comm (s:=Finset.range (k+1)) ]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j' _=> by ring
lemma billA (h:Influence P A)(ht:Rooted g): Influence ( reprice g P ) ( tune g A ):= by
    intro n x hx v k; unfold tune; rw [ rebill (A n x) _ _ ht ]; simp_rw [FPS.coeff_substituted _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans ht),smul_eq_mul ]; exact HasFDerivAt.fun_sum fun i _=> ( h n x hx v i ).mul_const _
lemma billH (h:Influence P A)(ht:U*T=1)(hp:Rooted g): Influence ( altered T U ( reprice g P ) ) ( ExchangeA g T A ):= markV ( billA h hp ) ht
end YM.FVA2.DerivD
