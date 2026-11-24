import YM.OPE.Compatible.Weave.Love
/-! # Wind basis matches Orthonormal continuum parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Woody Virgin Work.F08 Flume.Page Prairies Maxwell Maxwell.Free Finset
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis)
abbrev Own (p: Reed G):= ((roadV a p.1,p.2):Reed G)
local notation "Z"=> Signed.reflect a
lemma αProbe (p:Reed G): probeTurn Z (rayLeg p)= Rate a p.1 • rayLeg (Own a p):=by
     let i:=p.1.a; let b:=p.1.b; let X:=p.1.m; let f:=basis∘ X.get; let c:ℝ:= (X.length.factorial:ℕ); have ht :rayLeg p=c • Maxwell.Free.leg f p.2 i b:=rfl
     rw [ht]; ext1 u; change c*(turnJ Z⁻¹ u.val i b f) p.2 = Rate a p.1*(c*u.val i b f p.2)
     have hx(j:Axis):parity a j= φ a j:=by simp [Maxwell.Free.parity,φ,eq_comm]
     have hp(k:Axis): Ortho.move Z (basis k)= φ a k • basis k:=by ext l; by_cases h:k=a<;>by_cases H:l=a<;>simp [φ,h,H,eq_comm (a:=a)]
     rw [turns_apply,mirrored_inv,mirrored_inv]; simp_rw [reflect_entry,ite_mul,mul_ite,zero_mul,mul_zero,ite_smul,zero_smul];simp only [ite_self,Finset.sum_ite_irrel, sum_ite_eq', Finset.mem_univ, if_true,sum_const_zero,hx]
     rw [show (Ortho.move Z∘ f)=(fun i=> φ a (X.get i) • f i) from funext fun i=> hp _, u.val i b|>.map_smul_univ (fun i=> φ a (X.get i)) f];change c* ( (φ a i*φ a b)*(himp a p.1.m*u.val i b f p.2))= (φ a i*φ a b*himp a p.1.m)*_;ring
open Saga
def turnT (v:Saga G e k): Saga G e k:=match v with
| Saga.mon i h hk=> Saga.sml (∏ j, Rate a (i j).1) (Saga.mon (Own a ∘ i) h hk)
| Saga.empty=> Saga.empty
| Saga.add X Y=> Saga.add (turnT X) (turnT Y)
| Saga.sml a v=> Saga.sml a (turnT v) -- shadow a? `turnT v` recursion
lemma mirrSel (p:Reed G):mirrorBar Z (planeLeg p)=(Rate a p.1:ℂ) • planeLeg (Own a p):=by
    change reflectPol Z (realForm _)= _; rw [real_symbol, show reflectPol Z _=Maxwell.symbol _ _ from reflect_symbol ..,αProbe]; apply Maxwell.equalPol; intro A;rw [Maxwell.symbol_test, map_smul, show Maxwell.probe _ _=_ from (symbol_test A _ (rayLeg (Own a p)))]; change ↑(Rate a p.1 * ((rayLeg (Own a p)) _))= (Rate a p.1:ℂ) * _; exact Complex.ofReal_mul .. 
lemma mirrored_saga (v:Saga G e k): terra (turnT a v)=mirrorBar Z (terra v):=by
   induction v with
   | @mon i l h hs=> symm; change reflectPol Z (realForm (∏ j,planeLeg (l j)))=_; rw [map_prod,map_prod]; simp_rw [show ∀ i:Reed G,reflectPol Z (realForm (planeLeg i))=_ from fun i=>mirrSel a i]; change (∏ j, (Rate a (l j).1:ℂ) • planeLeg (Own a (l j)))=((∏ j,Rate a (l j).1:ℝ):ℂ) • ∏ j,planeLeg (Own a (l j)); simp only [← MvPolynomial.C_mul',Finset.prod_mul_distrib, Complex.ofReal_prod,map_prod]
   | empty=> exact (map_zero _).symm
   | add _ _ h p=> exact (congr_arg₂ (·+·) h p).trans (map_add ..).symm
   | sml v x hp=> simp only [turnT,terra,hp,map_smulₛₗ]; simp
lemma pole_align (x:Cover): incVec 1 ((Wm a).act x)=through a (incVec 1 x):=by ext k; simp [through,run_axis]
lemma summed (x:E4)(p q: WickPol G): Maxwell.Free.score a x p q = bond G (through a x) x (mirrorBar Z p) q:=by
    let P:= points fun _ : Fin 1=> x
    have hv: Table.Pairing.closedUp a P P= pairPoints (through a x) x:=by
         ext1 i; refine Fin.addCases ?_ ?_ i
         · intro i; fin_cases i; rw [Table.Pairing.enter]; rfl
         intro i;fin_cases i; rw [Table.Pairing.leave];rfl
    unfold Maxwell.Free.score cabinet; rw [hv,bond_eval]; congr 1; funext i; fin_cases i<;>rfl
end YM.OPE.Quit
