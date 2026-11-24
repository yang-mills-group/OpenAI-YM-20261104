import YM.OPE.Compatible.Navy.Poly
/-!
# simultaneous factor brush-oath. includes all normalization powers
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Pilot
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace ENNReal
variable {G:Gauge}{I J U K:Type}[Fintype I][Fintype J][Fintype U]
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable (p: U ≃ I ⊕ J)
local notation "L" => prL p G
local notation "R" => prR p G
variable (A:Lid G I) (B:Lid G J)
def roomP : Keys G U→ℝ:=(A.f∘prL p G) + (B.f∘prR p G)
def weightP : Keys G U→ℝ:=(A.w ∘ prL p G)*(B.w ∘ prR p G)
lemma jet_purse (n:ℕ)(x: Keys G U): jet (roomP p A B) n x= jet A.f n (L x)+jet B.f n (R x):=by
     let u:= prL p G; let v:= prR p G; have he : ContDiffAt ℝ (n: WithTop ℕ∞) A.f 0:=A.F.smooth.of_le (WithTop.coe_le_coe.mpr le_top); have hv : ContDiffAt ℝ (n:WithTop ℕ∞) B.f 0:= B.F.smooth.of_le (WithTop.coe_le_coe.mpr le_top); have ha : ContDiffAt ℝ (n:WithTop ℕ∞) (A.f ∘ u) 0:= (show ContDiffAt ℝ _ _ _ from u.map_zero.symm ▸ he).comp _ u.contDiff.contDiffAt; have hh: ContDiffAt ℝ (n:WithTop ℕ∞) (B.f∘v) 0:= (show ContDiffAt ℝ _ _ _ from v.map_zero.symm ▸ hv).comp _ v.contDiff.contDiffAt
     unfold jet; rw [show roomP p A B=(A.f ∘ u)+(B.f ∘ v) from rfl, iteratedFDeriv_add_apply ha hh,Next.Foundations.jets_linear _ he, Next.Foundations.jets_linear _ hv,_root_.add_apply,mul_add];rfl
lemma haloNow : Cel (roomP p A B):=by
      apply quadratic_min; intro x hx; rw [jet_purse]; obtain ⟨a,ha,hA⟩:=A.bright; obtain ⟨b,hb,hB⟩:=B.bright; let P:=prL p G x; let Z:=prR p G x; by_cases hp:P=0
      · have hz: Z≠0:= fun h=>hx ((Pilot.drinks p G).injective (a₂:=0) (by rw [map_zero]; exact Prod.ext hp h))
        exact add_pos_of_nonneg_of_pos ((mul_nonneg ha.le (sq_nonneg _)).trans (hA P)) ((mul_pos hb (sq_pos_of_pos (norm_pos_iff.mpr hz))).trans_le (hB Z))
      exact add_pos_of_pos_of_nonneg ((mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hp))).trans_le (hA P)) ((mul_nonneg hb.le (sq_nonneg _)).trans (hB Z))
def cradle : Lid G U where
     f:= roomP p A B
     F := by
          let u:= prL p G; let v:= prR p G; refine ⟨?_,?_,fun i=>?_⟩
          · exact (((show ContDiffAt ℝ ∞ A.f (u 0) from u.map_zero.symm ▸ A.F.smooth)).comp _ u.contDiff.contDiffAt).add (((show ContDiffAt ℝ ∞ B.f (v 0) from v.map_zero.symm ▸ B.F.smooth)).comp _ v.contDiff.contDiffAt)
          · unfold roomP; simp only [Pi.add_apply,_root_.Function.comp_apply,map_zero,A.F.base0,B.F.base0,zero_add]
          rw [jet_purse,A.F.base1,B.F.base1,zero_add]
     fmeas:= (A.fmeas.comp (prL p G).continuous.measurable).add (B.fmeas.comp (prR p G).continuous.measurable)
     bright:= haloNow p A B
     w:= weightP p A B
     coat:= (((prL p G).map_zero.symm ▸ A.coat : ContDiffAt ℝ ∞ A.w ((prL p G) 0)).comp _ (prL p G).contDiff.contDiffAt).mul (((prR p G).map_zero.symm ▸ B.coat : ContDiffAt ℝ ∞ B.w ((prR p G) 0)).comp _ (prR p G).contDiff.contDiffAt)
     charm:=by unfold weightP; simp only [Pi.mul_apply,_root_.Function.comp_apply,map_zero]; exact mul_pos A.charm B.charm
     gleams := (A.gleams.comp (prL p G).continuous.measurable).mul (B.gleams.comp (prR p G).continuous.measurable)
variable {D: ChartRatio G}(h:LocalRatio D)
include h
lemma rime (x: Keys G U): ((cradle p A B).hat D) x= A.hat D (L x) * B.hat D (R x) :=by
      let T:=cradle p A B; let u:=prL p G x; let v:=prR p G x; let w:=warmer D T.w; have he (x: Keys G U): w x= warmer D A.w (prL p G x)*warmer D B.w (prR p G x):=by unfold w warmer; simp only [T,cradle, Pi.mul_apply,weightP,_root_.Function.comp_apply,jacSplit p];ring
      have hx: Pawn.mold w 0 x=Pawn.mold (warmer D A.w) 0 u*Pawn.mold (warmer D B.w) 0 v:=by
          apply ((Pawn.calm (T.winds _ h)).stale x).equality; apply ((((Pawn.calm (A.winds _ h)).stale u)).pile ((Pawn.calm (B.winds _ h)).stale v)).cong; filter_upwards with t; change w (_•_)=_; rw [he,map_smul,map_smul];rfl
      have hz: T.seedPrice D=A.seedPrice D* B.seedPrice D:= (he 0).trans (by rw [map_zero,map_zero];rfl)
      have hh: wheel (Pawn.mold T.f 2) x=wheel (Pawn.mold A.f 2) u * wheel (Pawn.mold B.f 2) v :=by
           have hd(j:ℕ) :jet T.f j x= _:= jet_purse p A B j x; apply JetS.eta<;>simp only [wheel, JetS.ml_s,JetS.ml_l,JetS.ml_h,hd] <;>(try simp only [u,v])<;>ring
      rw [show ((cradle p A B).hat D) x=JetS.plainJ ((T.seedPrice D)⁻¹)*(Pawn.mold w 0 x*wheel (Pawn.mold T.f 2) x) from rfl,hx,hh,hz, mul_inv_rev]; rw [show ∀ c d:ℝ,JetS.plainJ (d*c)=JetS.plainJ d*JetS.plainJ c from fun i j=>by apply JetS.eta<;>simp]; unfold Lid.hat Lid.heat; simp only [Pi.mul_apply]; unfold u v
      ring
end YM.OPE.Cascade.Pilot
