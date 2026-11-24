import YM.Integration.WilsonPositionProgramTrialHomeDose
import YM.Integration.WilsonIndependentFittedRelativeClock
import YM.Integration.WilsonIndependentFittedMixedCash

/-! Recover the evaluated full internal dose from its public Wick readings
at any older held clock, using the already enrolled inverse on this cut. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookDoseReturn
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Blue Bank Wilson Tree Power PowerSeries
open Embroider Precision Exterior Fountain Soil Gauge Source Source.Drops Labels WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Classical
variable {G:Gauge}{k u e:ℕ}

private def reading (B:Cost)(q:ℕ)(t:ℝ):Cost→ₗ[ℝ]ℂ where
  toFun c:=cash q t (embed (reel B c))
  map_add' x y:=by simp [WilsonPhysicalMarkedDefect.RawBank.cash,mul_add,Finset.sum_add_distrib]
  map_smul' a x:=by
    have hs:reel B (a • x)=a • reel B x:=by
      change (substAlgHom _ (a • x))=a • (substAlgHom _ x)
      exact map_smul _ _ _
    rw [hs]
    simp only [WilsonPhysicalMarkedDefect.RawBank.cash,embed,coeff_map,map_smul,
      RingHom.id_apply,Complex.real_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (t:ℂ)^j * (algebraMap ℝ ℂ) (a * ((coeff j) (reel B x))) = _
    rw [map_mul]
    change (t:ℂ)^j * ((a:ℂ) * _) = (a:ℂ) * ((t:ℂ)^j * _)
    ring

theorem linear (H:Hol G)(Q:SealR G)(w:Rails Q.h k u e)(E W B V Z:Credit):
    ∃C:Credit,∀(X:CutsP H Q.ans Q.path w E W B V)
      (_:AheadT H X.vesselsC W V Q Z)(read:Cost→ₗ[ℝ]ℂ)(a:ℝ),
      (∑i,‖read (dose X a i)‖) ≤ X.vesselsC.cash C X.m*(∑j,‖read (publicDose Q X a j)‖):=by
  obtain ⟨D,grant⟩:=belt (C:=Z) (T:=Q.ans) (p:=Q.path) (e:=e) (H:=H) (E:=E) (W:=W)
  let n:ℝ:=Fintype.card (Alma Q.F)
  refine ⟨(pur n).prodC D,?_⟩
  intro X Y read a
  let F:=publicDose Q X a
  let r:=X.vesselsC.cash D X.m
  let M:Wall Q.F:=(Wray X.ax X.tx Q.ans Q.path X.N X.m)⁻¹
  have price (i j):‖M i j‖ ≤ r:=by
    have old:Y.p.f.arch.V.anchor ≤ X.m:=Y.p.tap.symm ▸ X.ha
    have sal:=grant Y.p.f.arch Y.stamps X.m X.m X.N X.N old le_rfl
      ((Nat.le_add_right X.m X.i).trans (X.hc.trans X.hn)) ((Nat.le_add_right X.m X.i).trans (X.hc.trans X.hn)) i j
    dsimp only [Realm.cash] at sal
    rw [Y.p.depths,Y.p.lands,Y.p.modes] at sal
    exact sal.main
  have due:0 ≤ ∑j,‖read (F j)‖:=Finset.sum_nonneg fun j _=>norm_nonneg _
  have inv:= (WilsonPositionProgramTrialHomeDose.original Q X a).1
  change (∑i,‖read (dose X a i)‖) ≤ _*∑j,‖read (F j)‖
  rw [←inv]
  calc
    (∑i,‖read (PermuteLens X.ax X.tx Q X.N X.m F i)‖) ≤ ∑_i:Alma Q.F,r*∑j,‖read (F j)‖:=by
      apply Finset.sum_le_sum
      intro i _
      change ‖read (∑j,M i j • F j)‖≤_
      rw [map_sum,Finset.mul_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _=>by
        rw [map_smul,norm_smul]
        exact mul_le_mul_of_nonneg_right (price i j) (norm_nonneg _))
    _ = n*r*(∑j,‖read (F j)‖):=by simp [n,nsmul_eq_mul,mul_assoc]
    _ ≤ _:=by
      apply mul_le_mul_of_nonneg_right _ due
      change n*D.buy _ ≤ ((pur n).prodC D).buy _
      rw [Credit.products]
      exact mul_le_mul_of_nonneg_right (pure_goal n _) (zero_le_one.trans (D.purchase (X.vesselsC.depth _ X.ha)))

/-- A single price is issued before the source, its amplitude, the placement,
the older clock and the requested real finite evaluation. -/
theorem original (H:Hol G)(Q:SealR G)(w:Rails Q.h k u e)(E W B V Z:Credit):
    ∃C:Credit,∀(X:CutsP H Q.ans Q.path w E W B V)
      (_:AheadT H X.vesselsC W V Q Z)(host:ℕ)(_older:host ≤ X.m)(a:ℝ)(q:ℕ)(t:ℝ),
      let obs:=fun c=>cash q t (embed (clock X.ax X.tx X.N X.m host c))
      (∑i,‖obs (dose X a i)‖) ≤ X.vesselsC.cash C X.m*(∑j,‖obs (publicDose Q X a j)‖):=by
  obtain ⟨C,paid⟩:=linear H Q w E W B V Z
  refine ⟨C,?_⟩
  intro X frame host older a q t obs
  let B':=relativeF X.ax X.tx X.N host (X.m-host)
  have actual:∀c,obs c=reading B' q t c:=fun c=>by
    change cash q t (embed (clock X.ax X.tx X.N X.m host c))=cash q t (embed (reel B' c))
    have book:=WilsonIndependentFittedRelativeClock.reported X.ax X.tx X.N host (X.m-host) c
    rw [show host+(X.m-host)=X.m by omega] at book
    rw [book]
  simpa only [actual] using paid X frame (reading B' q t) a

end YM.Integration.WilsonIndependentNotebookDoseReturn
