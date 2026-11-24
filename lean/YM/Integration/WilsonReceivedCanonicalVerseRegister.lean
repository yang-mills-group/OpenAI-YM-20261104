import YM.Integration.WilsonReceivedCanonicalVerseBasis
import YM.Integration.WilsonReceivedCompactVerseEntrance
import YM.Integration.OriginalCoverReanchoring

/-! Price every genuinely used registered socket on its own finite and covered sides
before the cutoff, the period and the actual diagnostic coordinates are supplied. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalVerseRegister
open Function Finset Lattice Laurent Wilson RG Source Labels
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords WilsonReceivedCanonicalVerseBasis
open WilsonReceivedCompactVerseEntrance (CoverBill)
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(k:I → ℕ){h:I → ℕ}
variable (κ:(i:I) → Knob (h i))(pt:I → Chamber)

def offer (q:(j:I) → Choice R k j)(j:I)(_:Unit):Seed G (h j):=WilsonReceivedCanonicalVerseBasis.basis R k κ pt j (q j)

def start (q:(j:I) → Choice R k j):Outerm G h:=independent (offer R k κ pt q)

theorem original (e:ℕ){s:ℝ}(hs:0<s):∃B:ℝ,1 ≤ B ∧ ∀q,
    Wellness k (start R k κ pt q) ∧ CoverBill (start R k κ pt q) e s B ∧
      WilsonFiniteMarkedHistoryStep.paired e (start R k κ pt q) s B:=by
  classical
  have get (q:(j:I) → Choice R k j):∃b:ℝ,1 ≤ b ∧ WilsonFiniteMarkedHistoryStep.paired e (start R k κ pt q) s b:=
    WilsonDepositedFreshFiniteHistory.source (offer R k κ pt q) (fun j _=>grade R k κ pt j (q j)) hs
  choose fee one filed using get
  let B:=1+∑q,fee q
  have non (q:(j:I) → Choice R k j):0 ≤ fee q:=zero_le_one.trans (one q)
  have inside (q:(j:I) → Choice R k j):fee q ≤ B:=by
    exact (single_le_sum (fun i _=>non i) (mem_univ q)).trans (by dsimp [B]; linarith)
  refine ⟨B,by dsimp [B]; linarith [sum_nonneg (s:=univ) (fun i _=>non i)],?_⟩
  intro q
  have common:WilsonFiniteMarkedHistoryStep.paired e (start R k κ pt q) s B:=by
    intro n o S a ha r
    exact (filed q n o S a ha r).more (pow_le_pow_left₀ (non q) (inside q) _)
  refine ⟨(OriginalCoverReanchoring.deposited (offer R k κ pt q) (fun j _=>grade R k κ pt j (q j))).1,?_,common⟩
  exact fun y S a ha r=>(common 1 y S a ha r).access

def shoulder (j:I)(c:Choice R k j):ℝ:=
  match c with
  | .inl _ => 1
  | .inr s => WilsonOriginalStarLaurentWallet.wallet R (k j) 0 (WilsonOriginalStarLaurentWallet.lag R (k j) s)

omit [Fintype I] [DecidableEq I] in
theorem measured (N p b:ℕ)(live:b ≤ N)(v:(j:I)→R.family.label (k j))(j:I)(c:Choice R k j):
    ‖dose R k N p b v j c‖ ≤ shoulder R k j c*(R.family.labels.level (k j)).coeffSize (v j):=by
  classical
  cases c with
  | inl u =>
    change ‖v j 0‖ ≤ 1*(R.family.labels.level (k j)).coeffSize (v j)
    rw [one_mul]
    exact single_le_sum (fun i _=>norm_nonneg (v j i)) (mem_univ 0)
  | inr s =>
    let z:=WilsonOriginalStarLaurentWallet.lag R (k j) s
    let F:=R.family.labels.level (k j)
    let v':=F.core (v j)
    let g:=regulatorRun R.family N p b
    let t:=(R.family.path.rep N p b).p.threshold
    let c:=(fun a=>WilsonOriginalStarLaurentWallet.coefficient R (k j) g t v' a)
    let w:=WilsonOriginalStarLaurentWallet.wallet R (k j) 0 z
    have fee:=WilsonOriginalStarLaurentWallet.fine R (k j) N p b live v' 0 z
    simp only [zero_mul,Real.exp_zero,mul_one] at fee
    let l:=WilsonOriginalStarLaurentWallet.lag R (k j)
    have single:(if l s=z then ‖c s‖ else 0) ≤ ∑i,if l i=z then ‖c i‖ else 0:=
      single_le_sum (f:=fun i=>if l i=z then ‖c i‖ else 0) (fun i _=>by split <;> positivity) (mem_univ s)
    rw [if_pos rfl] at single
    have zero:0 ≤ w:=by
      dsimp [w,WilsonOriginalStarLaurentWallet.wallet]
      exact sum_nonneg fun i _=>by split <;> positivity
    exact (single.trans fee).trans (mul_le_mul_of_nonneg_left (Work.G08.size_core F (v j)) zero)

end YM.Integration.WilsonReceivedCanonicalVerseRegister
