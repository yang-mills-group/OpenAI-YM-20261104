import YM.Integration.WilsonVacuumPreResetPeriodIndex
import YM.Integration.WilsonVacuumPreResetPeriodTail
import YM.RG01Estimate.Stanchion

/-! The original corrected independent period expansion on one finite,
spatially bounded, signed catalogue of the measured reset. The width D is
chosen first. The finitary countable tail can subsequently be sent to zero
on the fixed original finite torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPeriodCatalogue
open Function Filter Finset Lattice Wilson RG Marker WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat RG01Estimate IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection Quotes LocalComparison.Global Push.AbsoluteSums Push.AbsoluteSums.Animals
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetPeriodIndex WilsonVacuumPreResetPeriodTail
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

def live (B:BudgetPoint)(Z:SeriesA G)(A:Activities G n)(D t:ℕ):Finset ℕ:=
  (indices n Z t).filter (fun i=>short B D A.reg i)

def submitted (A:Activities G n)(closed:Finset ℕ):ℕ → Config G n → ℝ:=
  fun i=>if i∈closed then A.E i else 0

def model (B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ → ℕ → ℝ)(D t:ℕ):Precise.Leads G n:=
  let A:=entries n B σ C Z k
  ⟨⟨A.reg,A.forced⟩,A.E,submitted A (live B Z A D t),
    quote (Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) k⟩

def localRack (B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ → ℕ → ℝ)(D t:ℕ):
    let M:=model (n:=n) B σ C Z k D t
    Abacus.Rack M.listing (D*(4*B.B+2)+2*B.B) M.pioneers:=by
  let A:=entries n B σ C Z k
  let S:=live B Z A D t
  exact ⟨S,fun i x=>if (A.reg i).site=x then 1 else 0,fun i h=>if_neg h,
    fun i _=>by simp,fun _ _ _=>by split <;> norm_num,fun i hi x hx=>by
      have e:(A.reg i).site=x:=by simpa using hx
      rw [←e]
      exact housed _ _ _ _ (mem_filter.mp hi).2⟩

theorem moves (B:BudgetPoint)(σ C:ℝ)(Z:SeriesA G)(k:ℕ → ℕ → ℝ)(D t:ℕ)(s:Signed)(b:Site n):
    let M:=model (n:=n) B σ C Z k D t
    Nonempty (Caddy.Mirrors M.listing.reg s b M.trunk) ∧
    Nonempty (Caddy.Mirrors M.listing.reg s b M.pioneers) ∧
    Nonempty (Caddy.Mirrors M.listing.reg s b (-(M.trunk-M.pioneers))):=by
  intro M
  let A:=entries n B σ C Z k
  let W:=(WilsonVacuumPreResetPeriodIndex.original (n:=n) B σ C Z k s b).some
  let g:=W.mirror
  have eqs (i)(nz:A.E i≠0):g.walks i∈live B Z A D t ↔ i∈live B Z A D t:=by
    simp only [live,mem_filter,before,short]
    have ht:depth n Z (g.walks i)=depth n Z i:=W.tier i nz
    have hh:(A.reg (g.walks i)).support=(A.reg i).support.image (affine s b):=g.hues i
    have sameCov:coverNumber B.B ((A.reg i).support.image (affine s b))=coverNumber B.B (A.reg i).support:=
      Seat.visit_count (s,b) (A.reg i).support
    rw [ht,hh,sameCov]
  have P (i):M.pioneers (g.walks i)=M.pioneers i ∘ pull s b:=by
    change submitted A (live B Z A D t) (g.walks i)=submitted A (live B Z A D t) i ∘ pull s b
    by_cases z:A.E i=0
    · have zz:A.E (g.walks i)=0:=(g.posts i).trans (by rw [z];rfl)
      simp only [submitted,z,zz,ite_self]
      rfl
    by_cases h:i∈live B Z A D t
    · simp only [submitted,(eqs i z).2 h,h,if_true]
      exact g.posts i
    · have h':g.walks i∉live B Z A D t:=fun hv=>h ((eqs i z).1 hv)
      simp only [submitted,h',h,if_false]
      rfl
  refine ⟨⟨g⟩,⟨⟨g.walks,g.hooks,g.hues,P⟩⟩,⟨⟨g.walks,g.hooks,g.hues,?_⟩⟩⟩
  intro i
  funext U
  change -((A.E (g.walks i) U)-(M.pioneers (g.walks i) U))= -((A.E i (pull s b U))-(M.pioneers i (pull s b U)))
  rw [congrFun (g.posts i) U,congrFun (P i) U]
  rfl

theorem original (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:preExponent (Song.headline B)/B.B ≤ σ/4)(blocks:2≤B.B)
    (Z:SeriesA G)(draw:Draw Z σ C)(k:ℕ → ℕ → ℝ)(D:ℕ){η:ℝ}(ep:0<η):
    let far:=Real.exp (-(3:ℝ)*(D+1))*quote (Z.map (FundedCorrectedPeriod.piece n (Song.headline (Song.headline B)) σ C)) k
    ∀ᶠ t:ℕ in atTop,let M:=model (n:=n) B σ C Z k D t
      Precise.Suggests B M (far+η) M.bill:=by
  intro far
  let A:=entries n B σ C Z k
  let X:Listing G n:=⟨A.reg,A.forced⟩
  have width:preExponent B / B.B≤σ/4:=
    (div_le_div_of_nonneg_right (show preExponent B≤preExponent (Song.headline B) by
      change B.supportExponent+3≤(B.supportExponent+3)+3;linarith) (Nat.cast_nonneg _)).trans reach
  have funded:=(WilsonVacuumPreResetPeriodEntries.original simple hn B hs width blocks Z draw k).1
  have tail:=WilsonVacuumPreResetPeriodTail.long simple hn B hs reach blocks Z draw k D
  let omitted (t i:ℕ):Prop:=short B D A.reg i ∧ t≤depth n Z i
  have event:=Caddy.limits (A:=X) B omitted A.E funded (fun i _=>
    (eventually_gt_atTop (depth n Z i)).mono (fun t ht h=>(not_le_of_gt ht) h.2)) ep
  filter_upwards [event] with t ht
  let M:=model (n:=n) B σ C Z k D t
  have err:M.trunk-M.pioneers=(fun i=>if short B D A.reg i then 0 else A.E i)+
      (fun i=>if omitted t i then A.E i else 0):=by
    funext i
    change A.E i-submitted A (live B Z A D t) i=_
    simp only [submitted,live,mem_filter,before,Pi.add_apply,omitted]
    by_cases h:short B D A.reg i <;> by_cases le:depth n Z i<t <;>
      simp [h,le, show t≤depth n Z i ↔ ¬depth n Z i<t from not_lt.symm]
  refine ⟨funded,?_,?_,moves B σ C Z k D t⟩
  · convert Acquire.budget_cut (fun i=>i∈live B Z A D t) funded using 1 <;> first|rfl|skip
    funext i
    change submitted A (live B Z A D t) i=_
    by_cases e:i∈live B Z A D t <;> simp [submitted,e]
    rfl
  · change Meadow.Budget B A.reg (M.trunk-M.pioneers) (far+η)
    rw [err]
    apply Abacus.pay_bundle B tail
    convert ht using 1
    funext i
    by_cases e:omitted t i <;> simp [e]

end YM.Integration.WilsonVacuumPreResetPeriodCatalogue
