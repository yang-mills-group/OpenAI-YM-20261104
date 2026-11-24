import YM.Integration.WilsonMacroscopicRichFourierFiledScalar

/-! The complementary Fourier family stays on the original upper physical field.
Only the full source has to be booked. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSignedBookingSplit
open Function Filter Set MeasureTheory Lattice Wilson RG Source PhysicalNext.Repeat.Legato Trace.Physical.GermGraph RG16.Literal
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){N p h j:ℕ}
local notation "Upper"=>Config G (R.family.side N p)
local notation "B!"=>fun f=>Booked R.family N p h f j
local notation "A!"=>WilsonMacroscopicRichBookedReportMeter.sector R.family R.makes

theorem resolved {D K:Type*}[Fintype D](door:Opened R.family h j p)(live:j≤N)
    (P:(D→ℂ)→ₗ[ℂ]C(Upper,ℂ))(v:K→D→ℂ)(w:K→ℂ)(t:D→ℂ)
    (sum:HasSum (fun k=>w k•v k) t) (book: B! (P t) live) :
    let ok:=fun k=>B! (P (v k)) live
    ∃ g:D→ℂ,
      HasSum (fun k=>if ok k then w k•v k else 0) g ∧
      HasSum (fun k=>if ok k then 0 else w k•v k) (t-g) ∧
      B! (P g) live ∧ B! (P (t-g)) live ∧
      ∀ℓ:R.family.label h→ₗ[ℂ]ℂ,HasSum (fun k=>if ok k then w k*ℓ (topReport R.family N p h R.makes j door live (P (v k))) else 0)
        (ℓ (topReport R.family N p h R.makes j door live (P t))-ℓ (topReport R.family N p h R.makes j door live (P (t-g)))):=by
  intro ok
  let A:Submodule ℂ (D→ℂ):=(A! door live).comap P
  have good(k:K):ok k ↔ v k∈A:=Iff.rfl
  let f(k:K):D→ℂ:=if ok k then w k•v k else 0
  have inc(k:K):f k∈A:=by
    by_cases hk:ok k
    · simpa only [f,if_pos hk] using A.smul_mem (w k) ((good k).mp hk)
    · simpa only [f,if_neg hk] using A.zero_mem
  have hs:Summable f:=sum.summable.indicator {k|ok k}
  let g:=∑'k,f k
  have paid:HasSum f g:=hs.hasSum
  have gA:g∈A:=A.closed_of_finiteDimensional.mem_of_tendsto paid (Eventually.of_forall fun s=>A.sum_mem fun k _=>inc k)
  have tA:t∈A:=book
  have bad:B! (P (t-g)) live:=A.sub_mem tA gA
  have rest:HasSum (fun k=>if ok k then 0 else w k•v k) (t-g):=by
    have eq:(fun k=>if ok k then 0 else w k•v k)=(fun k=>w k•v k-f k):=by
      funext k;by_cases s:ok k <;> simp [f,s]
    rw [eq];exact sum.sub paid
  refine ⟨g,paid,rest,gA,bad,?_⟩
  obtain ⟨M,raw⟩:=WilsonMacroscopicRichBookedReportMeter.original R.family R.makes door live
  intro ℓ
  let L:(D→ℂ)→ₗ[ℂ]ℂ:=ℓ.comp (M.comp P)
  have signed:=paid.mapL L.toContinuousLinearMap
  have leg(k:K):L (f k)=(if ok k then w k*ℓ (topReport R.family N p h R.makes j door live (P (v k))) else 0):=by
    by_cases s:ok k
    · simp only [f,if_pos s,map_smul,L,LinearMap.comp_apply,raw (P (v k)) s,smul_eq_mul]
    · simp only [f,if_neg s,map_zero]
  have balance:L g=L t-L (t-g):=by rw [map_sub];abel
  have target:L g=ℓ (topReport R.family N p h R.makes j door live (P t))-ℓ (topReport R.family N p h R.makes j door live (P (t-g))):=by
    rw [balance];simp only [L,LinearMap.comp_apply,raw (P t) book,raw (P (t-g)) bad]
  change HasSum (fun k=>L (f k)) (L g) at signed
  simpa only [leg,target] using signed

end YM.Integration.WilsonMacroscopicRichSignedBookingSplit
