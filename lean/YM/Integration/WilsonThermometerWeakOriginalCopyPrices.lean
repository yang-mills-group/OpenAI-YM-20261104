import YM.Integration.WilsonThermometerWeakOriginalReclosure

/-! Receiving tariffs on all reflected copies of the same filed Wilson field, with one
support reserve for each actually occupied root and no charge proportional to the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakOriginalCopyPrices
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Configuration Rise
open Thirst Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V:Type} [Fintype V] [DecidableEq V] {ζ:V→Site n}

theorem short (q:BudgetPoint) (e:ℝ) (w:V→ℝ) {s:V→Signed} {Z:Support n}
    (error:V→SourceAt G ζ) (forced:V→Strike G ζ q.threshold) (hz:Injective ζ)
    (X:∀ i,(error i).extent=swath (s i) (ζ i) Z) (f:∀ i,(error i).fires=slot i)
    (X':∀ i,(forced i).extent=halo 8 (swath (s i) (ζ i) Z)) (f':∀ i,(forced i).fires=slot i)
    {c h:V→ℝ} {δ K:ℝ} (small:∀ i,transported (error i) q.threshold w (c i))
    (cap:∀ i,Taxed (forced i) (q:=q) w (h i)) (ds:∀ i,c i≤δ) (hc:∀ i,h i≤K) (hK:0≤K):
    Unpacks error q w e (δ*debt q.B e Z) ∧
    taxable (q:=q) forced w e (wilt q.B*(K*debt q.B (e+1) (halo 8 Z))) := by
  constructor
  · have cost i:debt q.B e (error i).extent=debt q.B e Z:=by rw [X,debt,swath_cover];rfl
    refine ⟨c,small,shorten (A:=fun i=>(error i).fires) _ f (fun i=>?_) (fun i=>(small i).1)⟩
    rw [cost];exact mul_le_mul_of_nonneg_right (ds i) (Real.exp_pos _).le
  have priced i:debt q.B (e+1) (forced i).extent=debt q.B (e+1) (halo 8 Z):=by
    rw [X',←swath_iffHalo,debt,swath_cover];rfl
  have hf i:(forced i).fires.val.Nonempty:=by rw [f'];exact Finset.singleton_nonempty _
  have ht:stars q (fun i=>(forced i).fires) (fun i=>(forced i).extent) (e+1) h (K*debt q.B (e+1) (halo 8 Z)):=by
    refine shorten _ f' (fun i=>?_) (fun i=>(cap i).1)
    rw [priced];exact mul_le_mul_of_nonneg_right (hc i) (Real.exp_pos _).le
  exact ⟨h,cap,roots_hits _ _ _ hz hf (fun i=>(forced i).remembers) (fun i=>(cap i).1)
    (mul_nonneg hK (Real.exp_pos _).le) ht⟩

theorem wide (p q:BudgetPoint) (w:V→ℝ) (e ceiling:ℝ) (far:V→Keepat n→SourceAt G ζ) {c:V→Keepat n→ℝ}
    (area:∀ i j,transported (far i j) p.threshold w (c i j))
    (rent:∀ i,(∑ j,c i j*debt q.B e (halo 8 (far i j).extent))≤ceiling)
    (slotEq:∀ i j,(far i j).fires=slot i):
    Credit (fun j:V×Keepat n=>far j.1 j.2) p q w e ceiling := by
  let F (j:V×Keepat n):=far j.1 j.2
  let C (j:V×Keepat n):=c j.1 j.2
  have bill j:transported (F j) p.threshold w (C j):=area _ _
  refine ⟨C,bill,fun x=>?_⟩;apply (sum_pay ..).2
  · rw [Fintype.sum_prod_type,Finset.sum_eq_single x]
    · have h j:x∈(far x j).fires.val:=by rw [slotEq];exact Finset.mem_singleton_self _
      simp only [h,↓reduceIte];exact rent x
    · intro i _ h;apply Finset.sum_eq_zero;intro j _;apply if_neg
      intro incorrect;change x∈(far i j).fires.val at incorrect;rw [slotEq] at incorrect
      exact h (Finset.mem_singleton.mp incorrect).symm
    simp
  exact fun i=>mul_nonneg (bill i).1 (Real.exp_pos _).le

end YM.Integration.WilsonThermometerWeakOriginalCopyPrices
end
