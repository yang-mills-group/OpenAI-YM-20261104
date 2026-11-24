import YM.FormalBulk08.Flat.Supply

/-! The actual stationary repeat maps on every occupied slot, with the exponential length of each new line. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakKernel
open Function Finset Lattice Laurent Bloch Precision FormalBulk08 Flat RG Next.Free UVExtension.Free Work.F08
open scoped BigOperators Classical

variable {I J:Type*} [Fintype J]

def cash (_A:Bloch.Row I J) (b:ℝ):ℝ:=(Fintype.card J:ℝ)*b

def parcel (A:Bloch.Row I J)(σ:ℝ)(x:I)(w:Cover×J):ℝ:=
  Real.exp (σ*size w.1)*‖A x w.2 w.1‖

theorem bond (A:Bloch.Row I J) {σ b:ℝ}(h:A.strip σ b) (x:I)(box:Finset Cover) :
    ∑w∈(box ×ˢ (univ:Finset J)),parcel A σ x w≤cash A b:=by
  rw [sum_product_right]
  have price (y:J):∑t∈box,Real.exp (σ*size t)*‖A x y t‖≤b:=
    ((h x y).2.1.sum_le_tsum box (fun a _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).trans (h x y).2.2
  calc _≤∑_:J,b:=sum_le_sum fun y _=>price y
       _=_:=by simp [cash]

def fare (A:Bloch.Row I J)(σ:ℝ){r:ℕ}(keys:Fin r→I)(boxes:Fin r→Finset Cover) : ℝ:=
  ∑x∈Fintype.piFinset (fun a=>(boxes a) ×ˢ (univ:Finset J)),∏a:Fin r,parcel A σ (keys a) (x a)

theorem tableau (A:Bloch.Row I J) {σ b:ℝ}(h:A.strip σ b) {r:ℕ}
    (keys:Fin r→I)(boxes:Fin r→Finset Cover) : fare A σ keys boxes≤(cash A b)^r:=by
  rw [fare,←prod_univ_sum]
  calc _≤∏_:Fin r,cash A b:=by
         apply prod_le_prod
         · intro a _; exact sum_nonneg fun w _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
         · intro a _;exact bond A h (keys a) (boxes a)
       _=_:=by simp

theorem original (G:Gauge) (k:ℝ) (hk:0<k) {j t:ℕ}(hj:4≤j)(ht:4≤t) :
    ∃σ b:ℝ,0<σ ∧ 0<b ∧ ∀P:Flight j t,∀l:List Axis,l.length≤j-2→
      let A:=advanceC P.L (Flight.duo k P).A0 l
      let M:=advanceC P.L (Flight.duo k P).T l
      ∀s:ℝ,s≤σ→∀r:ℕ,(∀keys:Fin r→_,∀boxes:Fin r→Finset Cover,
        fare A s keys boxes≤(cash A (b/(P.L.val:ℝ)^(1+l.length)))^r) ∧
        (∀keys:Fin r→_,∀boxes:Fin r→Finset Cover,
        fare M s keys boxes≤(cash M (b/(P.L.val:ℝ)^(2+l.length)))^r):=by
  obtain ⟨σ,b,sp,bp,live,-⟩:=Flat.transports G k hk hj ht
  refine ⟨σ,b,sp,bp,?_⟩
  intro P l hl
  dsimp only
  intro s hs r
  obtain ⟨left,right⟩:=live P l hl
  exact ⟨fun keys box=>tableau _ (strip_mono left hs le_rfl) keys box,
         fun keys box=>tableau _ (strip_mono right hs le_rfl) keys box⟩

end YM.Integration.WilsonThermometerUnitFilingWeakKernel
