import YM.Integration.WilsonPhysicalExteriorRichFarFrame

/-! Coefficientwise inversion of the actual positive-horizon, finite R-rich
detector matrix at the manuscript's first cutoff.  The native archive
recurrence is applied on each original measured tree before division. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRichFarOrders
open Function Filter Set Finset Real MeasureTheory Lattice RG RG16 Pert Pert.Position
open XSpace FVA2 FVA2.Register MS MS.Land MS.Menus MS.Rake MS.Tone
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorRichFarGram
open WilsonPhysicalExteriorRichFarFrame FVA2.O.Read
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (Q:Prescription (Press.portDeck G)) (H:ℕ)
local notation "B₀" => Press.portDeck G
local notation "I" => Glyph B₀ H
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R

def weight (c':ℝ) (u:ℕ→ℝ) (z:Point):ℝ:=1+|u z.1+log (T₀ c' z.1)|
private theorem funded (c':ℝ) (u:ℕ→ℝ) (z:Point) : 1≤weight R c' u z:=by
  unfold weight;linarith only [abs_nonneg (u z.1+log (T₀ c' z.1))]

private def bills (c c':ℝ) (lo:ℕ→ℕ) (u:ℕ→ℝ) : Subring (Point→ℂ) where
  carrier:=fun f=>∃K:ℝ,0≤K ∧ ∃d:ℕ,∀ᶠ z in channel R c lo,‖f z‖≤K*(weight R c' u z)^d
  zero_mem':=⟨0,le_rfl,0,Eventually.of_forall fun _=>by simp⟩
  one_mem':=⟨1,zero_le_one,0,Eventually.of_forall fun _=>by simp⟩
  neg_mem':=by
    rintro f ⟨K,hK,d,h⟩
    exact ⟨K,hK,d,h.mono fun z hz=>by simpa only [Pi.neg_apply,norm_neg] using hz⟩
  add_mem':=by
    rintro f p ⟨A,hA,i,hf⟩ ⟨B,hB,j,hp⟩
    refine ⟨A+B,add_nonneg hA hB,max i j,?_⟩
    filter_upwards [hf,hp] with z h₁ h₂
    change ‖f z+p z‖≤_
    rw [add_mul]
    exact (norm_add_le ..).trans (add_le_add
      (h₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (funded R c' u z) (le_max_left i j)) hA))
      (h₂.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (funded R c' u z) (le_max_right i j)) hB)))
  mul_mem':=by
    rintro f p ⟨A,hA,i,hf⟩ ⟨B,hB,j,hp⟩
    refine ⟨A*B,mul_nonneg hA hB,i+j,?_⟩
    filter_upwards [hf,hp] with z h₁ h₂
    change ‖f z*p z‖≤_
    rw [norm_mul,pow_add,mul_mul_mul_comm]
    exact mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg hA (pow_nonneg (zero_le_one.trans (funded R c' u z)) _))

private theorem constant (c c':ℝ) (lo:ℕ→ℕ)(u:ℕ→ℝ)(x:ℂ) :
    (fun _:Point=>x)∈bills R c c' lo u:=
  ⟨‖x‖,norm_nonneg _,0,Eventually.of_forall fun _=>by simp⟩

private theorem evaluation (c c':ℝ) (lo:ℕ→ℕ)(u:ℕ→ℝ) (P:Polynomial ℂ) :
    (fun z:Point=>P.eval ((u z.1+log (T₀ c' z.1):ℝ):ℂ))∈bills R c c' lo u:=by
  let fee:=bills R c c' lo u
  have clock:(fun z:Point=>((u z.1+log (T₀ c' z.1):ℝ):ℂ))∈fee:=by
    refine ⟨1,zero_le_one,1,Eventually.of_forall fun z=>?_⟩
    simp only [Complex.norm_real,Real.norm_eq_abs,weight,pow_one,one_mul]
    linarith
  induction P using Polynomial.induction_on' with
  | add P D hp hd =>
    simp only [Polynomial.eval_add];exact fee.add_mem hp hd
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact fee.mul_mem (constant R c c' lo u a) (fee.pow_mem clock n)

private theorem sums {α:Type*} (c c':ℝ) (lo:ℕ→ℕ)(u:ℕ→ℝ) (s:Finset α)(f:α→Point→ℂ)
    (h:∀a∈s,f a∈bills R c c' lo u) :
    (fun z:Point=>∑a∈s,f a z)∈bills R c c' lo u:=by
  have z:=Subring.sum_mem (bills R c c' lo u) h
  have e:(∑a∈s,f a)=(fun z:Point=>∑a∈s,f a z):=by funext x;exact Finset.sum_apply ..
  exact e ▸ z

private theorem exactFee (c c':ℝ)(lo:ℕ→ℕ)(u:ℕ→ℝ){f p:Point→ℂ}
    (h:f=ᶠ[channel R c lo]p)(hp:p∈bills R c c' lo u) : f∈bills R c c' lo u:=by
  obtain ⟨K,hK,d,hp⟩:=hp
  exact ⟨K,hK,d,(h.and hp).mono fun z hz=>by simpa only [hz.1] using hz.2⟩

/-- The unscaled inverse series on the actual R/Q finite Gram matrix, not the
inverse of the independently chosen limiting field table.  After the true
deposition/continuum error all orders of every entry have only polynomial
cost in the actual subtraction log. -/
theorem coefficients {hG:G.Simple} (N:WilsonPrescription G) {S:Prescription B₀} {dial:Bool}
    (issued:Main.Match N hG M S dial) (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (g:Test 2) (good:∀z,(g z).im=0 ∧ 0≤(g z).re) (pop:Nonempty (tsupport g))
    (nondeg:IsUnit (MSSeparatedTestGram.matrix M H 0 0 g))
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (μ:ℝ) (side:Bool) (u:ℕ→ℝ) (take:∀j,u j=μ ∨ u j=μ+R.family.S.scale j)
    (k:ℕ)(a b:I) :
    ∃K:ℝ,0≤K ∧ ∃d:ℕ,∀ᶠ z in channel R c lo,
      ‖Slate.slice k (series R Q H g c c' side u z)⁻¹ a b‖≤K*(weight R c' u z)^d:=by
  let A:=series R Q H g c c' side u
  let fee:=bills R c c' lo u
  let V:Warehouse G:=⟨R.family.labels,R.family.params,R.family.localSection,R.makes.sections,fun d=>Next.Foundations.valuation G d⟩
  have incoming (j:ℕ)(v w:I):(fun z=>Slate.slice j (A z) v w)∈fee:=by
    let m:=fun z:Point=>MSSeparatedTestGram.matrix M H (u z.1+log (T₀ c' z.1)) j g v w
    have saved:(fun z:Point=>m z)∈fee:=by
      have hs:=evaluation R c c' lo u (WilsonPhysicalExteriorSmoothGram.row M H g j v w)
      simpa only [m,WilsonPhysicalExteriorSmoothGram.evaluated_row V M H g] using hs
    have step:=WilsonPhysicalExteriorRichFarGram.measured R M Q H N issued rows g good pop slow h₁ h₂ h₃ lo μ 0 j 0
    have err:(fun z:Point=>Slate.slice j (A z) v w-m z)∈fee:=by
      refine ⟨1,zero_le_one,0,?_⟩
      rw [channel,eventually_inf_principal]
      filter_upwards [(tendsto_comap:Tendsto (Prod.fst:Point→ℕ) (comap Prod.fst atTop) atTop).eventually step] with z fe hd
      have hit:=fe side z.2 hd v w
      dsimp only [m,A]
      rw [WilsonPhysicalExteriorRichFarFrame.slice]
      rcases take z.1 with hx|hx <;> rw [hx]
      · simpa only [pow_zero,one_mul,neg_zero,zero_mul,exp_zero] using hit.1
      · simpa only [pow_zero,one_mul,neg_zero,zero_mul,exp_zero] using hit.2
    have h:=fee.add_mem err saved
    have e:((fun z=>Slate.slice j (A z) v w-m z)+(fun z=>m z))=(fun z=>Slate.slice j (A z) v w):=by
      funext z;exact sub_add_cancel ..
    exact e ▸ h
  obtain ⟨B,hB,later⟩:=tree R M Q H N issued rows g good pop nondeg slow h₁ h₂ h₃ lo μ side u take
  have seed (v w:I):(fun z:Point=>(Slate.slice 0 (A z))⁻¹ v w)∈fee:=
    ⟨B,hB,0,later.mono fun z hz=>by simpa only [pow_zero,mul_one] using hz.2 v w⟩
  change (fun z=>Slate.slice k (A z)⁻¹ a b)∈fee
  induction k using Nat.strong_induction_on generalizing a b with
  | h k ih =>
    let term:=fun (v:I)(z:Point)=>
      (Slate.slice k (1:Matrix I I (PowerSeries ℂ)) a v-
        ∑t∈range k,∑w:I,Slate.slice t (A z)⁻¹ a w*Slate.slice (k-t) (A z) w v)*
        (Slate.slice 0 (A z))⁻¹ v b
    apply exactFee R c c' lo u (p:=fun z=>∑v:I,term v z)
    · filter_upwards [later] with z hd
      have native:=congrFun (congrFun (Slate.inv_eq (n:=k) hd.1 (T:=A z) rfl) a) b
      simpa only [term,Matrix.mul_apply,Matrix.sub_apply,Matrix.sum_apply] using native
    · apply sums R c c' lo u univ term
      intro v _
      apply fee.mul_mem _ (seed v b)
      apply fee.sub_mem (constant R c c' lo u _) _
      apply sums R c c' lo u (range k) _
      intro t ht
      apply sums R c c' lo u univ _
      intro w _
      exact fee.mul_mem (ih t (Finset.mem_range.mp ht) a w) (incoming (k-t) w v)

end YM.Integration.WilsonPhysicalExteriorRichFarOrders
end
