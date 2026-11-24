import YM.Integration.WilsonRootedKioskOccupiedSlip
import YM.Integration.WilsonRootedKioskSoft

/-! The failed part and the former second-tap deposits share a single genuine
budget. All fields are tested after the original common envelope is selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskSlipCharge
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected Push.AbsoluteSums QuadraticLocal
open WilsonRootedKioskOccupiedSlip
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V T I J:Type}[DecidableEq V]{p:BudgetPoint}{o:V → Site n}{R:Census V}
variable {w:V → ℝ}{k a c d:ℝ}{B:ℕ}

theorem toll (hw:∀v,0<w v)(hk:1≤k){s:R.Mode}(hs:s≠R.quiet):
    Poly.toll (fun i=>w i/k) s ≤ k⁻¹*Poly.toll w s:=by
  have nonempty:0<s.val.card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (fun h=>hs (Subtype.ext h)))
  rw [mul_comm]
  unfold Poly.toll
  rw [prod_div_distrib, Finset.prod_const,←div_eq_mul_inv]
  gcongr
  · exact Finset.prod_nonneg fun v _=>(hw v).le
  nth_rw 1 [show k=k^1 from (pow_one k).symm]
  exact pow_le_pow_right₀ hk nonempty

theorem cost (L:Lamps T I G p o R)(hw:∀v,0<w v)(hk:1≤k)(held:Gross L w B a d):
    (sheet L).Budget (fun i=>w i/k) B a (k⁻¹*d):=by
  obtain ⟨f,fp,all,paid⟩:=held.before
  let y (i:I):=Poly.send (L.mode i) ((f i:ℝ):ℂ)
  have cap i: Poly.price (fun j=>w j/k) (y i) ≤ k⁻¹*(Poly.toll w (L.mode i)*f i):=by
    dsimp only [y];rw [Poly.solo,Complex.norm_real,Real.norm_of_nonneg (fp i),←mul_assoc]
    exact mul_le_mul_of_nonneg_right (toll hw hk (L.live i)) (fp i)
  refine ⟨y,fun i t U j=>?_,fun x=>?_⟩
  · change ‖(Poly.send _ _).part j‖ ≤ _ ∧ _
    dsimp only [y];simp only [Poly.part_send];split_ifs
    · exact ⟨(size L t i U).trans (all i t U),rfl⟩
    · simp
  have ip:0 ≤ k⁻¹:=inv_nonneg.mpr (zero_le_one.trans hk)
  apply budget_mono (WilsonRootedKioskSoft.scale ip paid x)
  · intro i
    by_cases incidence:x∈L.ground i
    · change 0 ≤ if x∈L.ground i then _ else _
      rw [if_pos incidence];exact mul_nonneg (Poly.nonnegative (fun j=>div_pos (hw j) (zero_lt_one.trans_le hk)) _) (Real.exp_pos _).le
    · change 0 ≤ if x∈L.ground i then _ else _
      rw [if_neg incidence]
  intro i
  change (if x∈L.ground i then _ else 0) ≤ (if x∈L.ground i then _ else 0)
  split
  · exact mul_le_mul_of_nonneg_right (cap i) (Real.exp_pos _).le
  · exact le_rfl

def roll (M:Canopy.ShiftRows T J G p o R)(L:Lamps T I G p o R):Canopy.ShiftRows T (J⊕I) G p o R where
  place:=Sum.elim M.place (sheet L).place
  soap t:=Sum.elim (M.soap t) ((sheet L).soap t)
  cost t i:=by cases i;exact M.cost t _;exact (sheet L).cost t _
  clean t i:=by cases i;exact M.clean t _;exact (sheet L).clean t _
  skip t i:=by cases i;exact M.skip t _;exact (sheet L).skip t _
  single t i:=by cases i;exact M.single t _;exact (sheet L).single t _

theorem stack (M:Canopy.ShiftRows T J G p o R)(L:Lamps T I G p o R)(old:M.Budget w B a c)(new:(sheet L).Budget w B a d):
    (roll M L).Budget w B a (c+d):=by
  obtain ⟨g,hg,gross⟩:=old.earned
  obtain ⟨f,hf,kiosk⟩:=new.earned
  let y:=Sum.elim g f
  refine ⟨y,fun i=>?_,fun x=>?_⟩
  · cases i;exact hg _;exact hf _
  let v (i:J⊕I):=if x∈((roll M L).place i).val then Poly.price w (y i)*Real.exp (a*coverNumber B ((roll M L).place i).val) else 0
  have l:SumBudget (v ∘ Sum.inl) c:=gross x
  have r:SumBudget (v ∘ Sum.inr) d:=kiosk x
  have both:=l.2.1.hasSum.sum (f:=v) r.2.1.hasSum
  refine ⟨?_,both.summable,both.tsum_eq.trans_le (add_le_add l.2.2 r.2.2)⟩
  intro i;cases i;exact l.1 _;exact r.1 _

theorem ordered (M:Canopy.ShiftRows T J G p o R)(L:Lamps T I G p o R)(t:T)(U:Config G n)
    (l:Summable (fun i=>M.soap t i U))(r:Summable (fun i=>(sheet L).soap t i U)):
    (roll M L).log t U=M.log t U+(sheet L).log t U:=
  (l.hasSum.sum (f:=fun i=>(roll M L).soap t i U) r.hasSum).tsum_eq

end YM.Integration.WilsonRootedKioskSlipCharge
