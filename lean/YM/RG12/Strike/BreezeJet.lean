import YM.RG12.Strike.Lengths
import YM.Contact.Trial
/-!
# Pulling exact local predifferentiated Taylor mark symbols

Continuum Euclidean displacement `w` after translating mark to pole x=0;
we clip smooth ext potentials *at the pole* prior to applying any Trial costs.
Taylor layers through `range n` (EMPTY subtraction takes `n=0`, no zeroth term!).
Keep separated from A-formal and from `Strike.clean` analytic & harmonic conditions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical Distributions
variable (f:R→ℂ) (x:R)(n:ℕ)
lemma read_tape {f:R→ℂ}{S:Set R} (hs:IsOpen S)(hf:silk S f){x:R} (hx:x∈S)(n:ℕ)(p:Strip n) : barrage f (List.ofFn p) x = iteratedFDeriv ℝ n f x (bar ∘ p) := by
   induction n generalizing x with
   | zero=>rfl -- List.ofFn zero
   | succ n he=>
      rw [List.ofFn_succ,barrage]; let q:Strip n:=Fin.tail p
      let v:=bar ∘ p; let A:=iteratedFDeriv ℝ n f
      have hd(x)(hx:x∈S):DifferentiableAt ℝ A x:= (hf _ hx).differentiableAt_iteratedFDeriv (WithTop.coe_lt_top _)
      have hh(y)(hy:y∈S):barrage f (List.ofFn q) y=(fun s:R=>A s (Fin.tail v)) y := he hy q
      change hit _ (barrage f (List.ofFn q)) x= _
      rw [in_turn hs hx _ hh,along _]; swap
      · exact (hd x hx).continuousMultilinear_apply_const _
      exact ((hd x hx).iteratedFDeriv_succ_apply_left').symm
lemma on_wind {f:R→ℂ}{S:Set R} (hs:IsOpen S)(hf:silk S f){x:R} (hx:x∈S)(n:ℕ)(v:R):
   iteratedFDeriv ℝ n f x (fun _=>v)=fall (gauge n (fun p=>barrage f p x)) v := by
   have hV: ∑ i:Axis4, v i • bar i=v:=by
      simp_rw [←project v]
      exact (EuclideanSpace.basisFun Axis4 ℝ).sum_repr' _
   let A:=(iteratedFDeriv ℝ n f x).toMultilinearMap
   change A (fun _=>v)=_
   rw [show (fun _:Fin n=>v)=fun _:Fin n=>∑ i:Axis4,v i • bar i from funext fun _=>hV.symm]
   rw [show A (fun _:Fin n=>∑ i:Axis4,_)=∑ i:Strip n,A (fun j=> v (i j) • bar (i j)) from A.map_sum (fun _ i => v (i:Axis4) • bar i)]
   apply Finset.sum_congr rfl
   intro i _
   rw [A.map_smul_univ (fun j=>v (i j)) (fun j=>bar (i j))] -- syntax match
   change _ • iteratedFDeriv ℝ n f x (bar ∘ i) = gauge _ _ _ * _
   rw [Complex.real_smul, Complex.ofReal_prod, ←read_tape hs hf hx n i,mul_comm]; rfl
-- derivative at x in all directions v with ordinary factorial
noncomputable def fresco (n:ℕ)(f:R→ℂ)(x:R):R→ℂ:=fun y => ((n.factorial:ℕ):ℂ)⁻¹ * fall (gauge n (fun p=>barrage f p x)) y
lemma exposed {S:Set R} (h:IsOpen S)(he:silk S f){x:R} (hx:x∈S)(y:R): YM.Contacts.jet n f x y=fresco n f x (y-x):=by
   unfold YM.Contacts.jet fresco; rw [on_wind h he hx,Complex.real_smul,Complex.ofReal_inv, Complex.ofReal_natCast]
lemma fresco_cont : Continuous (fresco n f x) := continuous_const.mul (fall_cont _)
noncomputable def rainJet (n:ℕ)(f:R→ℂ)(x y:R):ℂ:=∑ i∈Finset.range n,fresco i f x y
lemma chart_cont : Continuous (rainJet n f x) := continuous_finsetSum _ (fun _ _=>fresco_cont ..)
-- local Trial price where analytic. prove by extending on a fixed open ball
lemma leaf {S:Set R} (h:IsOpen S)(he:silk S f)(hz:(0:R)∈S):∃ φ:YM.Contacts.Trial R,⇑φ=ᶠ[𝓝 0] f:=by
   obtain ⟨t,ht,hT⟩:= Metric.isOpen_iff.mp h 0 hz
   have hh:0<t/4:=by linarith
   let A:=YM.Contacts.chi (E:=R) (t/4)
   let g(x:R):ℂ:=A x • f x
   have hA: tsupport A ⊆ Metric.closedBall (0:R) (t/2):=(YM.Contacts.chi_supported _ hh).trans (Metric.closedBall_subset_closedBall (by linarith))
   have hv: tsupport A ⊆ S:=Subset.trans hA (Subset.trans (Metric.closedBall_subset_ball (by linarith: t/2<t)) hT)
   have hg:HasCompactSupport g:= (YM.Contacts.chi_compact _ hh).smul_right 
   have hh':ContDiff ℝ (⊤:ℕ∞) g:=contDiff_iff_contDiffAt.mpr (fun x=>by
     by_cases hx:x∈S
     · exact (YM.Contacts.chi_smooth _).contDiffAt.smul ((he x hx).of_le le_top)
     have ht : x∉tsupport A:=fun q=> hx (hv q)
     have hf:= notMem_tsupport_iff_eventuallyEq.mp ht
     apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
     filter_upwards [hf] with y hy
     change A y • f y=_; change A y=0 at hy; rw [hy,zero_smul] )
   refine ⟨⟨g,hh', hg,subset_univ _⟩,?_⟩
   filter_upwards [Metric.closedBall_mem_nhds 0 hh] with i hi
   change A i • f i = _;rw [show A i=1 from YM.Contacts.chi_one hh _ (by simpa only [mem_closedBall_iff_norm,sub_zero] using hi)]; simp -- unfold g
-- local Taylor remainder at dead center; size constant not uniform in other marked points.
lemma tower {S:Set R} (hs:IsOpen S)(hf:silk S f)(hz:(0:R)∈S):∃ B:ℝ,0 ≤ B ∧ ∀ᶠ y:R in 𝓝 0,‖f y-rainJet n f 0 y‖ ≤ ‖y‖^n*B:=by
   obtain ⟨φ,H⟩:=leaf f hs hf hz
   obtain ⟨B,hB⟩:= YM.Contacts.Trial.majorant n φ
   refine ⟨B,hB.nonneg,H.mono fun y hy=>?_⟩
   cases n with
   | zero=>simpa only [rainJet,Finset.range_zero,sum_empty,sub_zero,pow_zero,one_mul,←hy] using! hB.value y
   | succ n=>
     have hm := YM.Contacts.taylor_est hB (0:R) y
     have he(i:ℕ): YM.Contacts.jet i φ 0 y=fresco i f 0 y:=by
       rw [← sub_zero y, ←exposed f i hs hf hz] -- target change
       unfold YM.Contacts.jet; rw [(Filter.EventuallyEq.iteratedFDeriv ℝ H i).eq_of_nhds]; simp
     unfold YM.Contacts.polynomial at hm; simp_rw [he] at hm; rwa [hy,sub_zero] at hm
end YM.RG12.Strike
