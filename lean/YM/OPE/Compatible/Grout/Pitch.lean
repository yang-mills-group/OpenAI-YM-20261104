import YM.OPE.Compatible.Grout.Film
/-!
# Facial Sable in any width. Exponential case.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma.Sable
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {X: Support f}{u v:Config G f→ℝ}
lemma solitary (h:Paced R X S u a):Sable R S X r u a:=by
    refine ⟨Unit,inferInstance,fun _=> u,fun _=>0,fun _=>a,fun _=>prepay h, ?_,fun i=>?_⟩; · simp only [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul]; exact ⟨fun _=>h.safe,.of_finite,by rw [tsum_fintype,Fintype.sum_unique]⟩
    simpa only [Fintype.sum_unique] using (hasSum_fintype (fun _:Unit=>u i))
lemma multiplication (h:Sable R S X r u a)(hv:Sable R S X r v σ)(_hh:0≤r):Sable R S X r (u*v) (a*σ):=by
    obtain ⟨I,hI,J,m,k,h,hw,hc⟩:=h; obtain ⟨W,hW,N,n,g,hY,ha,hH⟩:=hv
    have hp (i):= J i; clear hp
    refine ⟨I×W,inferInstance,fun i=> J i.1*N i.2,fun i=>m i.1+n i.2,fun i=> k i.1*g i.2,fun i=> (h i.1).product (hY i.2),?_,fun V=> ?_⟩
    · convert! Push.AbsoluteSums.budget_prod hw ha using 1; ext i; simp only [Nat.cast_add,mul_add,Real.exp_add]; ring
    have h_1:= (hc V); have h_2:= hH V
    have hs:=Summable.of_norm ((h_1.summable.norm.mul_of_nonneg h_2.summable.norm (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)).congr (g:= fun i:I×W=> ‖(J i.1*N i.2) V‖) (fun _=> by simp))
    exact h_1.mul h_2 hs
lemma scale (h:Sable R S X r u a) (s:ℝ):Sable R S X r (s • u) (‖s‖*a):=by
   obtain ⟨I,hI,J,m,k,h,hw,hc⟩:=h; refine ⟨I,hI,fun i=> s • J i,m,fun i=> ‖s‖*k i,fun i=>(h i).smul,?_,fun i=>(hc i).mul_left _⟩; convert budget_scale (norm_nonneg s) hw using 1; ext i; rw [mul_left_comm]
private lemma sumSide {α β:Type}{f:α→ℝ}{g:β→ℝ}(h:HasSum f a)(hp:HasSum g r): HasSum (Sum.elim f g) (a+r):=by
    have hf{A B:Type} (g:A→ℝ)(p:ℝ)(hx:HasSum g p): HasSum (Sum.elim g (fun _:B=> (0:ℝ))) p:= by
       refine ((Sum.inl_injective).hasSum_iff (fun j hj=>?_)).1 hx
       cases j; next i=> exact (hj ⟨i,rfl⟩).elim
       rfl
    have hg:= (hf f a h).add ((Equiv.sumComm α β).hasSum_iff.mpr (hf g r hp)) -- mp? equiv.hasSum_iff : sum(f∘e) ?
    exact hg.congr_fun (fun i=>by cases i<;>simp)
lemma addition (h:Sable R S X r u a)(hv:Sable R S X r v σ)(_hh:0≤r):Sable R S X r (u+v) (a+σ):=by
    obtain ⟨I,hI,J,m,k,h,hw,hc⟩:=h; obtain ⟨W,hW,N,n,g,hY,ha,hH⟩:=hv
    refine ⟨I⊕W,inferInstance,Sum.elim J N,Sum.elim m n,Sum.elim k g,fun i=>Sum.rec (motive:=fun i=>PaidY R S X _ _ _) ?_ ?_ i,?_,?_⟩
    · exact h
    · exact hY
    · -- HasSum.sum.elim
      let f i:= Real.exp (r*m i)*k i; let g' i:= Real.exp (r*n i)*g i
      have ht := sumSide hw.2.1.hasSum ha.2.1.hasSum
      have hh (i:I⊕W) : Real.exp (r * ((m ⊕ᵥ n) i : ℕ)) * ((k ⊕ᵥ g) i) = Sum.elim f g' i:=Sum.rec (fun _=>rfl) (fun _=>rfl) i
      simp_rw [hh]; refine ⟨fun i=>?_,ht.summable,ht.tsum_eq.trans_le (add_le_add hw.2.2 ha.2.2)⟩; rcases i with i|i; exact hw.1 i;exact ha.1 i
    intro i; exact (sumSide (hc i) (hH i)).congr_fun (fun x=>by cases x<;> rfl)
lemma powers (h:Sable R S X r u a)(hh:0≤r)(n:ℕ): Sable R S X r (u^n) (a^n):=by
   induction n with
   | zero=> simp only [pow_zero]; exact solitary ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _ _=>rfl,fun u=> norm_one.le⟩
   | succ n ih=> simp only [pow_succ]; exact ih.multiplication h hh
-- sum assembler
lemma growing {f':ℕ→Config G f→ℝ}{k:ℕ→ℝ}{g:Config G f→ℝ} (hh:∀ i,Sable R S X r (f' i) (k i))(hp: SumBudget k a) (hk: ∀ U,HasSum (fun i=>f' i U) (g U))(hl:0≤r):Sable R S X r g a:=by
   choose I hI J m w h hw he using hh
   have ht(s:Σ i,I i):0≤Real.exp (r * m s.1 s.2)* w s.1 s.2:= (hw s.1).1 s.2
   have hq:=hp.2.1.of_nonneg_of_le (fun i=>tsum_nonneg (hw i).1) (fun i=>(hw i).2.2)
   have hx : Summable (fun s:Σ i,I i=> Real.exp (r * m s.1 s.2)* w s.1 s.2):= (summable_sigma_of_nonneg ht).2 ⟨fun i=>(hw i).2.1,hq⟩
   have hv:SumBudget _ a:= ⟨ht,hx,hx.tsum_sigma.trans_le ((hq.tsum_le_tsum (fun i=>(hw i).2.2) hp.2.1).trans hp.2.2)⟩
   haveI : Countable (Σ i,I i):= by letI:=hI; infer_instance
   let g₀(s:Σ i,I i):= J s.1 s.2; have hs := fine (fun s:Σ i,I i=> h s.1 s.2) hv hl
   refine ⟨Σ i,I i,inferInstance,g₀,fun s=>m s.1 s.2,fun s=>w s.1 s.2,fun s=> h s.1 s.2,hv,fun i=>(hk i).sigma_of_hasSum  (fun p=>he p i) (Summable.of_norm ?_)⟩
   exact hs.2.1.of_nonneg_of_le (fun _=> norm_nonneg _) (fun s=> (h s.1 s.2).cash i)
lemma expo (h:Sable R S X r u a)(hh:0≤r):Sable R S X r (fun U=>Real.exp (u U)) (Real.exp a):=by
   have hv:0≤a:= (norm_nonneg _).trans ((h.present hh).2 1); let K(i:ℕ):= (i.factorial:ℝ)⁻¹; have hK i:‖K i‖=K i:=Real.norm_of_nonneg (by unfold K; positivity)
   have hk(t:ℝ): HasSum (fun i:ℕ=> K i*t^i) (Real.exp t):=by simpa only [K,mul_comm _ (t^_), ← div_eq_mul_inv,Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div] using! (Real.summable_pow_div_factorial t).hasSum
   refine growing (k:=fun i=>K i*a^i) (f':=fun i=> K i • u^i) (fun i=>by have he:=(h.powers hh i).scale (K i); rw [hK] at he; exact he) ⟨fun i=> by unfold K; positivity,(hk a).summable,(hk a).tsum_eq.le⟩ (fun U=> (hk (u U)).congr_fun fun i=>by simp) hh
end YM.PhysicalNext.Repeat.Aroma.Sable
