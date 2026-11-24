import YM.UVExt.CoerciveFlux

/-! The first and second directional responses have common limits when the incoming and test jets needed by the equation have common limits and a genuinely paid, strictly positive vertical Hessian on the slice. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Set Real Matrix Tensor
open scoped Topology ContDiff BigOperators Classical
variable {B F : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F]

-- bilinear helper, vertical directions need not span the full pair space

def eform (U : T (F×B) ℝ 2) (y z : B) := U ![(0,y),(0,z)]
private lemma first_smul {M : T (F×B) ℝ 2} (x : ℝ) (y z : F×B) : M ![x • y,z] = x * M ![y,z] := by change (M.curryLeft (x • y)) ![z] = x * ((M.curryLeft y) ![z]); rw [map_smul]; rfl
private lemma first_sub {M : T (F×B) ℝ 2} (x y z : F×B) : M ![x-y,z] = M ![x,z] - M ![y,z] := by change (M.curryLeft (x-y)) ![z] = M.curryLeft x ![z] - M.curryLeft y ![z]; rw [map_sub]; rfl
private lemma first_add {M : T (F×B) ℝ 2} (x y z : F×B) : M ![x+y,z] = M ![x,z] + M ![y,z] := by change (M.curryLeft (x+y)) ![z] = M.curryLeft x ![z] + M.curryLeft y ![z]; rw [map_add]; rfl
private lemma eform_linear {M : T (F×B) ℝ 2} (x : ℝ) (y z : B) : eform M (x • y) z = x * eform M y z := by
  unfold eform; rw [show ((0:F),x • y)=x • (0,y) from (Prod.smul_mk x (0:F) y).trans (by rw [smul_zero]) |>.symm,first_smul]
private lemma eform_sub {M : T (F×B) ℝ 2} (x y z : B) : eform M (x-y) z=eform M x z-eform M y z := by unfold eform; rw [show ((0:F),x-y)=(0,x)-(0,y) by rw [Prod.mk_sub_mk,sub_self],first_sub]

variable {S S' : ℕ→F×B→ℝ} {U : T (F×B) ℝ 2} {c : ℝ}

def clampedGap (S : ℕ→F×B→ℝ) (c : ℝ) := ∀ᶠ i in atTop, ∀ z, c*‖z‖^2 ≤ eform (spray S 2 i) z z
private lemma bill_ready {r : ℕ→B→ℝ} {R : B→ℝ} {x : ℕ→B} (hc : 0<c) (h : clampedGap S c) (hu : Tendsto (spray S 2) atTop (𝓝 U))
    (hr : ∀v, Tendsto (fun i=>r i v) atTop (𝓝 (R v))) (hZ : ∀ᶠ i in atTop, ∀ d,eform (spray S 2 i) (x i) d=r i d) :
    LineSolve (fun i => eform (spray S 2 i)) (eform U) r R x c :=
  { pos:=hc
    along:=fun {k} {z} {y} hk hy d=> by
      apply view_cont.continuousAt.tendsto.comp <| (hu.comp hk).prodMk_nhds (show Tendsto (fun j : ℕ=> (![⟨0,y j⟩, (0,d)] : Fin 2→F×B)) atTop (𝓝 ![(0,z), (0,d)]) from tendsto_pi_nhds.mpr fun i=> by
             fin_cases i
             · exact (tendsto_const_nhds (x:=(0:F))).prodMk_nhds hy
             exact tendsto_const_nhds (x:=((0:F),d)))
    right_side := hr
    subtraction := Eventually.of_forall fun _ x y z=> eform_sub x y z
    linearity := Eventually.of_forall fun _ x y z=> eform_linear x y z
    pays := h
    solves := hZ }

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ B] [CompleteSpace F] [CompleteSpace B]

lemma paired_rate (r : ℝ→B) (v : F) (h : ContDiffAt ℝ ∞ r 0) : deriv (paired v r) 0=(v,deriv r 0) := by
  convert tensor1 h v 1 using 1
  · rw [fish,iteratedDeriv_one]
  simp only [fish,iteratedDeriv_one,Prod.mk.injEq,and_true]; rw [show (fun t:ℝ=> t • v)= (fun t:ℝ=> id t • v) from rfl,deriv_smul_const (f:=v) differentiableAt_id]; simp
  
lemma paired_second (r : ℝ→B) (v : F) (h : ContDiffAt ℝ ω r 0) : fish 2 (paired v r)=(0,fish 2 r) := Prod.ext (by simpa only [show ¬(2:ℕ)=1 from by decide, ↓reduceIte] using tensor_word 2 h v) (by have hs := tensor1 (h.of_le le_top) v 2; exact (show (fish 2 (paired v r)).2=fish 2 r from congr_arg Prod.snd hs))
variable {a b : ℕ→ℝ→B} {v : F} (h : ∀ᶠ j : ℕ in atTop, Optimizes (S j) v (a j)) (h' : ∀ᶠ j : ℕ in atTop, Optimizes (S' j) v (b j))
include h in
lemma rate_bill (hc : 0 < c) (hV : clampedGap S c) (hu : Tendsto (spray S 2) atTop (𝓝 U)) :
    LineSolve (fun i => eform (spray S 2 i)) (eform U) (fun i d=>(-spray S 2 i) ![(v,0),(0,d)]) (fun d=>-U ![(v,0),(0,d)]) (fun i=>deriv (a i) 0) c := bill_ready hc hV hu (fun (d:B)=> (view_cont.continuousAt.tendsto.comp (hu.prodMk_nhds (tendsto_const_nhds (x:=(![(v,0),(0,d)] : Fin 2→F×B))))).neg) (h.mono fun i hi d=> by
        change _ = -(spray S 2 i ![_,_])
        refine eq_neg_of_add_eq_zero_right ((Eq.symm (first_add _ _ _)).trans (Eq.trans (show iteratedFDeriv _ _ _ 0 ![(v,0)+(0,deriv (a i) 0),(0,d)]=(spray S 2 i) ![deriv (paired v (a i)) (0:ℝ),(0,d)] from ?_) ((SolverRates hi).2 d).1)) -- replace wrong arity
        rw [paired_rate (a i) v (hi.analytic_pay.of_le le_top), Prod.mk_add_mk, add_zero, zero_add])

include h h'
lemma response_one {c c'} (h₁ : 0<c) (h₂ : 0<c') (ha : clampedGap S c) (hb : clampedGap S' c') (hh : Junction S S' 2) :
   ∃ z : B, Tendsto (fun i=>deriv (a i) 0) atTop (𝓝 z) ∧ Tendsto (fun i=>deriv (b i) 0) atTop (𝓝 z) := by
  obtain ⟨U,hw,hv⟩ := hh 2 le_rfl
  exact (rate_bill h h₁ ha hw).same_answer (rate_bill h' h₂ hb hv)
omit h'
lemma second_bill (hc : 0<c) (hV : clampedGap S c) (hu : Tendsto (spray S 2) atTop (𝓝 U)) {z : B} (ht : Tendsto (fun i=>deriv (a i) 0) atTop (𝓝 z))
    {V : B → T (F×B) ℝ 2} (hB : ∀ d, Tendsto (spray (fun i=>Analysis.D (0,d) (S i)) 2) atTop (𝓝 (V d))) :
   LineSolve (fun i=>eform (spray S 2 i)) (eform U) (fun i (d:B)=>-spray (fun i=>Analysis.D (0,d) (S i)) 2 i (fun _=>deriv (paired v (a i)) 0)) (fun d=> -V d (fun _=>(v,z))) (fun i=>fish 2 (a i)) c := by
  refine bill_ready hc hV hu (fun d=> ?_) (h.mono fun i hi d => ?_)
  · have hx : Tendsto (fun (i : ℕ) (_ : Fin 2)=> deriv (paired v (a i)) 0) atTop (𝓝 fun _=>(v,z)) := tendsto_pi_nhds.mpr fun _=> (tendsto_const_nhds.prodMk_nhds ht).congr' (h.mono fun j hj=> (paired_rate (a j) v (hj.analytic_pay.of_le le_top)).symm)
    exact (view_cont.continuousAt.tendsto.comp ((hB d).prodMk_nhds hx)).neg
  have hW := ((SolverRates hi).2 d).2; rw [paired_second (a i) v hi.analytic_pay] at hW
  exact eq_neg_of_add_eq_zero_right hW
include h'
lemma response_two {c c'} (h₁ : 0<c) (h₂ : 0<c') (ha : clampedGap S c) (hb : clampedGap S' c') (hh : Junction S S' 3) :
   ∃ z₂ : B, Tendsto (fun i=> fish 2 (a i)) atTop (𝓝 z₂) ∧ Tendsto (fun i=> fish 2 (b i)) atTop (𝓝 z₂) := by
  obtain ⟨z,hz,hy⟩ := response_one h h' h₁ h₂ ha hb (hh.mono (by omega))
  obtain ⟨U,hU,hU'⟩ := hh 2 (by decide)
  have hS : lucid S := h.mono fun i hi => hi.smooth.of_le le_top
  have hS' : lucid S' := h'.mono fun i hi => hi.smooth.of_le le_top
  choose V hV hV' using fun d : B=>hh.direction (q:=2) (0,d) hS hS' 2 le_rfl -- hh=q+1 ; rfl spurious
  exact (second_bill h h₁ ha hU hz hV).same_answer (second_bill h' h₂ hb hU' hy hV')

-- Through 3 or 4. Uniform positive price required for both sides at this fixed period. The transfer only consumes through-3 common jets (for k=4), not claiming through-4 common without a fit.
lemma critical_transfer {k} (hk : k=3 ∨ k=4) (hc : Junction S S' (k-1)) {c'} (ht : clampedGap S c) (oc : 0<c) (ht' : clampedGap S' c') (ot : 0<c') :
   ∃ X : ℕ→F×B, (∀ i≤k-2, Tendsto (fun j=>fish i (paired v (a j))) atTop (𝓝 (X i)) ∧ Tendsto (fun j=>fish i (paired v (b j))) atTop (𝓝 (X i))) ∧
    ∀ {A Q : T (F×B) ℝ k}, Tendsto (spray S k) atTop (𝓝 A) → Tendsto (spray S' k) atTop (𝓝 Q) →
     Tendsto (fun i=>fish k (S i ∘ paired v (a i)) - fish k (S' i ∘ paired v (b i))) atTop (𝓝 (Tensor.diagonal A (X 1)-Tensor.diagonal Q (X 1))) := by
  choose X hX hX' using show ∀ j: Fin (k-1), ∃ z, Tendsto (fun i=>fish j.val (paired v (a i))) atTop (𝓝 z) ∧ Tendsto (fun i=> fish j.val (paired v (b i))) atTop (𝓝 z) from by
    intro j; rcases lt_trichotomy j.val 1 with h0|h1|h2
    · have hj : j.val=0 := by omega
      exact ⟨0,tendsto_const_nhds.congr' (h.mono fun i hi=>by dsimp only []; simp only [hj,fish,iteratedDeriv_zero,pairAnchored _ _ hi.anchor]),
           tendsto_const_nhds.congr' (h'.mono fun i hi=>by dsimp only []; simp only [hj,fish,iteratedDeriv_zero,pairAnchored _ _ hi.anchor])⟩
    · obtain ⟨z,hu,hv⟩ := response_one h h' oc ot ht ht' (hc.mono (by omega)); exact ⟨(v,z),(tendsto_const_nhds.prodMk_nhds hu).congr' (h.mono fun i hi=>by dsimp only []; simp only [h1,fish,iteratedDeriv_one, paired_rate _ _ (hi.analytic_pay.of_le le_top)]), (tendsto_const_nhds.prodMk_nhds hv).congr' (h'.mono fun i hi=>by dsimp only []; simp only [h1,fish,iteratedDeriv_one,paired_rate _ _ (hi.analytic_pay.of_le le_top)])⟩
    have hj : j.val=2 := by omega
    obtain ⟨Y,hu,hv⟩ := response_two h h' oc ot ht ht' (hc.mono (by omega))
    exact ⟨(0,Y), (tendsto_const_nhds.prodMk_nhds hu).congr' (h.mono fun i hh=>by dsimp only []; rw [hj,paired_second _ _ hh.analytic_pay]), (tendsto_const_nhds.prodMk_nhds hv).congr' (h'.mono fun i hh=>by dsimp only []; rw [hj,paired_second _ _ hh.analytic_pay])⟩
  let X' j := if h:j<k-1 then X ⟨j,h⟩ else 0
  have cap j (hh) : Tendsto (fun i=>fish j (paired v (a i))) atTop (𝓝 (X ⟨j,hh⟩)) ∧ Tendsto (fun i=>fish j (paired v (b i))) atTop (𝓝 (X ⟨j,hh⟩)) := ⟨hX _,hX' _⟩
  refine ⟨X',?_,?_⟩
  · intro i hi; unfold X'; rw [dif_pos ?ih]; exact cap i _ -- fill name goal
    on_goal 1 => omega
  intro A Q hA hQ
  have hs {s : ℝ→B} {p : (F×B)→ℝ} {c : OrderedFinpartition k} (h : Optimizes p v s) (hc : ¬∀ i,c.partSize i≤k-2) : iteratedFDeriv ℝ c.length p 0 (fun u=>fish (c.partSize u) (paired v s))=0 := by
    push_neg at hc; obtain ⟨i,hi⟩ := hc
    exact silent_block c hk (fun q hq=> ((tensor_word q h.analytic_pay v).trans (if_neg (by omega)))) hi (h.smooth.of_le le_top) (SolverRates h).1 ((by simp only [fish,iteratedDeriv_one]; exact fun z=>((SolverRates h).2 z).1))
  refine faa_transfer hc (r:=k-2) (by omega) (h.mono fun i hi=>hi.smooth.of_le le_top) (h'.mono fun i hi=>hi.smooth.of_le le_top) (h.mono fun i hi=> (pairSmooth v hi.analytic_pay).of_le le_top) (h'.mono fun i hi=> (pairSmooth v hi.analytic_pay).of_le le_top) (h.mono fun i hi=> pairAnchored (a i) v hi.anchor) (h'.mono fun i hi=> pairAnchored (b i) v hi.anchor) (X:=X') hA hQ (fun i hi=> ?_) fun c hc=> ?_
  · unfold X'; rw [dif_pos (by omega: _<_ )]; exact cap _ _
  by_cases hx:∀ i,c.partSize i ≤ k-2
  · exact Or.inl hx
  right; filter_upwards [h,h'] with i h1 h2; unfold partitionVal; exact (hs (c:=c) h1 hx).trans (hs (c:=c) h2 hx).symm

end YM.UVExt.Paths
