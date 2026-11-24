import YM.SchemeConversionRG11.FirstW.Trice.Grail
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical
variable {T:Itinerary}{c:ℕ→Side}{n:Side}{G:Gauge}{x:Nodes}{W:Wash}{R ρ r :ℝ} (g:P→Badge G){s:P→StepPath T}(h:Box x R ρ)(hs:∀ i,sails T (s i) (x i))
abbrev firstK (g:P→Badge G)(T:Itinerary)(s:P→StepPath T)(i:P):= Laurel (g i) (glow i) T (s i)
local notation "Λ" => firstK g T s
def singleQ (g:P→Badge G)(m:P)(i j a b:Axis)(x:Nodes)(R ρ:ℝ):ℂ:= Triad.prime (fun i=>(g i).1) x R ρ m j a b i 0 - Triad.prime (fun i=>(g i).1) x R ρ m j b a i 0
abbrev colC (g:P→Badge G):ℂ:=↑(colorF (g 0).2 (g 1).2 (g 2).2)
include h hs
lemma believed (W:Wash)(hw:W.rOut<r)(ht:∀ i j:Fin 3,i≠j → r<‖x i-x j‖)(m:P)(i j a b:Axis)(hc:MarkGrid T c):
 Tendsto (fun k=> (↑(MinusUnit T (ack T (Λ m) (Λ (foreL m)) (Λ (aft m)) i j a b) k):ℂ)) atTop (𝓝 (colC g*singleQ g m i j a b x R ρ)):= by
 have HP := ack_all (A₀:=g m) (B₀:=g (foreL m)) (C₀:=g (aft m)) (u₁:=glow m) (u₂:=glow (foreL m)) (u₃:=glow (aft m)) W hw (hs m) (hs (foreL m)) (hs (aft m)) (ht _ _ (Triad.neg1 _)) (ht _ _ (Triad.neg2 _)) (ht _ _ (Triad.neg3 _)) hc i j a b
 have he := star_soft g m i j a b h hw ht; change _=colC g*singleQ g m i j a b x R ρ at he; rw [← he]; exact continuous_ofReal.continuousAt.tendsto.comp HP
omit h hs in
lemma pass_face (g:P→Badge G)(x:Nodes)(R ρ:ℝ)(m:P): pass (fun i=>(g i).1) x R ρ m mainPair 0= ∑ i:Axis,∑ j:Axis,if i< j then singleQ g m i j i j x R ρ -singleQ g m j i i j x R ρ else 0 := by
 let X(i j a b:Axis):= Triad.prime (fun i=>(g i).1) x R ρ m j a b i 0
 let Q(i j:Axis):= X i j i j-X i j j i; let L(i j:Axis): ℂ:= (if i<j then Q i j else 0); let H(i j:Axis): ℂ:=if i<j then Q j i else 0
 have h₁(i j:Axis): ∑ a,∑ b:Axis, mainPair i j a b*X i j a b=Q i j:= by
    simp only [mainPair,Int.cast_sub, sub_mul,Finset.sum_sub_distrib]; unfold Q; congr 1
    · rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]; rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]; simp; intro c _ hc; simp [Ne.symm hc]; intro c _ hc; simp [Ne.symm hc]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]; simp; intro c _ hc; simp [Ne.symm hc]; intro c _ hc; simp [Ne.symm hc]
 have h(i j:Axis): (if i< j then singleQ g m i j i j x R ρ-singleQ g m j i i j x R ρ else 0)= L i j + H i j:= by
    unfold L H; split_ifs; · unfold Q X singleQ; abel
    simp
 have hp(i j:Axis): Q i j= L i j+ H j i:= by
    unfold L H; rcases lt_trichotomy i j with hi|hi|hi
    · rw [if_pos hi, if_neg hi.asymm,add_zero]
    · subst i; simp [Q]
    rw [if_pos hi, if_neg hi.asymm,zero_add]
 unfold Triad.pass; change ∑ i:Axis,∑ j:Axis, ∑ a:Axis,∑ b:Axis,mainPair i j a b * X i j a b=_; simp_rw [h₁,h,hp,Finset.sum_add_distrib]; rw [Finset.sum_comm (f:=fun i j=> H j i)]
omit h hs
lemma sieve (T:Itinerary) (c:ℕ→Side)(g:P→Badge G)(s:P→StepPath T)(h:Box x R ρ)(hs:∀ i,sails T (s i) (x i))(hc:MarkGrid T c) : Tendsto (fun k=> (↑(6*tagV T (firstK g T s) k):ℂ)) atTop (𝓝 (-(colC g*∑ j:P,pass (fun i=>(g i).1) x R ρ j mainPair 0))) := by
 let F:= firstK g T s
 obtain ⟨r,H,Hr⟩:= Deck.diameter_q h.confirms; let Q:Wash:=⟨r/3,r/2,by linarith,by linarith⟩
 have he: Q.rOut<r:= by change r/2<r; linarith
 let L(m:P)(i j:Axis):=singleQ g m i j i j x R ρ-singleQ g m j i i j x R ρ
 have ht (m:P)(i j:Axis): Tendsto (fun k=> (↑(firstQ T F m i j k):ℂ)) atTop (𝓝 (colC g*L m i j)):= by
    have hX(q p a b:Axis):=believed g h hs Q he (fun i j hz=> lt_trans (show r<8*r from by linarith) (Hr i j hz)) m q p a b hc
    unfold L; rw [mul_sub]; simp_rw [firstQ,Pi.sub_apply,ofReal_sub]; exact (hX i j i j).sub (hX j i i j)
 have h1: (colC g*∑ j:P,pass (fun i=>(g i).1) x R ρ j mainPair 0)= ∑ i:Axis,∑ j:Axis, if i< j then ∑ m:P,colC g*L m i j else 0:= by
    simp_rw [pass_face g x,Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; split_ifs with H; simp only [L]; simp only [mul_zero,Finset.sum_const_zero]
 rw [h1]; simp_rw [spiral T,ofReal_neg,ofReal_sum]; refine Tendsto.neg ?_; apply tendsto_finsetSum; intro i _; apply tendsto_finsetSum; intro j _; by_cases H : i < j; · simp only [H,if_true,ofReal_sum]; exact tendsto_finsetSum _ fun m _=> ht m i j
 simp only [H,↓reduceIte,ofReal_zero]; exact tendsto_const_nhds
end YM.RG11.FirstW.Branch
