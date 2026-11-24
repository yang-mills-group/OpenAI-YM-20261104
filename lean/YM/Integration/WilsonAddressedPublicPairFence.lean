import YM.Integration.WilsonAddressedPublicPairPins

/-! The original Wilson Gram bound at the actual predecessor of the coarser purchased card. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Integration.WilsonAddressedPublicPairFence
open Function Filter Finset Lattice RG Wilson Source Labels Cells OPE Extraction Spec
open Table PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank Trace.Terrace Push Push.RelayDifference
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicSelfCards (fee width)
open WilsonAddressedPublicPairFilm (reading reflected direct)
open WilsonOriginalPublicRelativeGramPins (cutoff)
open WilsonAddressedPublicPairPins (whenFiled cost name)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem film {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,S.Field (d i).val)(b:Fin 2→Bool)(cash:PostT (A)):
    let w₀:=width F (B 0) (d 0) (v 0) (b 0)
    let w₁:=width F (B 1) (d 1) (v 1) (b 1)
    let m:=min w₀ w₁
    0 < m → ∀ᶠ w:ℕ×ℕ in f.fuse,∀a:Axis,∀(L:Type)[Fintype L]
      (u:L→Fin 2→Site ((C).side w.1 w.2))(μ:L→ℂ),
    (∀i i' t,i≠i' → (C).S.a (m-1) < (C).S.a w.1*(separation (u t i) (u t i'):ℝ)) →
    ‖∑t,μ t*reading R F B d v b a w.1 w.2 (u t)‖ ≤
      (∑t,‖μ t‖)*∏i,fee F (B i) (d i) (v i) (b i):=by
  classical
  intro w₀ w₁ m pos
  have live:∀ᶠ w:ℕ×ℕ in f.fuse,∀i:Fin 2,(C).ref (d i).val ≤ w.1:=by
    apply eventually_all.mpr
    intro i
    rw [Extraction.Order.fused]
    unfold Extraction.Order.late
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop _
  have enough:∀ᶠ w:ℕ×ℕ in f.fuse,m ≤ w.1:=by
    rw [Extraction.Order.fused]
    unfold Extraction.Order.late
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop _
  have low(i:Fin 2):m ≤ width F (B i) (d i) (v i) (b i):=by
    fin_cases i <;> first | exact min_le_left .. | exact min_le_right ..
  have room:12*(C).S.a m < (C).S.a (m-1):=by
    obtain ⟨n,hm⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
    have cash':12<((C).S.block n).val:=by
      have hold:=cash.cropK n
      unfold ctl at hold
      change 12<((A).S.block n).val
      omega
    have np:0<(((C).S.block n).val:ℝ):=by exact_mod_cast ((C).S.block n).property
    rw [hm,Nat.succ_sub_one,(C).S.a_step]
    rw [←mul_div_assoc,div_lt_iff₀ np]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast cash') ((C).S.a_pos _) |>.trans_eq (mul_comm ..)
  filter_upwards [WilsonAddressedPublicSampledCards.original F B d v b,live,enough] with w paid truthful before
  intro a L _ u μ apart
  let hand:Fin 2→Bool:=Fin.cons true (fun _=>false)
  let axes:Fin 2→Signed:=Fin.cons (Signed.mirror a) (fun _=>1)
  have actual:=paid (m-1) m (by omega) before low (by norm_num; linarith only [room]) L u μ (fun _=>hand) (fun _=>axes)
    (fun _ i=>by fin_cases i <;> rfl) (fun t i i' h=>apart i i' t h)
  convert actual using 2
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  change (C).omega w.1 w.2 _ = _
  apply congrArg (moment ((C).beta w.1 w.2))
  funext U
  rw [Fin.prod_univ_two,Fin.prod_univ_two]
  change _*_=oriented _ true (Signed.mirror a) _ U * oriented _ false 1 _ U
  exact congrArg₂ (·*·)
    (reflected R (p:=w.2) (truthful 0) ((((B 0).rows (d 0)).arm (b 0) (v 0)).source w) a (u t 0) U).symm
    (direct R (p:=w.2) (truthful 1) ((((B 1).rows (d 1)).arm (b 1) (v 1)).source w) (u t 1) U).symm

variable {I:Type}[Fintype I]{D T:ℕ}{home:Bool→ℝ}(B:∀t,Book F (l:=l) H z D T (home t))
    (d:Fin (D+1))(v:Bool→I→S.Field d.val)(b:Bool→I→Bool)
omit [Fintype I] in
theorem original (cash:PostT (A))(t:Bool)(i j:I)(site:ℕ){L:Type}[Fintype L]
    (x:L→Fin 2→ Cover)(μ:L→ℂ):
    let m:=min (whenFiled R F B d v b false i) (whenFiled R F B d v b t j)
    0 < m → (∀a,‖(C).S.gridPoint site (x a 0-x a 1)‖ ≤ 1) →
    (∀a,2*(C).S.a (m-1) < ‖(C).S.gridPoint site (x a 0)-(C).S.gridPoint site (x a 1)‖) →
    ∀ᶠ w:ℕ×ℕ in f.fuse,∀a:Axis,‖cutoff R a (fun _:I=>d.val) site x μ
      (name R F B d v b) t w i j‖ ≤ (∑a,‖μ a‖)*(cost R F B d v b false i*cost R F B d v b t j):=by
  classical
  intro m pos compact apart
  let which:Fin 2→Bool:=Fin.cons false (fun _=>t)
  let books:=fun h:Fin 2=>B (which h)
  let vec:Fin 2→S.Field d.val:=Fin.cons (v false i) (fun _=>v t j)
  let branch:Fin 2→Bool:=Fin.cons (b false i) (fun _=>b t j)
  have witness:=film R F books (fun _=>d) vec branch cash pos
  have reach:∀ᶠ w:ℕ×ℕ in f.fuse,site ≤ w.1:=by
    rw [Extraction.Order.fused]
    unfold Extraction.Order.late
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop site
  filter_upwards [witness,reach] with w received mature
  intro a
  let o:=fun h q=>Cells.location (C).S site w.1 w.2 (x h q)
  have inside(h:L):(C).S.a (m-1) < (C).S.a w.1*(separation (o h 0) (o h 1):ℝ):=by
    have dist:=WilsonAddressedPublicPairGeometry.gap (C) (p:=w.2) mature (x h 0) (x h 1) (compact h)
    have far:=(apart h).trans_le dist
    dsimp only [o]
    linarith only [far]
  have spaced:∀i i':Fin 2,∀h:L,i≠i' → (C).S.a (m-1) <
      (C).S.a w.1*(separation (o h i) (o h i'):ℝ):=by
    intro h₀ h₁ s ne
    fin_cases h₀ <;> fin_cases h₁
    · exact (ne rfl).elim
    · exact inside s
    · rw [separation_comm];exact inside s
    · exact (ne rfl).elim
  have measured:=received a L o μ spaced
  rw [Fin.prod_univ_two] at measured
  exact measured

end YM.Integration.WilsonAddressedPublicPairFence
end
