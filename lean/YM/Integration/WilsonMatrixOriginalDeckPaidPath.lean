import YM.Integration.WilsonMatrixOriginalDeckFiledDebit

/-! A bound on the actual signed cutoff measurements controls the whole multiscale transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPaidPath
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open Trace.Pilot Table Ward PhysMS RG17 RG12 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open Pier.Lair SharpGram SharpGram.Lenses WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckPath
open WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckFiledDebit
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {S:Table R.family.book} {f:Extraction.Order}
variable (F:Spec.Final R.family f S) (L:Layout F) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Quantitative high-to-low reconstruction using the original, pre-filed Wilson operands.
Every lower order is retained until the finite full-matrix product is taken. -/
theorem purchased (lead:PhysMS.Leading F J) {K:(Bel R.family.book).Hierarchy}
    (obey:∀d:ℕ,∀ᶠr in trail,AlignO F.sector F.room.kernel.spin K d (J r d))
    {u₀:Filter (ℕ×ℕ)} (mantle:Mantle F u₀) (services:Services R.family f S) (pegs:Pegs mantle L)
    (near:∀ᶠr in trail,R.family.S.a (L.level r)≤r ∧ r≤R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)
    (M:MS_Data G O) {p:E4} (hp:(0:E4)≠p) (U:Set (Points 2)) (atPair:U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃ (g:Test 2) (A C:ℝ) (e:ℕ),1≤A ∧ 0<C ∧ tsupport g⊆U ∧ (∀x,(g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧ (∀μ,IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
      ∃Z:Set ℝ,Z∈trail ∧ ∃w:(r:Z)→Glyph B h→R.family.label h,
        (∀r:Z,0<r.val ∧ R.family.ref h≤L.level r.val ∧ ∀a,mass R.family h (L.shift h r.val (w r a))≤
          R.family.path.levels.clock.hatBeta (L.level r.val)^e*‖WilsonMatrixOriginalDeckColumns.basis R.family B h a‖ ∧
          master L h r.val (w r a)=J r.val h (WilsonMatrixOriginalDeckColumns.basis R.family B h a)) ∧
        ∀η:ℝ,0<η → ∃W:Set ℝ,W∈trail ∧ ∀ (r:ℕ→Z) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ)
          (n:ℕ) (pos:∀i,0<(r i).val),Monotone (fun i=>(r i).val) → (∀i≤n,(r i).val∈W) →
          ∀(u:Filter (ℕ×ℕ)) [u.NeBot],u≤L.lens → ∀δ:ℝ,0≤δ →
            (∀ᶠz in u,debit R B F L h g (fun i=>(r i).val) pos (fun i=>w (r i)) V n z≤δ) →
            amount (steps V n-change B J h (r n).val (r 0).val) ≤ A^2*((r n).val/(r 0).val)^η*(C*δ)*Real.exp (A*(C*δ)) := by
  obtain ⟨g,A,C,hA,hC,supp,real,point,integral,gram,all⟩ :=
    WilsonMatrixOriginalDeckSignedHorizon.original R B F J h lead M hp U atPair
  obtain ⟨e,Z,hZ,w,prepaid,_⟩ := WilsonMatrixOriginalDeckFiled.purchased R B F L J h lead obey mantle services pegs near
  refine ⟨g,A,C,e,hA,hC,supp,real,point,integral,gram,Z,hZ,w,prepaid,?_⟩
  intro η hη
  obtain ⟨W,hW,decode⟩ := all η hη
  refine ⟨W,hW,?_⟩
  intro r V n pos ord days u _ cut δ hδ receipts
  let lengths := fun i=>(r i).val
  have result := (decode lengths V n pos ord days).2
  have read := WilsonMatrixOriginalDeckFiledDebit.realized R B F L J h g lengths pos (fun i=>w (r i)) V n
    (fun i _=>(prepaid (r i)).2.1) (fun i _ a=>((prepaid (r i)).2.2 a).2) u cut
  have cost := mul_le_mul_of_nonneg_left (le_of_tendsto read receipts) hC.le
  have scale : 0≤A^2*((r n).val/(r 0).val)^η := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (div_nonneg (pos n).le (pos 0).le) _)
  apply result.trans
  apply mul_le_mul (mul_le_mul_of_nonneg_left cost scale)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left cost (by linarith : 0≤A))) (Real.exp_pos _).le
  exact mul_nonneg scale (mul_nonneg hC.le hδ)

end YM.Integration.WilsonMatrixOriginalDeckPaidPath
