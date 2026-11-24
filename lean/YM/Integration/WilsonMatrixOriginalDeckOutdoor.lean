import YM.Integration.WilsonMatrixOriginalDeckObserver
import YM.Integration.WilsonMatrixOriginalDeckMeasured

/-! The signed high-field contribution, including all lower fields after transport, in the authentic reflected two-point experiment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckOutdoor
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open Trace.Pilot Table Ward PhysMS RG17 RG12 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open Pier.Lair SharpGram SharpGram.Lenses WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckPath
open WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckFiledDebit
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {S:Table R.family.book} {f:Extraction.Order}
variable (F:Spec.Final R.family f S) (L:Layout F) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- A presold Gram measurement at the internal dates and one physically bounded exterior read.
The numerator retains complex signs and the reflected field occupies its original absolute position. -/
theorem measured (M:MS_Data G O) (issued:WilsonMatrixOriginalDeckMeasured.Intake R B F L J h M)
    (simple:G.Simple) (lead:PhysMS.Leading F J) {H:(Bel R.family.book).Hierarchy}
    (obey:∀d:ℕ,∀ᶠr in trail,AlignO F.sector F.room.kernel.spin H d (J r d))
    (far:(Bel R.family.book).Field h) {K:Set (Points 2)} (compact:IsCompact K) (sep:K⊆conf 2)
    {p:E4} (hp:(0:E4)≠p) (U:Set (Points 2)) (atPair:U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃ (g:Test 2) (A C D:ℝ) (e:ℕ),1≤A ∧ 0<C ∧ 0≤D ∧ tsupport g⊆U ∧ (∀x,(g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧ (∀μ,IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
      ∃Z:Set ℝ,Z∈trail ∧ ∃w:(r:Z)→Glyph B h→R.family.label h,
        (∀r:Z,0<r.val ∧ R.family.ref h≤L.level r.val ∧ ∀a,mass R.family h (L.shift h r.val (w r a))≤
          R.family.path.levels.clock.hatBeta (L.level r.val)^e*‖WilsonMatrixOriginalDeckColumns.basis R.family B h a‖ ∧
          master L h r.val (w r a)=J r.val h (WilsonMatrixOriginalDeckColumns.basis R.family B h a)) ∧
        ∀η:ℝ,0<η → ∃W:Set ℝ,W∈trail ∧ ∀ (r:ℕ→Z) (V:ℕ→Matrix (Glyph B h) (Glyph B h) ℂ)
          (n:ℕ) (pos:∀i,0<(r i).val),Monotone (fun i=>(r i).val) → (∀i≤n,(r i).val∈W) →
          ∀(u:Filter (ℕ×ℕ)) [u.NeBot],u≤L.lens → ∀δ:ℝ,0≤δ →
            (∀ᶠz in u,debit R B F L h g (fun i=>(r i).val) pos (fun i=>w (r i)) V n z≤δ) →
            ∀(c:Glyph B h→ℂ) (x:Points 2), x∈K →
              let t:=(r n).val
              let s:=(r 0).val
              let E:=WilsonMatrixOriginalDeckObserver.read F J h t x far
              ‖(∑b,c b*WilsonMatrixOriginalDeckExterior.proposed B J h t E (steps V n) b)-
                ∑b,c b*S.classMoment S (fun _:Fin 2=>h) (t•x)
                  ![J s h (WilsonMatrixOriginalDeckColumns.basis R.family B h b),S.adj F.room.kernel.spin h timeAxis (J t h far)]‖ ≤
                (∑b,‖c b‖)*(D*(A^2*(t/s)^η*(C*δ)*Real.exp (A*(C*δ)))) := by
  obtain ⟨g,A,C,e,gA,gC,support,real,pos,unit,gram,Z,openZ,w,book,settle⟩:=issued hp U atPair
  obtain ⟨D,gD,outside⟩:=WilsonMatrixOriginalDeckObserver.price B F J h simple lead obey far compact sep
  refine ⟨g,A,C,D,e,gA,gC,gD,support,real,pos,unit,gram,Z,openZ,w,book,?_⟩
  intro η hη
  obtain ⟨W,openW,spend⟩:=settle η hη
  refine ⟨W∩{t|∀x∈K,WilsonMatrixOriginalDeckExterior.fare B J h t (WilsonMatrixOriginalDeckObserver.read F J h t x far)≤D},Filter.inter_mem openW outside,?_⟩
  intro r V n live mono days u nb cut δ nonneg billed c x hx
  let t:=(r n).val
  let s:=(r 0).val
  let E:=WilsonMatrixOriginalDeckObserver.read F J h t x far
  have estimate:=spend r V n live mono (fun i hi=>(days i hi).1) u cut δ nonneg billed
  have external:=WilsonMatrixOriginalDeckExterior.weighted B J h t s E (steps V n) c
  change ‖(∑b,c b*WilsonMatrixOriginalDeckExterior.proposed B J h t E (steps V n) b)-
      ∑b,c b*E (J s h (WilsonMatrixOriginalDeckColumns.basis R.family B h b))‖≤_
  apply external.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  exact mul_le_mul ((days n le_rfl).2 x hx) estimate
    (Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) gD

end YM.Integration.WilsonMatrixOriginalDeckOutdoor
