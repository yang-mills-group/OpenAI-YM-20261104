import YM.Integration.FVA1Physical.Wilson.TwoFieldBlocks
import YM.Integration.FVA1Physical.Wilson.BankDegree

/-! The actual two-stage Wilson coefficient on the physical coarse lattice
has a rooted weighted vault through its full polynomial degree. It accepts
independent field backgrounds and tests for every derivative word. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {μ:Type} [Fintype μ] {κ:μ→Type} [∀ a,Fintype (κ a)]

def composedDegree (p:ℕ):=emittedDegree p*(p+1+p)+2

theorem inherited_bank_degree (A:Issue G) (m i:ℕ) (b:PowerSeries ℝ) (T:Nesting G A.f) :
    (PowerSeries.coeff i (inheritedBank A m b T)).totalDegree ≤ m := by
  unfold inheritedBank enterRows
  rw [PowerSeries.coeff_map]
  apply (Rolling.clearD ..).trans
  simp only [sourceClock,PowerSeries.coeff_mk]
  apply totalDegree_finsetSum_le
  intro j _
  apply totalDegree_finsetSum_le
  intro d hd
  exact (totalDegree_smul_le ..).trans ((homogeneousComponent_isHomogeneous ..).totalDegree_le.trans
    (Nat.lt_succ_iff.mp (mem_range.mp hd)))

theorem composed_physical_vault (I:∀ a,κ a→Lamp G) {goal:Qlocal.Schedule.Goal G}
    (extra:Qlocal.Schedule.Obtainable goal) (simple:G.Simple) (b₀:ℝ) (hb:0<b₀) :
    ∃ (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex),
      R.family.path.levels.clock.kernel.penalty=b₀ ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ ∀ (p s L:ℕ), 6 ≤ s → ∀ (η:ℝ), 0<η →
      ∀ᶠ k:ℕ in atTop, ∀ N n,k ≤ N → ∃ S:Scene R.family.path.levels n (p+1+p),
        Realized R.alloy.B.kin N n k (p+1+p) (Lis.sun G u) S ∧
        ∀ j,k ≤ j → j+1<N → ∀ (F₁:Forest (R.family.path.levels.clock.op (j+1) n).ratio)
          (v₁:(R.family.path.levels.clock.op (j+1) n).Choices) (F:Forest (R.family.path.levels.clock.op j n).ratio)
          (v:(R.family.path.levels.clock.op j n).Choices),
          let E:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F₁ v₁
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let θ:=R.family.path.levels.clock.hatBeta
          ∀ (a:μ) (part:Bool) (b:Site A.c) (o:κ a→Site E.f),
            (∀ t:Slice (I a),separation (E.S.ratio.embed (A.S.ratio.embed b)) (legs (I a) o t).1 ≤ L*closeN (θ (j+2))) →
            let first:=emittedRows E R.metals.O (jointFieldBank (I a) E o part) p
            let input:=inheritedBank A (emittedDegree p) (S.action (j+1)) first
            ∀ i ≤ p, let W:=PowerSeries.coeff i (emittedRows A R.metals.O input p)
              W.totalDegree ≤ composedDegree p ∧
              Vault (Measuring.chart A.c G) {b} (αm (θ j)) s (composedDegree p) 0 W (θ j^η) := by
  have offer:=extra.also (Qlocal.Schedule.mapThreshold_obtainable (G:=G) (railMenu simple))
  obtain ⟨R,u,kern,⟨other,threshold⟩,frame,former⟩:=two_physical_field_blocks I offer simple b₀ hb
  refine ⟨R,u,kern,other,frame,?_⟩
  intro p s L hs η hη
  let h:=composedDegree p
  obtain ⟨l,hl⟩:=margin_eventually (half_pos hη)
  let nice:=max l (max h s)
  filter_upwards [former p s h L hs (margin l) (margin_pos l),eventually_ge_atTop (R.t nice)] with k money cut
  intro N n hN
  obtain ⟨S,scene,rows⟩:=money N n hN
  refine ⟨S,scene,?_⟩
  intro j kj jN F₁ v₁ F v E A θ a part b o near T src i hi W
  let Z:=RunFormalChain.fromRun R
  let H:=R.family.path.levels.params j
  let H':=R.family.path.levels.params (j+1)
  have wide:nice ≤ H.order:=(Nat.le_succ nice).trans (((R.makes.stages nice).2 j (cut.trans kj)).1)
  dsimp only [nice] at wide
  have budget:=railMenu_covers simple R.metals.K H H' A.S.patch A.S.kernel (by omega:s ≤ H.order)
    (by omega:l ≤ H.order) (x:=θ j) (threshold j n)
  have shift:tip G A.S.patch.L (θ j)=θ (j+1):=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  dsimp only at budget
  rw [shift] at budget
  have jN':j<N:=by omega
  have tr:=(scene.budget (j+1) jN' (kj.trans (Nat.le_succ j))).1
  have branch:= (R.family.path.levels.blocks j n).branches
  have prem:Premier (main A.f A.pre.clip A.pre.path):=by
    change Premier (main _ (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path)
    rw [Z.clips N n (j+1) jN',Z.selected N n (j+1) jN']; exact tr.quiet
  have crit:Critical A.F A.pre.clip A.pre.path A.ρ:=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [Z.clips N n (j+1) jN',Z.selected N n (j+1) jN'];exact (Z.planned.critical N j n jN' F).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [Z.clips N n (j+1) jN',Z.selected N n (j+1) jN']
    exact blueprint F v (Z.kin.path N (j+1)) _ branch tr.quiet (Z.post.price _) (Z.planned.gap N j n jN' F)
  have coeff:=normalized_input_degree A R.metals.O src p (emittedDegree p) (by unfold emittedDegree;omega)
    tr.bond pd ⟨fun t ht=>tr.plane.profile t (by omega)⟩
    (fun t _=>inherited_bank_degree A _ t (S.action (j+1)) T) hi
  constructor
  · change (PowerSeries.coeff i (emittedRows A R.metals.O src p)).totalDegree ≤ _
    rw [emittedRows,PowerSeries.coeff_map];exact (Rolling.clearD ..).trans coeff
  have raw:=rows j kj jN F₁ v₁ F v a part (A.S.ratio.embed b) o near i hi
  have z:bulkPoint A 0=0:=by rw [stationary_point A branch prem crit pd,smul_zero];exact map_zero _
  have initial:Vault (address A.F G) {A.S.ratio.embed b} (αm (θ (j+1))) s h (bulkPoint A 0)
      (PowerSeries.coeff i (normalizedRows A R.metals.O src p)) (θ (j+1)^margin l):=by rw [z];exact raw
  have issued:=selected_land R jN' S F v s budget.1 budget.2.1
  have moved:=emitted_rows A R.metals.O src p i s h branch prem crit pd b 0 budget.1 budget.2.2.1 issued initial
  simp only [smul_zero] at moved
  exact Quote.widen moved ((budget.2.2.2 h (by omega)).trans
    (Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed j).le (by linarith only [hl]))) le_rfl

end YM.Integration.FVA1Physical.Wilson
