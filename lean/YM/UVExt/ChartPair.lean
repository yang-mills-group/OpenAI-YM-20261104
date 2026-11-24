import YM.UVExt.GramLimit

/-! Use the actual Frame for each chart determinant and the fixed chart density. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths.Slab
open Function Set Filter Matrix Lattice Laurent Tree Exterior Precision Wilson RG Bid
open scoped BigOperators Topology ContDiff Classical InnerProductSpace
variable {G:Gauge} {f c:Side} {S:StepData c f} {g : Ratio c f}
private lemma basis_reach (F : Forest g) : reach (frame (G:=G) F) := by
   intro u v ht
   have he (k : Key F G→ℝ) (z : F.Free) j : (∑ i,k i • frame F i) z j=k (z,j) := by
      rw [Finset.sum_apply]; change (fun u:G.Color=>u j) (∑ c:Key F G,(k c • frame F c) z)=k (z,j); rw [show (fun (u : G.Color)=>u j) (∑ i:Key F G, ((k i) • frame F i) z) = _ from map_sum (PiLp.proj (𝕜:=ℝ) 2 (fun _=>ℝ) j) (fun (i:Key F G)=> ((k i) • frame F i) z) _] -- placeholders
      simp_rw [Pi.smul_apply]
      rw [Finset.sum_eq_single (z,j)]
      · rw [frame,Pi.single_eq_same,EuclideanSpace.basisFun_apply]; simp
      · rintro ⟨a,b⟩ _ hh
        by_cases h : a=z
        · obtain rfl := h
          simp [frame,EuclideanSpace.basisFun_apply,show j ≠ b from by rintro rfl; exact hh rfl]
        simp [frame,h]
      · simp
   exact funext fun ⟨i,j⟩=> (he u i j).symm.trans ((congr_arg (fun u=>u i j) ht).trans (he ..)) -- function type ht

variable {U R : ℕ→PathData G} {p r : Clip} {t : S.Choices} {F : Forest S.ratio} {ρ : ℕ→fieldDir G c 1 → AxisChart G F}
    {Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ} {η : ℝ}
    {U' R' η' ρ' Y'} (L : Slab F U R p r t ρ η Y) (V : Slab F U' R' p r t ρ' η' Y')
def determinantLine (L : Slab F U R p r t ρ η Y) n (v) (z : ℝ) := Real.log (Matrix.det (hessian F t p (U n) (z • v) (ρ n (z • v))))

def contribution (O : ChartRatio G) (v : fieldDir G c 1) (ρ : fieldDir G c 1→AxisChart G F) (z : ℝ) :=
    Real.log (∏ i : F.Free, O.J (ρ (z • v) i))
variable {O : ChartRatio G}
lemma contributionLimit {ρ ρ' : ℕ→fieldDir G c 1 → AxisChart G F} (hO : LocalRatio O) (v : fieldDir G c 1)
    (w : ℕ→fieldDir G c 1 × AxisChart G F)
    (h : Joint 2 (fun i=> paired v fun z=>ρ i (z • v)) (fun i=> paired v fun z=>ρ' i (z•v)))
    (hT : ∀ᶠ i in atTop,ρ i 0=0) : Joint 2 (fun i=> contribution O v (ρ i)) (fun i=>contribution O v (ρ' i)) := by
   let X := fieldDir G c 1 × AxisChart G F
   let P (v : X) := ∏ i : F.Free,O.J (v.2 i)
   let N := Real.log ∘ P
   have hP : ContDiffAt ℝ (⊤:WithTop ℕ∞) P (0,0) :=
     contDiffAt_prod (f:=fun i (t : X)=>O.J (t.2 i)) fun i _hp=> ((hO.germ _ (Metric.mem_ball_self hO.patch)).comp (f:=fun v:X=>v.2 i) (0,0) ((contDiffAt_apply ℝ G.Color i 0).comp (f:=Prod.snd) (0,0) contDiffAt_snd)) -- argument O.J 0 syntactically eval prod
   have hN : ContDiffAt ℝ (⊤:WithTop ℕ∞) N (0,0) := (Real.contDiffAt_log.mpr (show P (0,0) ≠ (0:ℝ) by change (∏ z:F.Free,O.J ((0:AxisChart G F) z)) ≠ 0; simp [hO.anchored])).comp (0,0) hP
   obtain ⟨A,hA,hA'⟩:=h.at_zero
   have ht : A=(0,0) := tendsto_nhds_unique hA (tendsto_const_nhds.congr' (hT.mono fun i hi=>by change (0,0)=(0•v,_); simp [hi]))
   exact Both_comp (f:=fun i=>paired v fun z=>ρ i (z•v)) (g:=fun i=>paired v (fun z=>ρ' i (z•v))) N 2 h hA hA' (ht ▸ hN)

set_option maxHeartbeats 600000 in
lemma determinant_branch (v) (h₀ : Junction L.inFT V.inFT 4) (he : 0 < η) (hp : 0 < η') : Joint 2 (L.determinantLine · v) (V.determinantLine · v) :=
by
     unfold determinantLine
     have ht := gram_both (f:=L.inFT) (f':=V.inFT) (frame (G:=G) F) (by exact (basis_reach F)) (x:=v) (ρ:=fun i z=>ρ i (z•v)) (ρ':= fun i z=>ρ' i (z•v)) h₀ (L.solves_slab v) (V.solves_slab v) η he (L.vertical_gap he) η' hp (V.vertical_gap hp)
     change Joint 2 (fun i z => Real.log (hessian F t p (U i) (_:fieldDir G c 1) (ρ i _) |>.det)) _
     unfold hessian
     simp only [Function.comp_apply,shiftedHess,inFT,Function.uncurry_apply_pair] at ht
     exact ht
lemma chart_terms (v) (h₀ : Junction L.inFT V.inFT 3) (he : 0 < η) (hp : 0 < η') (H : LocalRatio O) : Joint 2 (contribution O v ∘ ρ) (contribution O v ∘ ρ') := by
   let h1 := L.solves_slab v; let h2 := V.solves_slab v
   obtain ⟨w,hW⟩ := responses_joint h1 h2 h₀ he hp (vertical_gap L he) (vertical_gap V hp)
   let p i (z : ℝ) := ρ i (z•v); let q i (z:ℝ) :=ρ' i (z•v)
   have ht : lucid (paired v ∘ p) := h1.mono (fun i hi=> (pairSmooth (ρ:=p i) v hi.analytic_pay).of_le le_top); have ht' : lucid (paired v ∘ q) := h2.mono (fun i hi=> (pairSmooth v hi.analytic_pay).of_le le_top)
   exact contributionLimit H v w ⟨ht,ht', fun i hi=>⟨w i,hW i hi⟩⟩ (L.critical.mono fun i hi=> by simpa using hi.1)

end YM.UVExt.Paths.Slab
