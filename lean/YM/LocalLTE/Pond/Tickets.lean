import YM.LocalLTE.Pond.Arc
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
variable {G}
section paths
variable (P:BudgetPoint)(c:Clip)(R:PathData G)(o:Site n)(y:ℕ)
lemma tightL (i:Low) (h:i.length R ≤ P.B) : i.home R P o=neighbors P.B o :=by
   apply Finset.Subset.antisymm ?_ (Low.halo_home ..); unfold Low.home; cases hx:i.2 with
   | inl l=>exact Finset.Subset.refl _
   | inr l=>
      have hv (s:Slot) (hS:s.length ≤ i.length R): Wages.walkCuts s o ⊆ neighbors P.B o:=fun j hj=> (neighbors_mem ..).mpr ((separation_comm ..).trans_le (((slot_length s o hj).trans hS).trans h)); exact Finset.union_subset (Finset.union_subset (Finset.Subset.refl _) (hv _ (by simp [Low.length,hx]))) (hv _ (by simp [Low.length,hx]))
lemma tightH (i:High) (h:i.length R ≤ P.B) : i.home R o ⊆neighbors P.B o := by
    unfold High.home; rw [Paths.atom_foot]; intro j hj; exact (neighbors_mem ..).mpr ((Paths.where_slot _ _ _ hj).trans h)
-- membership. Low lens cost.Hlo.B−1.
lemma lousy (hb:3 ≤ P.B)(hc:WilsonStartup.Decent c P) (i:Low)(p:ℝ) (hi:i.length R<P.B) : P.Regular (neighbors (P.B-1) o) (Low.fresh R c i o p) := by
    let Z:BudgetPoint:= {P with B:=P.B-1, B_pos:=by omega}
    have ht:i.home R Z o=neighbors (P.B-1) o:= tightL Z R o i (by unfold Z; dsimp only; omega)
    have hL:= i.plain_local R Z (by unfold Z; dsimp only; omega) o
    have hV:= i.fresh_regular R c o hc p
    rw [← ht]; refine reg_bill (i.fresh_bill R c o hc p) hV.borel (?_) hV.symmetry
    intro U V h; unfold Low.fresh; rw [hL U V h]; rw [Low.proxy_local R i o U V (?_)] -- edit order
    exact agrees_mono h (Finset.coe_subset.mpr (i.clover_home R (by unfold Z; dsimp only; omega) o))
end paths
section widths
variable (G)
lemma proxyV (j:ℕ) : ∃ c:ℝ,0≤c∧∀ (n:Side)(o:Site n)(R:PathData G)(i:Low)(x:Directions G n),‖x‖≤1 → Brush j c 1 (i.proxy R o ∘ soloV) x:=by
    obtain ⟨c,hc,H⟩:= stretch G j; refine ⟨‖(2:ℝ)⁻¹‖*c,by positivity, fun n o R i x h=>?_⟩
    have ht (a b:PlaqAxes):Brush j (‖(2:ℝ)⁻¹‖*c) 1 (fun v=> inner ℝ (petals (soloV v) o a) (petals (soloV v) o b) /2) x:= by
         simp_rw [div_eq_inv_mul]; exact (H n o a b x h).smul _
    unfold Low.proxy Low.analogue; cases hy:i.2 <;> exact ht _ _
lemma slots (L:Side)(j:ℕ): ∃ p:ℝ→ℝ, Rate G L 0 p∧∀ t (n:Side)(o:Site n) (s: Slot),s.length ≤ radiusB t →∀ x:Directions G n,‖x‖≤1 → Brush j |p t| 1 (fun v=> s.atSite (soloV v) o) x:= by
    obtain ⟨c,hc,H⟩:= LocalLTE.Cabana.thick G j
    let D:= royalty G; let z:ℝ:= c*D; let a(t:ℝ):=2*(radiusB t:ℝ)*z; have hx:Rate G L 0 a:= ((Rate.radius_price (G:=G) (L:=L)).mul_left 2).mul_right _
    let p(t:ℝ):=D^2*(1+a t)^j; refine ⟨p,Rate.mul_left (by simpa only [zero_mul] using (((Rate.const 1).add hx).pow j)) _,fun t n o s hp x hh=>?_⟩
    have hv:= H _ x hh; have hk:Brush j (D^2) (a t) (fun v=> s.atSite (soloV v) o) x:= by
       apply (Blaze.slot_cost s o hv.pos hv.atLink).climb le_rfl; refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hv.pos (zero_le_one.trans (royalty_ge _))); gcongr
    exact hk.trim.climb (le_abs_self (p t)) le_rfl
lemma plainly (L:Side)(j:ℕ): ∃ p:ℝ→ℝ,Rate G L 0 p∧∀ t (n:Side)(o:Site n)(R:PathData G)(i:Low), i.length R ≤ radiusB t → ∀ x: Directions G n,‖x‖≤1→ Brush j (p t) 1 (i.plain R o ∘ soloV) x:=by
    obtain ⟨C,hC,hX⟩:=slots G L j; obtain ⟨A,hA,hp⟩:= priceF G j
    let v:= (innerSL ℝ (E:=G.Color)); let z t:=((‖(2:ℝ)⁻¹‖* (‖v‖*(|C t| * |C t|)))*(1+(1+1))^j)
    have hz:Rate G L 0 z:=((((Brim.absolut hC).mul (Brim.absolut hC)).weaken (show (0:ℝ)+0 ≤0 by linarith)|>.mul_left _).mul_left _).mul_right _
    refine ⟨(fun t=>z t+A),hz.add (Rate.const _),fun t n o R i h x hx=>?_⟩
    cases hy:i.2 with
    | inl l=>
      unfold Low.plain; rw [hy]; apply (hp n o _ _ hx).climb (le_add_of_nonneg_left _) le_rfl; unfold z; positivity
    | inr l =>
      have ht(s:Slot)(hs:i.length R ≥ s.length):= hX t n o s (hs.trans h) x hx
      have hv:= (((ht (i.left R l) (by simp [Low.length,hy])).twins (ht (i.right R l) (by simp [Low.length,hy])) v).smul (2:ℝ)⁻¹).trim
      apply (hv.climb (show z t ≤_ from le_add_of_nonneg_right hA) le_rfl).shimmy; filter_upwards with i'; simp only [Function.comp_apply,Low.plain,hy,div_eq_inv_mul]; rfl
lemma highs (L:Side)(j:ℕ): ∃ p:ℝ→ℝ, Rate G L 0 p∧∀ t (n:Side)(o:Site n)(R:PathData G) (s: High), s.length R ≤ radiusB t →∀ x:Directions G n,‖x‖≤1 → Brush j (s.charge R*p t) 1 (s.plain R o ∘ soloV) x:=by
    obtain ⟨c,hc,H⟩:= LocalLTE.Cabana.thick G j
    let D:= royalty G; let p (i:ℕ) (t:ℝ):=(D^2)^i*(1+i*(2*(radiusB t:ℝ)*(c*D)))^j
    have ht(i:ℕ):Rate G L 0 (p i):=by simpa only [p,zero_mul] using! ((((Rate.const 1).add ((((Rate.radius_price (G:=G) (L:=L)).mul_left 2).mul_right (c*D)).mul_left (i:ℝ))).pow j).mul_left ((D^2)^i))
    refine ⟨(fun t=>|p (3:ℕ) t| + |p (4:ℕ) t|),(Brim.absolut (ht 3)).add (Brim.absolut (ht 4)), fun t n o R s hs x h=>?_⟩
    have hv:= (Blaze.Vine.atom_brush (s.term R) soloV o (H n x h) hs).trim; apply hv.climb _ le_rfl
    rw [mul_assoc]; have hx:0≤ s.charge R:= Finset.sum_nonneg fun _ _=> abs_nonneg _
    apply mul_le_mul_of_nonneg_left (show p (s.arity) t ≤_ from ?_) hx; rcases s.significant with h|h
    · exact h ▸ (le_abs_self (p 3 t)).trans (le_add_of_nonneg_right (abs_nonneg (p 4 t)))
    exact h ▸ (le_abs_self (p 4 t)).trans (le_add_of_nonneg_left (abs_nonneg (p 3 t)))
end widths
end YM.AnalyticBridge.VerifiedReset.Collection.Price
