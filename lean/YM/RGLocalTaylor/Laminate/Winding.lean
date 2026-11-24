import YM.RGLocalTaylor.Laminate.Known
import YM.RGLocalTaylor.Read.Germ

/-!
# Coupon exact shape for projections in the nilpotent exponent.

No low-leaf cut over the horizon of derivative order, all `column` keep
full exposures. Derivative supports on the UNMASKED germ and no sorting
by moved marker histories; the SAME expansion will be applied (after final
Unit projection on markers and removing the empty sector) and keep `bookFoot`
anchors. Includes current formula and across horizons compatible columns, on
fixed χ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March
namespace Laminate
open RG01.Survive Mayer Trees Merge Palette
variable (Y':Team R) (p : Molecule S)
local notation "U!" => p \ Y'.signs S
variable (H χ)

lemma columnShape (u:Orders k) : let f:= column Y' p H (χ:=χ) k u; GaugeInvariant f ∧ Measurable f ∧ LocalOn (H.unionP p) f:= by
  intro v; have h0 : GaugeInvariant (0:Config G c→ℝ) ∧ Measurable (0:Config G c→ℝ) ∧ LocalOn (H.unionP p) (0:Config G c→ℝ) := ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
  unfold v column; split; swap; · exact h0
  next he=>
    let g := Laminate.scopeM Y' p H (χ:=χ) k
    have ht (j:ℕ): GaugeInvariant (g j) ∧ Measurable (g j) ∧ LocalOn (H.unionP p) (g j):=by
      unfold g Laminate.scopeM; split; swap; · exact h0
      let f (u:Decors U! k) := Mayer.tagged H p (partner Y' H) u
      have h u : Fits H (f u) (H.unionP p) 1:= fits_tagged (f':=partner Y' H) _ (fun i hi=> (partnerFit (compartments Y' p he ▸ hi)).1) _
      exact ⟨fun x U=> sum_congr rfl fun u _=> (f u).onLog_invariant (H:=H) (χ:=χ) p x U, Finset.measurable_fun_sum _ (fun u _=> ((h u).log_seam (χ:=χ)).2), fun U V hu=> Finset.sum_congr rfl fun u _=> ((h u).log_seam (χ:=χ)).1 U V hu⟩
    split
    · let X':=frontLoad Y' p (H:=H); have hv := (fit_original (H:=H) (M:=Y') (j:=1) p).log_seam (χ:=χ)
      unfold Laminate.excess; refine ⟨?_,?_,?_⟩
      · intro z U; simp only [Pi.sub_apply,Finset.sum_apply]; exact congr_arg₂ (·-·) (X'.onLog_invariant (χ:=χ) p z U) (sum_congr rfl (fun j _=> (ht j.val).1 z U))
      · apply hv.2.sub; apply show ((Measurable (fun V=> (∑ d:Fin (k+1), g d.val) V))) from ?_; simp_rw [Finset.sum_apply]; exact Finset.measurable_fun_sum _ (fun j _=> (ht j.val).2.1)
      intro x y hy
      simp only [Pi.sub_apply,Finset.sum_apply]; exact congr_arg₂ (·-·) (hv.1 x y hy) (sum_congr rfl (fun j _=> (ht j.val).2.2 x y hy))
    exact ht _
lemma commonColumn (i:Fin (k+1)) (i':Fin (l+1)) (h:i.val=i'.val) : column Y' p H (χ:=χ) k i.castSucc=column Y' p H (χ:=χ) l i'.castSucc:= by
  unfold column; simp only [Fin.val_castSucc]; rw [if_neg (show i.val≠ k+1 from i.isLt.ne),if_neg (show i'.val≠l+1 from i'.isLt.ne)]; unfold Laminate.scopeM; split
  · split
    next=> rw [h]; exact fixed _ _ (h ▸ Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ i'.isLt) _
    rfl
  rfl

lemma prescriptive {ρ e uJ vJ θ K : ℝ} (v:H.ThinP) (N : Captain H j C' d Y B A b r a q n χ) (h:Awning H N.conduit A b ρ e uJ vJ k l) (hT:Q.goal L s≤K)
    (M m:ℕ) (u:Orders M)(hK:Approved K θ j M) (ha:authorized H v.val) (he:m≤M) (hy:u.val=m) (hz:Start v.val)(hy':Y'.signs S⊆v.val) (V:Config G c)(hf:Healthy (Pressure.temp s) (H.smallAt v) V) :
    let W:=v.val \ Y'.signs S
    column Y' v.val H (χ:=χ) M u V= ∑ g∈univ.filter (fun g:Decors W M =>decorOrder g=m),
       likely fun i:Greenbelt.Reserve S=>likely fun j:S.Choices=>
        let X:= ((planted (prism T s χ o.K V (Greenbelt.allot i)) v.val).taggedL j)
        ∫ z,planned H v.val g (partner Y' H) X z ∂Insert.moment X:= by
  dsimp only; unfold column Laminate.scopeM; rw [if_pos hy',hy, if_neg (show ¬m=M+1 by omega), if_pos hz]
  exact sum_congr rfl fun i hi=> Mayer.localized i sdiff_subset ((mem_filter.mp hi).2.symm ▸ he) N h hT hK _ (fun i hi=> (partnerFit (compartments Y' _ hy' ▸ hi)).1) (fun i hi=>hz _ (sdiff_subset hi)) v.2.2 ha V hf

variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ)
/-- Component-letter register. Keep before changing marker bases and `stance`s (none privileges). -/
abbrev VoucherL (S:StepData c f)(k:ℕ):= Tickets (Palette.sign M' S) × Orders k
def rector (q:H.ThinP) (V:Config G c)(u:VoucherL M' S k): ℝ:= packPrice rA u.1.val*column (team M' u.1) q.val H (χ:=χ) k u.2 V
omit [Fintype ι] in
lemma rector_shape (q:H.ThinP) (u:VoucherL M' S k) : let f:= fun V=> rector χ H M' rA q V u; GaugeInvariant f ∧ Measurable f ∧ LocalOn (H.smallAt q) f := by
  intro f; obtain ⟨hi,hL,hh⟩:= columnShape χ H (team M' u.1) q.val u.2 -- order?
  exact ⟨fun g U=> congr_arg (_*·) (hi g U),measurable_const.mul hL,fun U V hu=>congr_arg (_*·) (hh U V hu)⟩

lemma warrant (N : Captain H j C' d v Y A b r B q n χ) (i:H.ThinP)(U:Config G c) (x : ℝ)(y : Finset ι) (k:ℕ):
    vote M' H χ rA i.val U x y=masked (Pressure.temp s) (H.smallAt i) (fun V=>∑ p:VoucherL M' S k, Switch.click p.1.val (rector χ H M' rA i V p) x y) U:=by
  letI:Nonempty (Forest S.ratio):=Tree.select S.ratio S.patch.odd_side
  let g p V:=rector χ H M' rA i V (p:VoucherL M' S k); have h p:Palette.act M' H χ U i.val p=masked (Pressure.temp s) (H.smallAt i) (fun V=>∑ j:Orders k,column (team M' p) i.val H (χ:=χ) k j V) U:=by
    by_cases hz:p.reach⊆i.val
    · simp_rw [←Finset.sum_apply,Laminate.passport _ _ _ k (Palette.label M' p|>.symm ▸ hz)]; exact teamLecturer (Palette.label M' p|>.symm ▸ hz) U N i.2.2
    rw [show act _ _ _ _ _ p=0 from Classical.byContradiction (fun H=>hz ((present M' _ _ _ p _ (F:=Classical.ofNonempty) H).1))]; unfold column; simp only [Palette.label,hz, ↓reduceIte]; unfold masked; apply Eq.symm; by_cases h:Healthy (Pressure.temp s) (H.smallAt i) U; rw [Set.indicator_of_mem h]; simp; exact Set.indicator_of_notMem h _
    
  unfold vote color; simp_rw [h, Palette.amplitudes]; by_cases hx: Healthy (Pressure.temp s) (H.smallAt i) U
  · simp_rw [masked_eq _ _ _ _ hx]; rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun i _=>?_; unfold Switch.click; by_cases hp:i.val⊆y <;> simp_rw [hp]; simp only [↓reduceIte]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _=>mul_assoc ..); simp
  simp [masked_ne _ _ _ _ hx]

end Laminate
end YM.RGLocalTaylor
