import YM.LocalTaylorR2.Pavilion.Degas
/-! # Complete PTO of principal miniatures in Lie variables. No charge on nominal unaffected channels in the Pass (other enrolments). -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Pavilion
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o0 : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R: Rep G f}{X X':Coat T F}{J:Canvas.Basecamp G}{b a γ W α y' ζ d v q μ u C :ℝ}{χ:Chi}{j i' l :ℕ}
variable {Q:YM.ConnectedActivityE6.Target G P}{o:Target.Order G W}{H : Cash W s μ L Q o C T R}
open Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census

def mosaics (H: Cash W s μ L Q o C T R) (p:ℕ) (i: LogIndex c f): Port.Test T:=
    match i with
    | .inr (.inl (.inr (.inl k)))=> fun _ X _=> gainV p X k
    | _ => spinV H p i
lemma arrival (i:Bond f)(hS : Zone X X' (atEdge S i) (24*X.B)) (p:Room P S T X.x) : stag X i= stag X' i:= by
  funext t; exact colonial i (X:=Pavilion.drip X t) (X':=Pavilion.drip X' t) ⟨hS.temp,hS.width,hS.chi,fun _ _=>Iff.rfl,fun _ _=> rfl,fun _ _=>rfl,hS.site,hS.bond⟩ p
lemma curvature (i:Bond f)(h: Cash W s μ L Q o C T R)(hC:∀ (F:Forest S.ratio) (X:Coat T F),X.width=o.K→ X.x=s → ContDiffAt ℝ j (stag X i) 0 ∧ ∀ᶠ y in 𝓝 0, Hue (Pavilion.drip X y)) : let p:LogIndex c f:= .inr (.inl (.inr (.inl i)))
    Kept h (h.supportP (identityLog p)) (mosaics h j p):=by
  intro p; have hf:=h.laws.data; let o':=atEdge S i; let t:=Canvas.primary G
  constructor
  · intro F X X' w v hs ht Z hv hl hm; subst s
    let A:Borough X X' Z w v ∅ ∅ R:= ⟨hl,(observe _).1 hm,fun _ _=>Iff.rfl⟩; have hp:100≤X.B:=hf.room.sight.1
    have hP: Cleanroom Z (400*X.B) o':= fun j hj=> town_circle (S:=S) (p:=i) hv j (hj.trans (show 400*X.B≤ Q.halo*X.B from Nat.mul_le_mul_right _ (by have h:=Q.buys; omega)))
    have hL d (hd:d≤250*X.B): Zone X X' o' d:= A.social (fun i hi=> hP i (by omega))
    change gainV j X i=gainV j X' i; unfold gainV
    rw [← A.B, (hL _ le_rfl).forward i (by change separation o' o'+_+_ ≤_; rw [separation_self]; omega),pitch_fence t o' (hL _ (by omega)) (by omega), arrival i (hL _ (by omega)) hf.room]
  · intro E _ F X ht hk V Y w hV hY hw; change Measurable fun x=> if voyage X.seeds (200*X.B) i then 0 else blockTaylor j (stag X i) (Pavilion.pitch t (drive X (V x) (Y x)) o'); split_ifs; · exact measurable_const
    exact ((blockTaylor_contDiff j (stag X i) 0).continuous.measurable.comp (fiction t X _ hV))
  · intro F X hs hw hu z w
    obtain ⟨he,hΨ⟩:=hC F X hw hs; change (if voyage X.seeds (200*X.B) i then 0 else blockTaylor j (stag X i) (Pavilion.pitch t _ o'))=if voyage X.seeds (200*X.B) i then 0 else _; split; · rfl
    rw [footing]; apply blockTaylor_equivariant he _ (ContinuousLinearMap.id ℝ ℝ) ?_
    filter_upwards [hΨ] with x hx; change (Pavilion.drip X (tinters _ c f x)).condensation i=(Pavilion.drip X x).condensation i; rw [rafters]; exact (royals (Pavilion.drip X x) (fun _=> z o') hf.room.accepted hx).2.2 i
  intro F X hs hw hΨ k B d E _ _ _ V y hp hv h
  obtain ⟨v,hv⟩:=hp.sails; change Zest (fun t' x=> if voyage X.seeds (200*X.B) i then 0 else blockTaylor j (stag X i) (Pavilion.pitch t (drive X (V x) t'.1) o')) y k
  split_ifs; · exact Zest.still _
  exact (titrates t X o' hv).wand (blockTaylor_contDiff j (stag X i) k)
lemma titular (v d:ℝ→ℝ)(L:Side)(o:Target.Order G W)(P:Teller G)(Q:YM.ConnectedActivityE6.Target G P) (p i:ℕ)(ζ:ℝ)(hv:Rate G L (-(1/2)) v)(hd:Rate G L (-(1/2)) d)(hu:∀ᶠ x in atTop, 0≤v x)(D:Patch)(hD:D.Branches P.bind G)(χ:Chi) : ∃ b: ℝ→ℝ, Rate G L (-((p:ℝ)+1)/2) b ∧ (∀ x,0≤b x) ∧
    ∀ᶠ s in atTop, ∀(c f':Side)(S:StepData c f')(T:Tube G S)(R:Rep G f')(μ C:ℝ)(H:Cash W s μ L Q o C T R), S.patch=D → Pass H p i (mosaics H p) ζ (v s) (d s) 1 (b s) χ:= by
  obtain ⟨K,hK,hN,hP⟩:= graduates v d L o P Q p i ζ hv hd hu D hD χ
  obtain ⟨A,hA,hY⟩:= storesD P Q o v d L hv hu D hD χ p i
  have he:∀ᶠ s in atTop,0< Pressure.fiery G s L:= ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun _ hx=> Work.E09.temp_pos hx
  obtain ⟨Z,_,hZ⟩:= bazaar P Q o _ L Rate.flame (he.mono fun _ hx=> hx.le) D hD (p+1) (by omega)
  refine ⟨fun x=> K x+|A x|, hK.add (hA.compare (Eventually.of_forall fun x=> (abs_abs _).le)),fun x=>add_nonneg (hN _) (abs_nonneg _),?_⟩
  filter_upwards [he,hY,hZ,hP] with x hx hU hv' hp c f S T R μ C H hS
  have h := hp _ _ S T R μ C H hS
  constructor
  · rintro (i|k|i); exact h.stamp _
    · rcases k with k|k|k; exact h.stamp _
      · apply curvature k H; intro F X hw he; let η:= Pressure.fiery G x L; let g:= hv' _ _ _ _ R μ C H F X k hS he hw
        refine ⟨((g 0 (by rw [norm_zero]; exact hx.le)).2.smaller (p.le_succ)).smooth, ?_⟩
        filter_upwards [Metric.closedBall_mem_nhds (0:ZipP G c f) (show 0<η from hx)] with i hi using (g i (mem_closedBall_zero_iff.mp hi)).1
      exact h.stamp _
    exact h.stamp _
  · rintro (k|k|k) he <;> first | rfl | exact (he k rfl).elim
  intro j; have he' j:= (h.round j).climb H (le_add_of_nonneg_right (abs_nonneg (A x))) le_rfl
  rcases j with j|j|j; exact he' (.inl j)
  · exact (hU c f S T R μ C H j hS).climb H (le_add_of_nonneg_left (hN _)) le_rfl
  exact he' (.inr (.inr j))
def stars (G:Gauge): Regime G where
  symbol H l i := mosaics H l i
  enroll P Q:=by
    refine ⟨0, fun L _ D hD i l χ W _ μ _ o v d hv he hd a b ζ ha hb _=>?_⟩
    obtain ⟨B,hB,hN,hb'⟩:= titular v d L o P Q l i ζ hv hd he D hD χ
    obtain ⟨V,hV,h⟩:= passport G P Q L o ζ a χ B v d l i (by convert! (((Rate.power (a:=a)).weaken ha).pow l).mul hB using 1; ring) hN
    exact ⟨V,hV.weaken hb.le,(hb'.and h).mono fun x hx c f S T R C H hS _ r hr=> hx.2 _ _ S T R μ C H r _ hr (hx.1 c f S T R μ C H hS)⟩
end YM.LocalTaylorR2.Pavilion
