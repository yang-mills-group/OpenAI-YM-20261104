import YM.LocalTaylorR2.Kiln.Assume
import YM.LocalTaylorR2.Kiln.Cadet

/-! # Uniform (after L) near-and-far ticket. Before weights. Includes physical marker preprice ingredients separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Kiln
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Work.G05
variable {G:Gauge}{c f L n : Side} {S:StepData c f}{P:Teller G}{T:Tube G S}{F:Forest S.ratio}
variable {d j k p:ℕ}{s:ℝ}{R:Rep G f}
variable {X X': Coat T F} {A : ℕ→ Atom G d}{i:Trans f}
open Itinerary Port
variable {W :ℝ}
def debt (J:Basecamp G)(p:ℕ)(A:ℕ→ Atom G d)(R:Rep G f)(a η:ℝ)(i:Trans f): Port.Test T:= fun _ X w=> living X a η A R i (worldZ X R.beta w) - lantern J X a η A R i p (worldZ X R.beta w)

lemma portrait (G:Gauge) (P:Teller G) (o:Target.Order G W) (L:Side) (J:Basecamp G)(D:Patch)(hD:D.Branches P.bind G) (v s:ℝ→ℝ)(hV: Rate G L (-(1/2)) v)(ht: Rate G L (-(1/2)) s)(hw:∀ᶠ x in atTop,0 ≤ v x)(d j p:ℕ)(χ:Chi)(l:ℕ) : ∃ K K', Rate G L (-((p+1:ℕ):ℝ)/2) K ∧ Rate G L 0 K' ∧ ∀ᶠ x in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(R:Rep G f)(Q:YM.ConnectedActivityE6.Target G P)(μ C:ℝ)(H:Cash W x μ L Q o C T R), S.patch=D → ∀ (η:ℝ)(A:ℕ→ Atom G d)(i:Trans f), (A i.2.2).Invariant→ Sees H j (v x) (s x) χ (debt J p A R o.a η i) (bill (K x) (K' x) η x A i) (seating l x S A i):=by
  obtain ⟨C,hC,hY⟩:= Basecamp.tenant G L P J j hV hw
  obtain ⟨B,hB,hN,hX⟩:= Clutch.central G L χ j ht (2*o.a)
  obtain ⟨r,g,hr,he,hG,hq⟩:= latentRate G P L D hD d (j+p+1)
  let e x:= 4*(radiusB x:ℝ)*(v x*royalty G); let Y x := s x+4*o.a*Pressure.fiery G x L; let H:= royalty G
  let a x:= H*(Y x*H)*(1+(e x+1+e x))^j
  -- compose coarsely, without requiring larger hatch on every edge.
  let u x:= C x + |a x| + (C x + |a x|)
  have h₁ : Rate G L 0 e:= by simpa only [zero_add] using! ((Rate.radius_price.mul_left 4).mul ((hV.weaken (b:=0) (by norm_num)).mul_right (royalty G)))
  have h₂:Rate G L (-(1/2)) a:= by
    have h:Rate G L 0 (fun x=> (1+(e x+1+e x))^j):= by simpa only [zero_mul] using! (((Rate.const 1).add ((h₁.add (Rate.const 1)).add h₁)).pow j)
    have hY:Rate G L (-(1/2)) Y:= ht.add (Rate.flame.mul_left _)
    simpa only [add_zero] using ((hY.mul_right H).mul_left H).mul h
  have y:= hC.add (h₂.compare (v:=fun x=> |a x|) (Eventually.of_forall fun x=>(abs_abs _).le)); have hu:Rate G L (-(1/2)) u:= y.add y
  let U x:= j.factorial*g x*((1+((1+1)*1):ℝ))^j*u x^(p+1); let Ω x:=(1+B x)^j
  have hz : Rate G L (0) Ω:=by simpa only [zero_mul] using! (((Rate.const 1).add hB).pow j)
  have hg:Rate G L (-((p+1:ℕ):ℝ)/2) U:=by convert! ((((hG.mul_left _).mul_right _).mul (hu.pow (p+1))): Rate G L _ _ ) using 1; push_cast; ring
  refine ⟨fun x=> |U x| *Ω x, fun x=> (2:ℝ)^d*Ω x,?_,hz.mul_left _,?_⟩
  · simpa only [add_zero] using (hg.compare (v:=fun x=>|U x|) (Eventually.of_forall fun x=> (abs_abs _).le)).mul hz
  filter_upwards [hY,hX,hu.below (by norm_num) r hr] with x hC hQ hu c f S T R Q μ C' H hS η A i h F _ _ _ Z X V y z w t hx hk hMX hχ hv hs
  subst x
  have hA:= H.laws.data; have hl:= hA.funds.length_eq; have hr:=hA.room
  unfold debt; simp_rw [hs.moving]
  let b:= seating l X.x S A i; have hb:1 ≤ b:= sit_ge ..
  apply count_in o.a η w p hv hs hr h hb (hN X.x)
  · let Y := atomFoot S.ratio l X.B A i; have hp:homeFoot X A i ⊆ Y:= image_subset_image (Corona.halo_mono (by rw [zero_mul]; exact Nat.zero_le _) (Subset.refl _))
    apply (hQ _ _ S T Z X rfl hχ hl (mul_pos (by have hp:= o.large; positivity) hr.fiery) F t _ _ w V y z hs _ _ hp).climb le_rfl
    apply mul_le_mul_of_nonneg_left _ (hN _); exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans (le_add_of_nonneg_left zero_le_one)
  intro he' hy hZ
  let o':= axis S i; let X' y:= vary X (V y)
  have hy': Clean (V w) X.x o' (40*radiusB X.x+1):=by rw [hs.atV]; exact (clean_far X.seeds X.V hMX (show ¬ Inside o' X.seeds (200*radiusB X.x) from hy)).shrink (v:=o') (D:=40*radiusB X.x+1) (by rw [separation_self]; have hv:=hr.sight.1; omega)
  obtain ⟨hU,hΓ⟩:= hC.2 _ _ S T hl hr (bed X) (by unfold bed Coat.B; omega) F V w X.χ o' hv hy'
  obtain ⟨hC',hY'⟩:= warranted _ _ _ _ J _ _ _ i _ hv hs hr h he' hy hZ hU hΓ
  have hz:= hC.1; have hb:0 < u X.x:=by unfold u; positivity
  let f':=latent A S i; let v' t:= argument J (X' t) A i (y t)
  have hρ:= (le_abs_self _).trans hu
  have hh : Brush j (u X.x) 1 v' w:=by unfold Coat.t at hC'; rw [hl] at hC'; exact hC'
  apply (((Mesh.priced (d:=p) (f:=f') hb (hρ.trans ‹r ≤ 1›) (fun t h=> hq X.x _ _ S T t A i hS hr.accepted (h.trans hρ) X.k he') hh).shimmy ?_).climb ?_ le_rfl)
  · exact hY'.mono fun t ht=> congr_arg (·-pollen J (X' t) A i p (y t)) ht
  apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (le_abs_self (U X.x)) (munch A i)); unfold U; ring
end YM.LocalTaylorR2.Kiln
