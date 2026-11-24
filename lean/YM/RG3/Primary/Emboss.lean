import YM.RG3.Primary.Tax
import YM.RG3.Law.Derivative

/-! # Put full d law in canonical form at slot s, exported on its SAME
P. Does not limit actual configuration, with p.Regular & null test
receipts on the new singleton and full merged K. Conditional on unused
reserves at ACTUAL addresses + viewport slot availability. At this stage
no aperture theorem from Makes: use authorized UV folio or padding theorem
which preserves same evaluations and bounds, or prove
Aperture explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Primary
open RG Push.Local Press Forms Law Finset Function Source Lattice Wilson Marker Overlay Ac MeasureTheory
open Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {R : Census V} (s : V) (d : Deck R P)
variable {D : ℕ} {F : Labels.Frame G D} (A : Hol G) (C : SectionData F)

private def sent (i:R.Mode) : ℂ →+ Marker.Poly R := { toFun := Poly.send i, map_zero' := Poly.send_zero _, map_add' := fun _ _ => by ext; simp only [Poly.part_plus,Poly.part_send]; split <;> simp }

omit [Fintype V] [Nonempty V] in
lemma okay (h : (0:Cover) ∈ C.stencil) (i : ℕ) (U : Config G n) :
    d.contents.ray i U - (dress s d A C).contents.ray (i+1) U =
      sent (R.fire s) (primary C (d.contents.origins s) P.p.threshold (vector s d A (F:=F) i) U + (feeds s d A C h).value i U) := by
  let e := vector s d A (F:=F) i
  by_cases hu : earns s d i
  · have he : e = weighted A F (d.contents.origins s) (d.contents.support i) P.p.threshold (d.contents.H i) := if_pos hu
    change Poly.send (d.contents.rays i) (masked _ _ _ U)-Poly.send (d.contents.rays i) (masked _ (grows _ _ C i) (fires s d A C i) U) = _
    have h0 : d.contents.rays i=R.fire s := hu
    rw [h0, fires,grows,if_pos hu,if_pos hu]
    change sent (R.fire s) _ - sent (R.fire s) _ = _
    rw [← map_sub]; apply congrArg
    rw [show (feeds s d A C h).value i U = rebate A C _ _ _ _ U from if_pos hu,rebate]
    simp only [Pi.sub_apply]
    change _ = primary C _ P.p.threshold e U + _; rw [he]; abel
  change d.contents.ray i U - _=sent _ (primary _ _ _ e U + (if earns s d i then _ else _))
  have ha : (dress s d A C).contents.ray (i+1) U=d.contents.ray i U := by
    unfold Bands.ray; rw [show (dress s d A C).contents.H (i+1)=d.contents.H i from if_neg hu,
      show (dress s d A C).contents.support (i+1)=d.contents.support i from if_neg hu]; rfl
  rw [ha, sub_self, show e=0 from if_neg hu,map_zero,Pi.zero_apply,if_neg hu,add_zero,map_zero]

omit [Nonempty V] in
lemma funded {w : ℝ} {θ : V→ℝ} {m δ} (he : Readable A C P.p n w) (hp : d.Active)
    {u c d' b a} (h : d.Budget θ u c d' b a) (hs : StemPay s d A C w θ m δ) :
    Adjust d (feeds s d A C he.sound.anchored) P (dress s d A C) := by
  let f := feeds s d A C he.sound.anchored
  let X := dress s d A C
  have hθ := h.radial.pure
  have hv := hs.purchase hθ he hp
  have hh i : Feed.hot (f.mode i) := R.fire_hot _
  refine ⟨rfl,rfl,fun U => ?_,fun U => ?_⟩
  · change _ = _ + f.bare U; unfold Feed.bare; simp only [if_pos (hh _),tsum_zero,add_zero]
  let o := d.contents.origins s
  let q : F.Coeff →L[ℂ] ℂ := ((LinearMap.proj (R:=ℂ) U).comp (primary C o P.p.threshold)).toContinuousLinearMap
  have hg := hs.combine hθ he hp
  have hC := hs.log_bounds hθ he hp h
  have HE := colored s d A C he hp
  have hQ : X.Active := by
    refine ⟨?_,hp.captions⟩
    exact ⟨HE.rays,HE.home,HE.regular,hp.articles.occurs,hp.articles.retained,hp.articles.inspects,hp.articles.keeps,hp.articles.meas,hp.articles.invi⟩
  have HJ := h.radial
  have ht : X.contents.Radial θ (u+δ) (c+δ+θ s*P.p.mass (C.footprint o) (w*(δ/(θ s)))) d' b :=
    ⟨hθ,hC.allowance,HJ.factor,hC.bulk,HJ.hits⟩
  let Vnew i := X.contents.ray i U
  let Vold i := d.contents.ray i U
  have h0 : Summable Vnew := (X.contents.bulkBound hQ.articles ht U).1
  have h1 : Summable Vold := (d.contents.bulkBound hp.articles h.radial U).1
  have h2 := (summable_nat_add_iff 1).2 h0
  let W i := f.value i U
  let Δ := sent (R.fire s)
  have cont : Continuous Δ := Bands.sends _
  have ht0 : Summable W := (hv.usage (show 0≤P.p.supportExponent+1 by linarith [P.p.exponent_pos]) hθ U).of_norm
  let Vc := Primary.comp s d A F
  have hx : HasSum (fun i => q (vector s d A i)) (q Vc) := hg.1.hasSum.map q q.cont
  have hb' : HasSum (fun i => Vold i - Vnew (i+1)) (Δ (q Vc + tsum W)) := by
    exact HasSum.congr_fun ((hx.add ht0.hasSum).map Δ cont) (fun i => okay s d A C he.sound.anchored i U)
  have hW : f.text U=Δ (tsum W) := by
    unfold Feed.text; simp only [f,Feed.mode,feeds,if_pos (show Feed.hot (R.fire s) from R.fire_hot _)]; exact (ht0.hasSum.map _ cont).tsum_eq
  have Ht0 := h0.sum_add_tsum_nat_add 1
  simp only [sum_range_one] at Ht0
  unfold Deck.log Bands.extra
  have Hu : ∑ j, Poly.send (R.fire j) (X.contents.units j) = (∑ j, Poly.send (R.fire j) (d.contents.units j)) + Δ (Vc 0) := by
    have hi j := map_add (sent (R.fire j)) (d.contents.units j) (if j=s then Vc 0 else 0)
    change ∑ j,sent (R.fire j) (d.contents.units j+if j=s then Vc 0 else 0) = _
    simp_rw [map_add]; rw [sum_add_distrib]; congr 1
    exact (sum_eq_single s (by intro i hi h; rw [if_neg h,map_zero]) (by simp)).trans (by rw [if_pos rfl])
  change _+tsum Vold+_= (∑ j,Poly.send (R.fire j) (X.contents.units j)) + tsum Vnew + d.captions.chord + f.text U
  rw [hW, Hu, ← Ht0]
  have hx : Δ (q Vc)=Δ (Vc 0)+Vnew 0:=map_add Δ ..
  have hh := hb'.tsum_eq
  rw [h1.tsum_sub h2,map_add,hx] at hh
  rw [sub_eq_iff_eq_add.mp hh]; abel
end YM.RG3.Primary
