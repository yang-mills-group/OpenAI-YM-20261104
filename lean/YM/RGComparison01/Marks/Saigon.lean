import YM.RGComparison01.Marks.Branch
import YM.RGComparison01.Marks.Spline
/-!
# Earn correct coordinate growth for the marked calculus

 Upgrade Checkered, Courants of E6 to polynomial witnesses
 required in the marked real payment. Invocation tools unchanged down to
 projections in that payment. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Gate

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge}
lemma growth (G : Gauge) (L : Side) {v:ℝ→ℝ} (hv:Geo G L v): Geo G L (fun x=> kernelGrowth (radiusB x) G (v x)) := by
  have hk:Geo G L (fun x=> 4*(radiusB x:ℝ)*(v x*royalty G)):= ((Geo.fixed _).times Geo.radii).times (hv.times (Geo.fixed _))
  exact (hk.joins (hv.joins hv)).joins hk
lemma gates (G : Gauge) (L : Side) (k m:ℕ) (C u:ℝ): Geo G L (fun x=> Tablet.facePrice k (radiusB x) m C u):= by
  have h:Geo G L (fun x=> ((radiusB x+2:ℕ):ℝ)):= by push_cast; exact Geo.radii.joins (Geo.fixed _)
  simp_rw [facePrice,Nat.cast_mul]; exact ((Geo.balling h).times (Geo.fixed _)).times (Geo.fixed _)

end YM.ConnectedActivityE6.Blaze.Gate
namespace YM.ConnectedActivityE6.Blaze.Vine

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge}
lemma greenery (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W : ℝ) (χ : Chi)
    (j : ℕ) {V : ℝ→ℝ} (h : RGComparison01.Fine G L V) (hv : ∀ᶠ x in atTop,0≤V x) :
    ∃ X : ℝ→ℝ, RGComparison01.Fine G L X ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T→ ShellAccess S G x W K γ →
    ∀ (F : Forest S.ratio) (Y : Coat T F) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Config G c) (z : E), Y.x=x → Y.width=K → Y.χ=χ → Mode U z j (V x) →
      let p i:= vary Y (U i); (p z).manifest → ∀ i, Brush j (|X x|) 1 (fun z=> stand (bar (p z) 0) i) z := by
  obtain ⟨A,hA,hX⟩:= Vine.signal G L W γ K j χ h
  obtain ⟨C,hC,hq⟩:= bounded_stencils P D hD
  obtain ⟨e,he,hD⟩:= prospect P L D hD j h hv
  let m:= royalty G
  let f x:=m*(|A x| *m); let b x:= C*(m*(f x*m)); let d x:= 4*(radiusB x:ℝ)*(V x*royalty G)
  let H x:= b x*(1+(d x+(V x+1+V x)+d x))^j
  refine ⟨fun x=> ‖Coat.scale‖*(e x+H x),?_,?_⟩
  · have hf : Fine G L f := Fine.grind_left (Geo.fixed _) (Fine.grind_right hA.higher (Geo.fixed _))
    have hz:= h.slow
    have hj : Geo G L d:= ((Geo.fixed _).times Geo.radii).times (hz.times (Geo.fixed _))
    have hc : Fine G L H:= Fine.grind_right (Fine.grind_left (Geo.fixed C) (Fine.grind_left (Geo.fixed _) (Fine.grind_right hf (Geo.fixed _)))) (((Geo.fixed (1:ℝ)).joins ((hj.joins ((hz.joins (Geo.fixed 1)).joins hz)).joins hj)).power j)
    exact Fine.grind_left (Geo.fixed _) (RGComparison01.Fine.plus he hc)
  filter_upwards [hD,hX, room G P L] with x hX he hp c f S T hS hh ha F Y E _ _ U z hv hw ht hhV p hF i
  subst x
  let y := Y.x
  let X:=p z; let s:= i.fst.fst; let k:= i.fst.snd
  have hj (i:Bond f) := he c f S T hh.length_eq ha E F Y U z ht rfl hw hhV i
  have hx := hp _ _ S T hh
  by_cases hg : Y.selected s (spot S k)
  swap
  · have he z: stand (bar (p z) 0) i=0 := by unfold stand bar; rw [if_neg (show ¬(p z).selected i.1.1 (spot S i.1.2) from hg)]; rfl
    simp_rw [he]; exact (Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl
  let G' (t:E) := strain (p t) s k 0
  have hG : Brush j (e y+H y) 1 G' z := by
    have hk := Blaze.turn hhV s
    apply (hX _ _ S T hS hh (choice s Y.k) k E (fun t=> pull s 0 (U t)) z hk (safe_hull X hF s k hg)).gathering
    rw [show (fun i=> orientedRow T (p i).R s k (p i).V ((p i).signal 0)) =
      (fun i=> straightened T Y.R (pull s 0 (U i)) (displacement s ((p i).saved) (replica S.ratio (U i))) k) from by
        funext i; simp only [Coat.signal, (p i).lens_zero, add_zero]; rfl]
    have ht i := displacement_pay (S:=S) (V:=fun i=> (p i).saved) s i _ _ hhV (hj (edge s i))
    have hn := royalty_ge G; have hm := hhV.pos
    exact ((hard_turn k hx (e:=royalty G *(|A Y.x| *royalty G)) (by positivity) (by exact (ht (0,0)).pos)
      (fun i _=> ht i) hk (hq c f S T hS hh.funds) hC.le).trim)
  have hh (z) : bar (p z) 0 i.1= Coat.scale • G' z := if_pos hg
  unfold stand; simp_rw [hh]; exact (colorEvaluated _ (hG.smul Coat.scale)).climb (le_abs_self _) le_rfl
end YM.ConnectedActivityE6.Blaze.Vine
namespace YM.ConnectedActivityE6.Blaze

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
open YM.ConnectedActivityE6.Blaze.Vine
variable {G : Gauge}
variable {η r Q : ℝ}
lemma saigon (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W : ℝ) (χ : Chi) (j : ℕ) {η r Q : ℝ} (hT : Torch η r Q)
    {V : ℝ→ℝ} (h : RGComparison01.Fine G L V) (hv : ∀ᶠ x in atTop,0≤V x) :
    ∃ b : ℝ→ℝ, Fine G L b ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T→ ShellAccess S G x W K γ →
    ∀ (F : Forest S.ratio) (Y : Coat T F) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Config G c) (z : E), Y.x=x → Y.width=K → Y.χ=χ → Mode U z j (V x) →
      let p i:= vary Y (U i); let X := p z
      X.manifest → Allow X.plate (along S) (tubularPrice G L) η r Q →
        (∀ i, Brush j (|b x|) 1 (fun y => voltage (p y) i) z) := by
  obtain ⟨Z,hZ,Ha⟩:=bounded_stencils P D hD
  let e := retain η r Q; let t:= P.top.width; let s:= min e (t/2)
  have hs : 0<s := lt_min hT.prices (half_pos P.top.width_pos); have ht : s<t := (min_le_right ..).trans_lt (by unfold t; linarith [P.top.width_pos])
  obtain ⟨M,hM,hp⟩:= Vine.greenery P L D hD K γ W χ j h hv
  let k:= carat D P L s Z; let m:= tubularPrice G L; let A:=k*k+1; let w:=payE η r Q m
  let b x:= kernelGrowth (radiusB x) G (V x); let g x:= k*|M x| *(1+(b x+1))^j
  let d x:= b x+b x; let l x:= facePrice j (radiusB x) m A w; let p x:=driftP j (d x)
  let f x:= (Fintype.card G.ColorIndex:ℝ) * ((l x*g x)*(1+(p x+1))^j)
  have he (g : ℝ→ℝ) (hp : Geo G L g) : Geo G L (fun x=> (1+g x)^j) := (((Geo.fixed 1).joins hp).power j)
  have hk:= growth G L h.slow; have hV:= gates G L j m A w
  have hM' : Fine G L g := Fine.grind_right (Fine.grind_left (Geo.fixed k) hM.higher) (he _ (hk.joins (Geo.fixed 1)))
  have hh := hk.joins hk; have hd : Geo G L p := (Geo.fixed _).times hh
  refine ⟨f,Fine.grind_left (Geo.fixed _) (Fine.grind_right (Fine.grind_left hV hM') (he _ (hd.joins (Geo.fixed 1)))),?_⟩
  filter_upwards [hp,room G P L] with x Hx HZ c f' S T hS hY hF F Y E _ _ U z hx hy he hV V' X h hX
  subst x; let x:= Y.x
  have hz:=Ha _ _ S T hS hY.funds
  have ht := replicaM Y D hS hY.length_eq (HZ _ _ _ _ hY) hV Z hZ hz hs.le ht
  have ha := plates Y D hS hY.length_eq (HZ _ _ _ _ hY) hV Z hZ hz hs.le ‹s<t›
  have hL i : Brush j (g x) 1 (fun y=>leanB (V' y) i) z := (beam_vec ht.reverse
    (u:=fun y i=> stand (bar (V' y) 0) i) (abs_nonneg _) zero_le_one (Hx _ _ S T hS hY hF F Y E U z rfl hy he hV h) i).trim
  have hp : 0 ≤ g x := by dsimp only [g]; have hh : 0≤k:=ht.basis; have he : 0≤ b x:= ht.pos; positivity
  intro i
  have hh:=padjets Y.shutter ha hX (show s≤e from min_le_left ..)
  have he (p) := (beam_vec hh.reverse hp zero_le_one (u:=fun i => leanB (V' i)) hL p).trim
  have hv : Brush j (f x) 1 (fun t=>voltage (V' t) i) z := tie G _ (mul_nonneg (mul_nonneg hh.basis hp) (pow_nonneg (add_nonneg zero_le_one (add_nonneg hh.pos zero_le_one)) j)) zero_le_one (fun p=> (he (i,p)).opposite)
  exact hv.climb (le_abs_self _) le_rfl
end YM.ConnectedActivityE6.Blaze
