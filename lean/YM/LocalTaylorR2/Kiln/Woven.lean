import YM.LocalTaylorR2.Kiln.Movable

/-! # Color-moving test, and tag locality, without any small dependence on the measure. Like Canvas.Ink & E06 etc. -/
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
open Itinerary
variable {B B' b α v ζ d' s γ W :ℝ}{J:Basecamp G} {w w': Air f G} {k k':Finset ℕ} {Z:Support c}
lemma curtain {x:ZipP G c f}(_h:P.Funds S T)(s:G.El) (hp:(A i.2.2).Invariant) : latent A S i (tinters s c f x)=latent A S i x:=by
  let u : Site c→ G.El:=fun _=> s
  have he : shaft S (tinters s c f x)=gauge (constantGauge u S.ratio) (shaft S x):=by
    change increment (replica S.ratio (increment 1 (tint s c x.1))) (spinRow S u x.2)= _
    rw [tint_one]; exact tilt ..
  unfold latent; rw [he,moss _ _ _ _ _ hp]
lemma chain {u : Directions G f} (z:Site c→ G.El) (hx: ShellAccess S G X.x W X.width γ): argument J (sluice X z) A i (spinRow S z u) = tinters (z (axis S i)) c f (argument J X A i u):=by
  let o:=axis S i
  apply Prod.ext
  · funext x; change point J X.χ (bed X) o (gauge z X.V) x = G.adjoint (z o) (point J X.χ (bed X) o X.V x); unfold Canvas.point; split
    next he=> rw [around z]; exact J.log.conjugate X.χ _ _
    next he=> rw [map_zero]
  funext x; let p:= homeFoot X A i; change (if atEdge S x∈ p ∧ distAt S x o≤ bed X then _ else 0) = (G.adjoint _) (if atEdge S x∈ p ∧ distAt S x o≤ bed X then _ else 0); split
  next he=> rw [pockets X hx]; change spinRow S (carrier o (gauge z X.V)) (spinRow S z (X.signal u)) x = G.adjoint (z o) (spinRow S (carrier o X.V) (X.signal u) x); unfold spinRow carrier; simp only [travel_gauge, deposits, ← G.adjoint_mul, inv_mul_cancel_right]
  next he=> rw [map_zero]
lemma levee (z:Site c→ G.El) {u:Directions G f} : switch R A i ((sluice X z).input (spinRow S z u))=switch R A i (X.input u):=by
  simp only [switch,opened,banks X z,Work.F05.pull_gauge_zero,Healthy,gauge_flags]
  congr 1
lemma pole (p:Room P S T X.x) {u u':Directions G f} (h: Zone X X' (axis S i) (12*X.B)) (hh:∀ j:Bond f, atEdge S j∈ homeFoot X A i → X.Hot j→ u j=u' j): argument J X A i u = argument J X' A i u':=by
  have hz:100≤X.B:=p.sight.1
  have hv: bed X = bed X':= by unfold bed Coat.B; rw [h.temp]
  let Xp:= axis S i; let O:=homeFoot X A i; have hP: AgreeNear id Xp (12*X.B) X.V X'.V:= h.pay
  have ht':homeFoot X' A i= O:= by unfold O homeFoot Coat.B; rw [h.temp]
  apply Prod.ext
  · ext1 j; change point J X.χ (bed X) Xp X.V j = point J X'.χ (bed X') Xp X'.V j; rw [h.chi,← hv]; unfold Canvas.point; split
    next he=> rw [(admits hP (r:=bed X) (by unfold bed; omega)) j he]
    next he=> rfl
  unfold argument; dsimp only; rw [← hv,ht']; ext1 j
  change (if atEdge S j ∈ O ∧ distAt S j Xp ≤ bed X then _ else 0) = (if atEdge S j ∈ O ∧ distAt S j Xp ≤ bed X then _ else 0); split
  next hx=>
    have hf := hx.2
    have hL: distAt S j (axis S i)+1+10*X.B≤12*X.B := by change distAt S j (axis S i) ≤ bed X at hf; unfold bed at hf; omega
    unfold spinRow; rw [carrier_near (axis S i) (atEdge S j) X.V X'.V _ hP (by change separation (axis S i) (atEdge S j) ≤ _ at hf; unfold bed at hf; omega), (h.reports j hL (hh j hx.1)).2]
  next _ => rfl
set_option maxHeartbeats 400000 in
lemma borough (h:Borough X X' Z w w' k k' R) (p:Room P S T X.x)(η a:ℝ)(Y:ℕ)(K:Basecamp G)(i:Trans f) {l:ℕ}(hh:500≤ l)(hs:atomFoot S.ratio l X.B A i⊆ Z)(hy:0<R.beta) : lantern K X a η A R i Y (worldZ X R.beta w) = lantern K X' a η A R i Y (worldZ X' R.beta w'):=by
  let U:= worldZ X R.beta w; let V:= worldZ X' R.beta w'; let o:= axis S i; let O:= homeFoot X A i
  have hx:100≤X.B:= p.sight.1
  have hc (x:Site c)(hj: x ∈ O) : Cleanroom Z (350*X.B) x:= fun y hy=> pastturn hs hj y (hy.trans (Nat.mul_le_mul_right X.B (by omega)))
  have he (k:ℕ) (hv:k≤ 230*X.B): Zone X X' o k:= h.social (fun y hy=> hc _ (show o∈O from heart) _ (by omega))
  have hΛ : dim X i ↔ dim X' i:= by unfold dim; rw [← h.B]; exact (he _ le_rfl).covert o (by rw [separation_self]; omega)
  have hT: light X A i ↔ light X' A i:= by unfold light; rw [h.weather]
  have hP: homeFoot X' A i= O:= by unfold O homeFoot; rw [h.B]
  have hF: pane X a A i U=pane X' a A i V:=by
    have he := (h.rooms p R.beta).enforces p O (fun i hi j hj=> hc i hi j (hj.trans (by omega))) (2*a)
    rw [X.oldysis hy,X'.oldysis hy] at he; unfold pane; rw [hP]; exact he
  have hj:= (h.rooms p R.beta).turnU p (l:=l) (by omega) i.1 (inspected ((A i.2.2).footprint i.2.1)) hs; rw [X.oldysis hy,X'.oldysis hy] at hj
  have hy: switch R A i (X'.input V)=switch R A i (X.input U):= Eq.symm (switching R A i hj)
  change lantern K X a η A R i Y U=_
  unfold lantern; simp only [hT,hΛ]; split_ifs; · exact congr_arg₂ (·*·) (congr_arg (η*·) (placed_local _ R.p _ _ _ hj)) hF
  next ht _=>
    have hy' : pollen K X A i Y U = pollen K X' A i Y V := by
      apply congr_arg (blockTaylor Y (latent A S i)); apply pole p (he _ (by omega)); exact fun j hj _=> (h.hair p j (fun i h=>hc _ hj i (h.trans (by omega))) _).2
    unfold V at hy hy' hF; rw [hy,hy', hF]
  next _=> rfl
end YM.LocalTaylorR2.Kiln
