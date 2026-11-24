import YM.LocalTaylorR2.Canvas.Reeding

/-!
 # Borough/tag and exterior coherence of principal jets
 Retain all actual ephemerality (frozen χ choice and Patch geometry and frame list) on both sides.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Canvas
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R:Rep G f}{X X':Coat T F}{b a γ W α y' ζ d q :ℝ}{χ:Chi}{j p' l :ℕ}
variable {w w':Air f G}{Z:Support c}{k k':Finset ℕ} {A : Basecamp G}
open Work.G05 Animals Itinerary
lemma alerts {K : Signed}(i:Spot c f) (x : ZipP G c f)(p:Room P S T X.x) (h : Zone X X' (K.act (lead S i)) (12*X.B)) :
    ivy T X.x (choice K X.k) i x=ivy T X.x (choice K X'.k) i x:=by
  let o:=lead S i; let z:=K.act o
  have hR := p.sight
  have ht (U:Config G f): AgreeNear id o (X.B/2) (S.prediction U (choice K X.k)) (S.prediction U (choice K X'.k)):=by
    let q:= pull K⁻¹ 0 U
    have he: U=pull K 0 q:=by unfold q; rw [pull_pull,inv_mul_cancel]; simp [Lattice.affine]
    rw [he,(carry K (funds_branch p.accepted) X.k q).2,(carry K (funds_branch p.accepted) X'.k q).2]
    apply Zone.nearV K (h.predicts z ?_ _ _ (fun _ _=>rfl) p); change separation z z + (X.B/2+1)+_+_ ≤ 12*X.B; rw [separation_self]; change _+_+1≤ 12*(radiusB X.x); unfold Coat.B; omega
  unfold ivy squarepot; rw [rivers p i _ _ (fun _ _=>rfl) (fun _ _=>rfl) (ht _) true]
  apply congr_arg₂ (·-·) rfl
  refine sum_congr rfl fun j hj=> ?_
  have hh: focus S j=o:=by rw [cost_is_here j,(parent_iff j i).1 hj]
  let V := increment (1:Config G c) x.1; let U:=replica S.ratio V
  suffices h: Scroll.freely T X.x V (choice K X.k) j= Scroll.freely T X.x V (choice K X'.k) j from by change ‖Scroll.freely _ _ V _ j+_‖^2/2=‖Scroll.freely _ _ V _ j+_‖^2/2; rw [h]
  unfold Scroll.freely baseStroke; apply congr_arg₂ (·-·); swap; · rfl
  rcases j with j|j; · simp only [entryCost,Sum.elim]
  unfold entryCost
  dsimp only [Sum.elim]; unfold Tube.Z; rw [ht (replica S.ratio V) j (by change j.1=o at hh; simp [hh])]
lemma blueprint (J:Basecamp G) (p:Room P S T X.x) (i: Coat.Stream c f) (e : Zone X X' (rowSite S i) (12*X.B)) {u u':Directions G f}
    (h:∀ (j:Bond f), distAt S j (rowSite S i) ≤ X.B → X.Hot j → u j=u' j) : arbor J X i u=arbor J X' i u' :=by
  let o:= rowSite S i; let s:=i.1; let z:= lead S i.2; have ht:100≤X.B:= p.sight.1
  let A:= pull s 0 X.V; let C:= pull s 0 X'.V; let B:= bed X; have hB : B ≤ X.B := by unfold B bed; omega
  have he: AgreeNear id z (8*X.B) A C:= Zone.nearV s (e.pay.shrink (by change separation o o + (8*X.B+1) ≤_; rw [separation_self]; omega))
  have hv : bed X=bed X':= by unfold bed Coat.B; rw [e.temp]
  unfold arbor; dsimp only; rw [←hv]; apply Prod.ext
  · dsimp only; rw [e.chi]; funext j; unfold point; split
    next hp=> rw [(admits he (r:=B) (by omega)) j hp]
    next hp=> rfl
  dsimp only; funext j; split
  next hk=>
    let j':= edge s j; have ha : distAt S j' o ≤ X.B := (projects S i.1 (lead S i.2) j).trans (by change _≤bed X at hk; unfold B bed at *; omega)
    have hq : displacement s (X.signal u) (replica S.ratio X.V) j = displacement s (X'.signal u') (replica S.ratio X'.V) j :=by
      unfold displacement; dsimp only; rw [(e.reports j' (by change distAt S j' o+1+10*X.B ≤_; unfold o at *; have hj:= p.frame; omega) (h j' ha)).2, e.replica_here j' (by change distAt S j' o ≤ _; omega)]
    unfold spinRow; change G.adjoint (carrier z A _) (_)= G.adjoint (carrier z C _) (_)
    rw [carrier_near z _ A C _ he (by change separation z (atEdge S j) ≤ B at hk; omega), hq]
  next hp=> rfl

-- Exact cost read unchanged here (the next Canvas will regrade this).
lemma dyes (H:Borough X X' Z w w' k k' R) (p:Room P S T X.x) (i:Coat.Stream c f) (hr:500≤l)(hl: sleeve S X.B l (.inl i)⊆ Z) (hp:0<R.beta): pineCone A X a R i j (worldZ X R.beta w)=pineCone A X' a R i j (worldZ X' R.beta w'):=by
  let o:=rowSite S i; have hs:100≤X.B:=p.sight.1
  have hC:Cleanroom Z (400*X.B) o:= fun v hv=> hl ((Animals.neighbors_mem ..).2 (hv.trans (Nat.mul_le_mul_right _ (by omega))))
  have hu y (hi:y∈ Animals.neighbors X.B o):Cleanroom Z (30*X.B) y:= fans hC
    (by have hh := (Animals.neighbors_mem ..).1 hi; omega)
  have hs' (k : ℕ)(h:k≤250*X.B): Zone X X' o k:= H.social (fun i hi=> hC i (by omega))
  have he : Inside o X.seeds (200*X.B) ↔ Inside o X'.seeds (200*X.B):= (hs' _ le_rfl).covert _ (by rw [separation_self]; omega)
  let V:= hC
  let Z':= hs' (12*X.B) (by omega)
  let u:=worldZ X R.beta w; let u':=worldZ X' R.beta w'
  have hf : rootTaylor A X i j u= rootTaylor A X' i j u' :=by
    have he: arbor A X i u=arbor A X' i u' := blueprint _ p _ Z' (fun j hj _=> (H.hair p j (fans hC (by change separation o (atEdge S j)≤ _ at hj; omega)) _).2)
    rw [rootTaylor,rootTaylor,← H.weather,he, show ivy T X.x (choice i.1 X.k) i.2=_ from funext fun x=> alerts _ x p Z']
  have hP:= (H.rooms p R.beta).enforces p _ hu (2*a); rw [X.oldysis hp,X'.oldysis hp] at hP
  unfold pineCone booth; dsimp only; rw [← H.B, show rowSite S i=o from rfl, hP, (H.cornice p i (fun j hi=> hC j (hi.trans (by omega)))).1, hf]; simp_rw [he]; rfl
end YM.LocalTaylorR2.Canvas
