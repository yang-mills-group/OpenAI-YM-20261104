import YM.LocalTaylorR2.Exponent.Anima

/-!
 # Bill at any bulk precinct; not using a global-neighborhood cardinal cost. Numeric Price permits grow also multiplied at huge scaling factors, through any specified p. Use true mask in comparing. Proof on genuine Mercy Patch.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Canvas Axial Kiln Work.G05
variable {i:Trans f}{X:Coat T F}{K:ℕ→Atom G p} {b:ℝ} {w:Air f G}{U:Support c}
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable (H: Cash W X.x μ L Q o C T R)
variable {V:E→ Config G c}{u:E→ Directions G f}{z:E→ Air f G}{x:E}
variable (h:Mode V x j v)(hy:X.width=o.K)(hX:X.manifest)(hz:Clutch X w o.a R.beta d x j V u z)
variable (hp:atomFoot S.ratio Q.halo X.B K i⊆U)
include H hz hp h hX hy
lemma ranged (he: ¬ dim X i) (hq:Brush j b 1 (fun y=> Canvas.point (J G) X.χ (bed X) (axis S i) (V y)) x):
    let A:= d+o.cap*X.t+2*Fintype.card G.ColorIndex; let t:= 4*(X.B:ℝ)*(v*royalty G); let D:= royalty G*(A*royalty G)*(1+(t+1+t))^j; let Y:=1+(b+D)
    let f' := facescale (edgesM S U X.B) w
    Brush j ( (Y+Y)*f') 1 (fun y=> argument (J G) (vary X (V y)) K i (u y)) x := by
  intro A t D Y f'
  let o':= axis S i; let Z:=homeFoot X K i
  have hR:= H.laws.data; have h₀:100≤X.B:=hR.room.sight.1; have hW : 1≤f':= (Flux.expenses ..).1
  let k:= (royalty G); have hk:1≤k:=royalty_ge _; have ht:0≤t:=by unfold t; have h₁:= h.pos; have h₂:= royalty_ge G; positivity
  have hA:0≤A:=by unfold A; have h₁:0<X.t:= hR.room.fiery; have h₂:=hR.safety.1; have h₃:=hz.price; positivity
  have hb:=hq.nonneg; have hD:0≤D:=by unfold D; have h:=royalty_ge G; positivity
  unfold argument; rw [add_mul]; apply Brush.pair (hq.climb ((le_mul_of_one_le_right hb hW).trans (mul_le_mul_of_nonneg_right (by unfold Y; linarith) (by positivity))) le_rfl)
  have hY:0 ≤ Y:=by unfold Y; positivity
  refine Brush.fold zero_le_one (by positivity) ?_; intro p
  by_cases hl: atEdge S p∈ Z ∧ distAt S p o'≤bed X; swap; · exact Brush.zi (Eventually.of_forall fun _=> if_neg hl) (by positivity) zero_le_one
  have ho y p : (vary X (V y)).Hot p ↔ X.Hot p:= Iff.rfl
  by_cases he':p∈F.trunks
  · apply Brush.zi _ (by positivity) zero_le_one; refine Eventually.of_forall fun t=> ?_
    change (if atEdge S p∈ Z ∧ distAt S p o'≤bed X then spinRow _ _ _ _ else 0)=0; rw [if_pos hl,spinRow,(vary X (V t)).on_trunk _ _ he',map_zero]
  have ht' : X.Hot p := far_active X.seeds F p (clear (v:=200*X.B) he (by obtain ⟨_,hh⟩:=hl; unfold o' bed distAt at hh; omega)) he'
  let r y:= carrier o' (V y) (atEdge S p)
  have hr: Brush j k t (fun y=> G.mat (r y)) x :=by
     apply (tour (carriage o' (atEdge S p)) o' h.pos h.atLink).climb le_rfl
     apply mul_le_mul_of_nonneg_right _ (mul_nonneg h.pos (zero_le_one.trans hk)); exact_mod_cast (SliceRows.mileage o' _).trans (Nat.mul_le_mul_left 4 (hl.2.trans (by unfold bed; omega)))
  have hv: p∈edgesM S U X.B:= mem_filter.mpr ⟨mem_univ _,fun y hy=> deckhead H hp _ hl.1 _ (hy.trans (by omega))⟩; have hP:= (decorate (g:=r) hr (ranges p hv H hX hy hz)).trim
  refine (hP.climb ((?_ : _=D*f').le.trans (mul_le_mul_of_nonneg_right (by unfold Y; linarith) (by positivity))) le_rfl).shimmy ?_; swap
  · refine Eventually.of_forall fun t=>?_ ; dsimp only; change (if atEdge S p∈ Z ∧ distAt S p o' ≤ bed X then _ else _) = _; rw [if_pos hl,spinRow,(vary X (V t)).at_hot _ _ ((ho _ _).2 ht')]; rfl
  unfold D A f'; ring
omit h H hy hX hp hz in
lemma coverBrush (U:Type*)[NormedAddCommGroup U][NormedSpace ℝ U]{F:U→ℝ}{a b c s :ℝ}{p:U}
    (h:Brush j a b F p) (hh: b ≤ c * s)(hc:1 ≤ c)(hs:0 ≤ s): Brush j (a * c^j) s F p:=by
  have ha:=h.nonneg; have hb:=h.pos; have ht:0≤c:=zero_le_one.trans hc
  refine ⟨h.smooth,hs,fun i hi=>?_⟩; calc
    _ ≤ a*b^i:= h.order i hi
    _ ≤ a*(c*s)^i:=by gcongr
    _ ≤ _:=by rw [mul_pow,← mul_assoc]; gcongr

omit h in
lemma barley {D Y M θ:ℝ} (hB:D≥0)(hV:1≤Y)(hA:1≤θ)(hp0:0≤M)(hT:Stamp T) (hF:Brush j 1 (D*θ) (fun y=>pane X o.a K i (u y)) x)
    (hy' :light X K i→ ¬ dim X i→ let f':=facescale (edgesM S U X.B) w
      Brush j ((Y+Y)*f') 1 (fun y=>argument (J G) (vary X (V y)) K i (u y)) x)
    (hu₁:light X K i→ Brush l ((K i.2.2).magnitude*M) 1 (latent K S i) 0) (a:ℝ):
    let A' := |stamp j l 1 (Y+Y)| * (2*(1+D)^j) * M
    let f':=facescale (edgesM S U X.B) w; let g x:= demesne R a o.a K i l F (vary X (V x)) (z x)- Kiln.flame H a K i l F (vary X (V x)) (z x)
    Brush j (Kiln.bill A' 0 a X.x K i*f'^(l+j)) θ g x ∧ (w∉ eerie X U (o.ξ/2) R.beta → g =ᶠ[𝓝 x] 0):=by
 intro A' f' g; let X' y:= vary X (V y); let Ξ:=atomFoot S.ratio Q.halo X.B K i
 have hθ:0≤θ:=zero_le_one.trans hA; have hf:1 ≤ f':=(Flux.expenses ..).1; have hh':= munch K i
 have hK :0 ≤ A':= by unfold A'; positivity
 by_cases he: light X K i ∧ ¬ dim X i; swap
 · have hy:g=ᶠ[𝓝 x] 0:= Eventually.of_forall fun y=>by dsimp [g,Kiln.flame,demesne]; rw [if_neg (show ¬ (light (vary X (V y)) K i ∧ ¬ dim (vary X (V y)) i) from he),sub_self]
   exact ⟨Brush.zi hy (mul_nonneg (positiveBill ..) (by positivity)) hθ,fun _=> hy⟩
 let t x:= pollen (J G) (X' x) K i l (u x); let u' x:= pane X o.a K i (u x); let H':= switch R K i (X.input (worldZ X R.beta w))
 have hs : g=ᶠ[𝓝 x] fun x=> a* (t x*(1-H'*u' x)):= by
   filter_upwards [hz.patch] with y hj; unfold g Kiln.flame demesne; dsimp only; rw [if_pos (show light (vary X (V y)) K i ∧ ¬ dim (vary X (V y)) i from he)]; unfold Kiln.lantern; rw [if_pos (show light (vary X (V y)) K i from he.1), if_neg (show ¬ dim (vary X (V y)) i from he.2), hz.moving]
   change a*t y-a* (t y * switch R K i ((X' y).input (u y)))*u' y=_
   by_cases hh:u' y=0; · rw [hh]; ring
   rw [show switch R K i _=H' from switching R K i (overlay (X:=X' y) _ _ hj hz.pulse hh)]; ring
 constructor; swap
 · intro ht; have hH : H'=1:= if_pos (bastion i H hX hy he.1 he.2 hp ht hT); filter_upwards [smallG U H hX hy hz ht,hs] with y he hy
   have he' : u' y =1:= Finset.prod_eq_one fun i hi=> he i (plaza_chapter hi (fun z hz x hx=> deckhead H hp z hz x (hx.trans (by have hz:100≤X.B:=H.laws.data.room.sight.1; omega))))
   rw [show g y=_ from hy,he',hH]; change _=0; ring
 rw [Kiln.bill,if_pos (show (K i.2.2).length≤ till X.x from he.1), abs_of_nonneg hK]
 let V₀:=Y+Y; let z₀:=(K i.2.2).magnitude*M; let H₀:= stamp j l 1 V₀
 have hu :1≤ V₀ := by unfold V₀; linarith
 have hZ:0≤ z₀:= mul_nonneg (munch ..) hp0
 have hp' : Brush j (z₀*(|H₀| * f'^(l+j))) 1 t x:= by
    apply (tactile (latent K S i) (hu₁ he.1) (hy' he.1 he.2) (one_le_mul_of_one_le_of_one_le hu hf)).climb _ le_rfl
    exact (upperShape z₀ _ _ l j hu hZ hf).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self H₀) (by positivity)) hZ)
 have hh : Brush j 2 (D*θ) (fun x=>1-H'*u' x) x:= by
    apply ((Brush.certified hF.pos (1:ℝ)).separating (hF.smul H')).climb _ le_rfl; unfold H' switch; split <;> norm_num
 refine (coverBrush E ((hp'.paints hh).smul a) (c:=1+D) (by linarith : 1+D*θ ≤(1+D)*θ) (by linarith) hθ).climb ?_ le_rfl|>.shimmy hs
 apply le_of_eq; unfold A' z₀ H₀ V₀; rw [Real.norm_eq_abs]; ring
end YM.LocalTaylorR2.Exponent
