import YM.LocalTaylorR2.Pavilion.Install
/-!
 # Mat log replica Taylor, reduced board shell of determinant. Keep color stencil exact and inverse over analytic chart. This occurrence is NOT the Fourier Wick coefficient. `drip` as in principal. Curvature (not Full matrix log) at true rooted sectors. Angular cancellations on all. Conditioning cost. -/
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
open Progress.StationaryScenes.Green

def stag (X:Coat T F)(i:Bond f)(u:ZipP G c f) := (Pavilion.drip X u).condensation i
def gainV (p:ℕ)(X:Coat T F)(i:Bond f):= if voyage X.seeds (200*X.B) i then 0 else blockTaylor p (stag X i) (Pavilion.pitch (Canvas.primary G) X (atEdge S i))

lemma colonial (i:Bond f) (K : Zone X X' (atEdge S i) (24*X.B)) (p:Room P S T X.x): X.condensation i=X'.condensation i:=by
  cases isEmpty_or_nonempty G.ColorIndex with
  | inl h=>simp [Coat.condensation,Batch.joint]
  | inr h=>obtain ⟨z⟩:=h; exact K.condensates p (i,z) rfl (by omega)
lemma helm (i:Bond f)(x:ZipP G c f)(g: Site c→ G.El)(p:Room P S T X.x)(h:¬ Inside (atEdge S i) X.seeds (200*X.B))(he:Hue X) (hp:AgreeNear id (atEdge S i) (24*X.B) (gauge g X.V) (increment 1 x.1)): stag X i x=X.condensation i:=by
  let Y:=sluice X g; let K:=dry Y x; have hx:X.condensation i=Y.condensation i := ((Stained.royals X g p.accepted he).2.2 i).symm
  rw [hx]; change K.condensation i=Y.condensation i
  symm
  refine colonial i ⟨rfl,rfl,rfl,fun v hv=> ?_, fun _ _=>rfl,hp,fun _ _=>rfl,fun _ _=> rfl⟩ p
  exact iff_of_false (fun hz=> h (Lattice.halo_spec.mpr ⟨v,hz,(separation_comm ..).trans_le (show separation (atEdge S i) v≤ _ from hv.trans (by change 24*X.B≤200*X.B; omega))⟩)) (fun hy=> Y.blank_no v 0 (halo_subset _ _ hy))

lemma bazaar (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(o:Target.Order G W)(v: ℝ→ℝ)(L:Side)(V:Rate G L (-(1/2)) v)(he:∀ᶠ x in atTop, 0≤v x)(D:Patch)(hD:D.Branches P.bind G) (k:ℕ)(hp:1≤k) : ∃ t, Rate G L 0 t ∧ ∀ᶠ s in atTop, ∀ (c f: Side) (S: StepData c f)(T: Tube G S)(R:Rep G f)(μ C:ℝ)(_H : Cash W s μ L Q o C T R) (F:Forest S.ratio) (X:Coat T F) (i : Bond f), S.patch=D→ X.x=s → X.width=o.K → ∀ (u:ZipP G c f), ‖u‖≤v s → Hue (Pavilion.drip X u) ∧ Brush k (|t s|) 1 (stag X i) u:=by
  obtain ⟨K,e,q,y,B,hK,he,hq,-,hB,hY⟩:= quenched P L D hD k hp V he o.eta o.gap o.ample o.f
  let a:= min q 1; let A := max K 1; have hA:Torch e a A:=⟨he,lt_min hq zero_lt_one,le_max_right .., min_le_right ..⟩
  let m:=tubularPrice G L; let Z:=(Fintype.card G.ColorIndex:ℝ)*((o.ample+1)*payE o.eta o.gap o.ample m)
  let v' x:= Z+crownP k (radiusB x) m G e a A K
  refine ⟨fun x=> v' x*(1+(B x+driftP k (B x)))^k,?_,?_⟩
  · have hf:Rate G L 0 v':=(Rate.const _).add (((polynomial G L k m _ _).mul_left _).mul_left (Fintype.card G.ColorIndex))
    simpa only [zero_mul,add_zero] using! hf.mul (((Rate.const 1).add (hB.add (hB.mul_left _))).pow k)
  filter_upwards [hY] with x hx c f S T R μ C H F X i hS ht hv u hu
  let D:= X.shutter; let Y z:=(Pavilion.drip X z).plate; subst x
  have hR:= H.laws.data.localP F X.blank rfl hv (X.bowed (temp_nonneg _))|>.sails.scale
  obtain ⟨hh,hQ,-⟩:=hx _ _ S T hS H.laws.data.funds F X rfl hR u hu
  have he : Allow (Y u) (along S) m e a A:= ⟨hh.census,hh.symmetry, hA.hot,hA.spans,(zero_lt_one.trans_le hA.hQ), Control.pricing hh.price le_rfl (le_max_left ..), fun i=> (mul_le_mul_of_nonneg_right (min_le_left ..) (nn i)).trans (hh.ground i)⟩
  refine ⟨Pulse.vibrate D _ he hA,?_⟩
  have hq' : Tablet k 0 K (B X.x) Y (along S) (along S) u := hQ.tilt le_rfl le_rfl le_rfl hA.hot.le
  have hf:= plotsB D Y he hq' he.weather.1.le hA i
  let z:= Batch.joint X.blank.plate D i; have hp:= Batch.nearBase D o.f hR i
  exact ((semi (((Brush.certified hf.pos z).climb hp le_rfl).separating hf)).trim).climb (le_abs_self _) le_rfl
lemma storesD (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(o:Target.Order G W)(v d: ℝ→ℝ)(L:Side)(V:Rate G L (-(1/2)) v)(he:∀ᶠ x in atTop, 0≤v x)(D:Patch)(hD:D.Branches P.bind G) (χ:Chi)(p j:ℕ) : ∃ t, Rate G L (-(p+1)/2) t ∧ ∀ᶠ s in atTop, ∀ (c f: Side) (S: StepData c f)(T: Tube G S)(R:Rep G f)(μ C:ℝ)(H : Cash W s μ L Q o C T R) (i : Bond f), S.patch=D → Sees H j (v s) (d s) χ (fun _ X _=> X.undercurrent i-gainV p X i) (|t s|) 1 := by
  obtain ⟨B,hB,hY⟩:= Basecamp.tenant G L P (Canvas.primary G) j V he
  let Z x:= B x+B x; have hz:Rate G L (-(1/2)) Z := hB.add hB; have hf : ∀ᶠ x in atTop,0 < Z x:= hY.mono fun s hs=>add_pos hs.1 hs.1
  obtain ⟨A,hA,hT⟩:=bazaar P Q o Z L hz (hf.mono fun _ hv=>hv.le) D hD (j+p+1) (by omega)
  have hL:= Glass.portal P D L hD j χ V he o.K o.γ W o.indexPay o.f
  refine ⟨fun x=> ((j.factorial*|A x|)*((1+((1+1)*1):ℝ))^j*Z x^(p+1)),?_,?_⟩
  · have hΩ : Rate G L 0 (fun x=> (j.factorial*|A x|)*((1+((1+1)*1):ℝ))^j):= ((hA.compare (v:=fun x=> |A x|) (Eventually.of_forall fun z=> (abs_abs _).le)).mul_left _).mul_right _
    convert (hΩ.mul (hz.pow (p+1))) using 1; push_cast; ring
  filter_upwards [hY,hT,hL,hf,hz.below (by norm_num) 1 zero_lt_one] with x hp hv h hu hh c f S T R μ C H i he E _ _ _ F X V u z y w hs hw hΨ hχ hM hC
  subst x; let g:=Canvas.primary G; let R' t:=vary X (V t); let o':= atEdge S i; let t x:= Pavilion.pitch g (R' x) o'
  have hR:= H.laws.data; let r:= hR.room
  let p':=hR.localP F X rfl hw hΨ; by_cases ht:voyage X.seeds (200*X.B) i
  · exact Brush.zi (Eventually.of_forall fun u=> by change (if voyage X.seeds (200*X.B) i then 0 else _) -(if voyage X.seeds (200*X.B) i then 0 else _)= (0:ℝ); simp only [if_pos ht,sub_self]) (abs_nonneg _) zero_le_one
  have hμ : ¬ Inside o' X.seeds (200*X.B):= without i X.seeds ht
  obtain ⟨h₁,h₂⟩:= hp.2 c f S T hR.funds.length_eq r (24*X.B) (by unfold Coat.B; omega) E V y X.χ o' hM (by rw [hC.atV]; exact (clean_far _ X.V hΨ hμ).shrink (by rw [separation_self]; have he:100≤X.B:=r.sight.1; change 0+(40*X.B+1)≤200*X.B; omega))
  have hz: Brush j (Z X.x) 1 t y:= Brush.pair h₁ ((Brush.certified zero_le_one (0:Directions G _)).climb (by rw [norm_zero]; exact hp.1.le) le_rfl)
  refine (((Mesh.priced hu ((le_abs_self _).trans hh) (fun u hu=> (hv _ _ S T R μ C H F X i he rfl hw u hu).2) hz)).climb (le_abs_self _) le_rfl).shimmy ?_
  have he' := Stained.eventual_hue (h c f S T he hR.funds hR.access F X hw hχ rfl p' E V y hC.atV hM) p'.sails
  filter_upwards [h₂,he'] with u hu hT; change (if voyage X.seeds (200*X.B) i then 0 else (R' u).condensation i) -(if voyage X.seeds (200*X.B) i then 0 else blockTaylor p (stag X i) (t u))= _
  rw [if_neg ht,if_neg ht, ← helm (X:=R' u) i (t u) (carrier o' (V u)) r hμ hT hu]; rfl
end YM.LocalTaylorR2.Pavilion
