import YM.LocalTaylorR2.Pavilion.Erased
/-!
 # Lease precision on actual Root. Argument Taylor of even the Gaussian mean term at the same shifted mass/width/ϑ and stencil. Cost through normal power plus all transmission/stretch. No Roller assumption supplied at approximating field (fields along this interpolation needn't be *manifest*).

 Use `pitch` (24B) and canonical `tenant` estimate, blank spine as proved actual in this window. Factor costs already account for extraction of scalar β.
 -/
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

lemma landV (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(o:Target.Order G W)(v: ℝ→ℝ)(L:Side)(V:Rate G L (-(1/2)) v)(he:∀ᶠ x in atTop, 0≤v x)(D:Patch)(hD:D.Branches P.bind G) (k:ℕ)(hp:1≤k) : ∃ t, Rate G L 0 t ∧ ∀ᶠ s in atTop, ∀ (c f: Side) (S: StepData c f)(T: Tube G S)(R:Rep G f)(μ C:ℝ)(_H : Cash W s μ L Q o C T R) (F:Forest S.ratio) (X:Coat T F) (i : Coat.Stream c f), S.patch=D→ X.x=s → X.width=o.K → ∀ (u:ZipP G c f), ‖u‖≤v s → Brush k (|t s|) 1 (meanV X i) u:=by
  obtain ⟨Z,hZ,hQ⟩:= abridge P L D hD k hp V he o.f
  refine ⟨fun x=>2*((|Z x| *|Z x|)*(1+(1+1):ℝ)^k),?_,?_⟩
  · have hU : Rate G L 0 (fun x=> |Z x|):= hZ.compare (Eventually.of_forall fun x=>(abs_abs _).le)
    convert (((hU.mul hU).mul_right _).mul_left 2) using 1; ring
  filter_upwards [hQ] with x hx c f S T R μ C H F X i hD hX hv u ht
  let Z' v:= drip X v; let J := |Z x|; have hJ:= abs_nonneg (Z x)
  let K:ℝ:=(J*J)*(1+(1+1):ℝ)^k; have hK:0≤K:=mul_nonneg (mul_nonneg hJ hJ) (pow_nonneg (by norm_num) _)
  have hf (u): ¬ Inside (rowSite S i) (Z' u).seeds (200*(Z' u).B):= X.blank_no (rowSite S i) (200*X.B)
  unfold meanV; simp_rw [uncloud (drip X _) _ (hf _)]
  refine (Brush.spree _ _ (fun _=>K) zero_le_one (fun a (_:a∈ parents i.2)=>?_)).climb ?_ le_rfl
  · have he:= hx c f S T hD H.laws.data.funds F (X.wrapY 1) hX
      (H.laws.data.localP _ (X.wrapY 1).blank hX hv ((X.wrapY 1).bowed (temp_nonneg _))).sails.scale (i.1,a) u ht
    exact (semi (squared (he.climb (le_abs_self _) le_rfl))).trim
  rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right _ hK).trans (le_abs_self _)
  exact_mod_cast (show (parents i.2).card ≤ 2 by rcases i with ⟨i,k|k|k⟩ <;> simp [parents])
def delta (p:ℕ)(i:Coat.Stream c f)(R:Rep G f)(Z: Coat T F) := -R.beta*Raw.orientation*(voltageV Z i - tune (Canvas.primary G) Z i p)
lemma rootpay (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(o:Target.Order G W)(v d: ℝ→ℝ)(L:Side)(V:Rate G L (-(1/2)) v)(he:∀ᶠ x in atTop, 0≤v x)(D:Patch)(hD:D.Branches P.bind G) (χ:Chi)(p j:ℕ) : ∃ t, Rate G L (-(p+1)/2) t ∧ ∀ᶠ s in atTop, ∀ (c f: Side) (S: StepData c f)(T: Tube G S)(R:Rep G f)(μ C:ℝ)(H : Cash W s μ L Q o C T R) (i : Coat.Stream c f), S.patch=D → Sees H j (v s) (d s) χ (fun _ X _=> Pavilion.delta (p+2) i R X) (|t s|) 1:=by
  let J:= Canvas.primary G; obtain ⟨Z,hZ,hY⟩:= Basecamp.tenant G L P J j V he
  let K s:= Z s+Z s; have hf:= hZ.add hZ
  have hp : ∀ᶠ s in atTop, 0<K s:= hY.mono fun s hs=> add_pos hs.1 hs.1
  obtain ⟨M,hM,hP⟩:= landV P Q o K L hf (hp.mono fun _ hp=> hp.le) D hD (j+(p+2)+1) (by omega)
  let A s:= (j.factorial*|M s|)*((1+((1+1)*1):ℝ))^j*K s^(p+2+1)
  refine ⟨fun s=> (2*betaF G s L)*A s, ?_,?_⟩
  · have hΩ : Rate G L 0 (fun s=> (j.factorial*|M s|)*((1+((1+1)*1):ℝ))^j):= ((hM.compare (v:=fun x=> |M x|) (Eventually.of_forall fun z=> (abs_abs _).le)).mul_left _).mul_right _
    convert ((Rate.hat.mul_left 2).mul (hΩ.mul (hf.pow (p+2+1)))) using 1; push_cast; ring
  filter_upwards [hY,hP,hp,hf.below (by norm_num) 1 zero_lt_one] with x hk hF hψ hM c f S T R μ C H i hS E _ _ _ F X V u z y w hX hW hm hχ ht hu
  let Wm t:= vary X (V t); have hw:= H.laws.data; have hQ:= hw.room; have hL:= hw.funds.length_eq; let o':= rowSite S i
  by_cases hs : Inside o' X.seeds (200*X.B); · exact Brush.zi (Eventually.of_forall (fun t=> by change Pavilion.delta _ i R (Wm t)=0; unfold Pavilion.delta; rw [tune,voltageV,if_pos (show Inside _ (Wm t).seeds (200*(Wm t).B) from hs), if_pos (show Inside _ (Wm t).seeds (200*(Wm t).B) from hs), sub_self,mul_zero])) (abs_nonneg _) zero_le_one
  subst x χ; let Lf t:= Pavilion.pitch J (Wm t) o'; let D':=meanV X i; have hf t: meanV (Wm t) i= D':= rfl
  obtain ⟨hp,hh⟩:= hk.2 c f S T hL hQ (24*X.B) (by unfold Coat.B; omega) E V y X.χ o' ht (by
    rw [hu.atV]; exact (clean_far X.seeds X.V hm hs).shrink (by rw [separation_self]; have hx:100≤X.B:=hQ.sight.1; change 0+(40*X.B+1) ≤200*X.B; omega))
  have hg : Brush j (K X.x) 1 Lf y:= Brush.pair hp ((Brush.certified zero_le_one (0:Directions G _)).climb (by rw [norm_zero]; exact hk.1.le) le_rfl)
  have hx:= H.laws.intake; have hB := Mesh.priced (d:=p+2) hψ ((le_abs_self _).trans hM) (fun u hu=> hF c f S T R μ C H F X i hS rfl hW u hu) hg
  refine ((hB.smul (-R.beta*Raw.orientation)).climb ?_ le_rfl).shimmy ?_
  · rw [norm_mul,norm_neg,Real.norm_of_nonneg hx.positive.le,Real.norm_of_nonneg Raw.orientation_range.1.le]; apply ((mul_le_mul_of_nonneg_right _ hB.nonneg)).trans (le_abs_self _)
    exact ((mul_le_of_le_one_right hx.positive.le Raw.orientation_range.2).trans (show R.beta≤ _ from (by rw [← hL]; exact hx.window.2)))
  filter_upwards [hh] with t hy; let L:=carrier o' (V t); change Pavilion.delta (p+2) i R (Wm t)= -R.beta*Raw.orientation*((D'-blockTaylor (p+2) D') (Lf t))
  unfold Pavilion.delta tune voltageV; rw [if_neg (show ¬Inside (rowSite S i) (Wm t).seeds (200*(Wm t).B) from hs),if_neg (show ¬Inside (rowSite S i) (Wm t).seeds (200*(Wm t).B) from hs), ← winded (Wm t) (Lf t) i hQ L (show ShellAccess S G X.x W X.width o.γ from by rw [hW]; exact hw.access) hs hy,hf]; rfl
end YM.LocalTaylorR2.Pavilion
