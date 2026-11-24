import YM.Contacts.Milling.Forge
/-! Seasonal conditional report for well-rooted formal jets. Per-torus exact before accounting. -/
noncomputable section
namespace YM.Contacts.Milling.Forge
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open PertExtension.GaussianScore FreeResolvent PhysicalNext.RankCovariance Pulse.Form
open PertExtension.Chart Kale Spark House Radial Ion
open scoped Topology ContDiff BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side} {S:StepData c f} {X E α:Type}{k e r:ℕ}
local notation "T" => planting S.ratio S.patch.odd_side
local notation "κ" => (AxisChart G T)
local notation "Ξ" => insertion (plant T (G:=G))
local notation "Λ" => Link G f
local notation "Δ" => Link G c
local notation "ψ" => Yard G S
local notation "Ω" => House.Dir (Yard G S)
def hoist (G: α→ X→ℝ)(F: Pulse.Field (Fin r) α):Pulse.Field (Fin r) X:= printRun (allAt (fun _=> G) F)
section lin
variable [Fintype α][Fintype X]
lemma hoist_read (R: Matrix α X ℝ) (F: Pulse.Field (Fin r) α) (x:X→ℝ): design (hoist R F) x= design F (R*ᵥ x):= by
   rw [hoist, design, verse_print,← design]; simp only [design_spec,allAt,tsum_fintype, Finset.sum_mul,Matrix.mulVec,dotProduct]; rw [Finset.sum_comm]; apply sum_congr ?_; swap; · congr!
   intro j _; rw [Fintype.prod_sum,mul_sum]; apply sum_congr ?_; swap; · congr!
   intro k _; rw [prod_mul_distrib,mul_assoc]
end lin
lemma hoist_shape {G:α→ X→ℝ} {F : Pulse.Field (Fin r) α} : Poem (hoist G F):= print_even _
@[simp] lemma hoist_empty (G:α→X→ℝ) : hoist G (0:Pulse.Field (Fin r) α)=0:= by unfold hoist; rw [show allAt (ι:=Fin r) _ _=_ from (show allAt (fun _:Fin r=>G) (0: Field (Fin r) α)=0 from funext fun i=> by simp [allAt])]; exact print_zero

def circ (G: Gauge)(n:Side)(H:FreeResolvent.FaceRow)(r:ℕ): Pulse.Field (Fin r) (Lines G n 1):= if h:r=2 then takeRank h.symm ((2:ℝ)⁻¹ • printRun (both (spindle G n H))) else 0
lemma circ_read (G:Gauge)(n:Side)(H:FreeResolvent.FaceRow)(x:Link G n): design (circ G n H 2) x=x ⬝ᵥ (spindle G n H*ᵥ x)/2:= by
  rw [circ,dif_pos rfl]; unfold takeRank; dsimp only; rw [design,verse_scale',verse_print,map_smul,← design,design_spec]; let I:= Lines G n 1
  let e : I×I≃(Fin 2→ I):= (Equiv.prodCongr (Equiv.refl I) (Equiv.funUnique (Fin 1) I).symm).trans (Fin.consEquiv (n:=1) (fun _=>I)); let Z (p:Fin 2→I):= both (spindle G n H) p*∏ i,x (p i); calc
    _ = (2:ℝ)⁻¹ • ∑ a: (Fin 2→I), Z a := by congr! <;> try rfl
    _ = _ := ?_
  rw [← Equiv.sum_comp e Z,Fintype.sum_prod_type]; simp only [smul_eq_mul,dotProduct,Matrix.mulVec,dotProduct,mul_sum,Finset.sum_div]; apply sum_congr ?_; swap; · congr!
  intro i _; apply sum_congr ?_; swap; · congr!
  intro j _; unfold Z; rw [Fin.prod_univ_two]; change _* (spindle G n H i j*(x i*x j))=_; ring
lemma circ_shape (i:ℕ){H:FreeResolvent.FaceRow}: Poem (circ G n H i):= by
  unfold circ; split
  next e=> subst i; apply Poem.scale; exact print_even _
  exact Poem.empty -- indent
abbrev shave (S:StepData c f)(G:Gauge) : Matrix (Lines G f 1) (Yard G S) ℝ:= (insertion (offspring S))ᵀ
lemma shaved (x:Ω): shave S G *ᵥ x=teen S x:= by funext i; simp [shave,Matrix.mulVec,dotProduct,FreeResolvent.insertion]; rw [Finset.sum_eq_single (offspring S i)]; rw [if_pos rfl]; rfl; exact fun a _ h=> if_neg (fun e=> h e.symm); simp
-- lift vote generic syntax behind Primitive
variable (S G)
def compote {α:Type} (q:Field (Fin r) α)(K H : Field (Fin r) α)(e:ℕ):Field (Fin r) α:= if e=0 then 0 else (if r=e then K else 0) + -( (if r=e+2 then H else 0) + q)
def banners (Q:ChartRatio G)(F:House (Lines G f 1)): House (Yard G S):= fun e r=> compote (hoist (shave S G) (F e r)) (sparkling S Q r) (pilotWord S G r) e -- pos log exponent
variable {S G}
lemma compote_seed {α:Type}{F P H : Field (Fin r) α}(h:Poem F)(hp:Poem P)(he:Poem H): Poem (compote F P H e):= by
  unfold compote; split; exact Poem.empty; apply Poem.add
  · split; exact hp; exact Poem.empty
  refine Poem.minus (Poem.add ?_ h); split; exact he; exact Poem.empty
lemma compote_zero {α:Type}{F P H : Field (Fin r) α}(hp:e=0∨e+2<r) (he:e+2<r → F=0) : compote F P H e=0:= by unfold compote; split; rfl; rw [if_neg (by omega),if_neg (by omega),he (by omega)]; simp
variable {Q: ChartRatio G}{F:House (Lines G f 1)} {Y:ℝ→Config G f→ℝ}
lemma banner_snug (h:Shaped F) : Snug (banners G S Q F):= by
   refine ⟨fun i r=> compote_seed hoist_shape (print_even _) (print_even _),fun e r hp=> compote_zero hp ?_⟩; intro ht; rw [h.thin e r (.inr ht),hoist_empty]
section
variable [Fintype α] (u:House.Dir α)
lemma parcel (e:ℕ)(u:House.Dir α)(X:House α): MvPolynomial.aeval u (PowerSeries.coeff e (clouds X))= ∑ r∈Finset.range (e+3),design (X e r) u:= by simp only [clouds,PowerSeries.coeff_mk,stage,map_sum]; rfl
lemma parcel_add (F Q : Pulse.Field (Fin r) α): design (F+Q) u=design F u+design Q u:= by rw [design,verse_add,map_add]; rfl
lemma parcel_neg (F: Pulse.Field (Fin r) α): design (-F) u= -design F u:= by rw [← neg_one_smul ℝ F,design,verse_scale',map_smul, neg_one_smul]; rfl
@[simp] lemma parcel_nil: design (0:Pulse.Field (Fin r) α) u=0:= by simp [design]
lemma parcel_bill {F P H : Field (Fin r) α} (e:ℕ)(h:e≠0): design (compote F P H e) u= (if r=e then design P u else 0)+ -((if r=e+2 then design H u else 0) + design F u):= by unfold compote; rw [if_neg h]; split_ifs <;> simp [parcel_add,parcel_neg]
end
lemma banners_ink (x:Ω)(hQ:Package Y F k)(h:S.patch.Branches S.kernel G)(hu:LocalRatio Q){e:ℕ}(he:e+2<k): MvPolynomial.aeval x (PowerSeries.coeff e (clouds (banners G S Q F)))=Radial.layers (tribute Q S Y) e (1,x):= by
   rw [parcel]; by_cases ht:e=0; · subst e; simp [Radial.layers,banners,compote]
   unfold banners Radial.layers; simp_rw [parcel_bill x e ht,hoist_read,shaved,sum_add_distrib,sum_neg_distrib]; change _= -jet (tribute Q S Y) _ _+_; simp only [sum_ite_eq',sum_add_distrib, Finset.mem_range,if_pos (show e<e+3 from by omega), if_pos (show e+2<e+3 from by omega),tribute_jet hQ h hu _ he,if_pos (show 2 ≤ e+2 from by omega),one_pow,one_mul,if_neg ht,Nat.add_sub_cancel]
   rw [show ace S (1,x)=(1,teen S x) from rfl, House.stamp F k e he,← hot_craft h,←gold_spec hu]; simp only [terrace,stage,map_sum, design]; ring_nf; rw [sub_right_comm]; congr!
-- Xgress measured under both fibre & histogram
def attendP (S:StepData c f)(G:Gauge)(i:Yard G S) : Module.Dual ℝ (AxisChart G (planting S.ratio S.patch.odd_side)):= i.2.elim (fun _=>0) (fun q=> attend S (planting S.ratio S.patch.odd_side) ((splitCo S.ratio (Dye G)).symm (i.1,q)))
def sky (S:StepData c f)(G:Gauge)(M:Matrix (Lines G f 1) (Lines G c 1) ℝ): Matrix (Yard G S) (Lines G c 1) ℝ:= Matrix.of fun i:Yard G S=> i.2.elim (fun q=> (1:Matrix _ _ ℝ) (i.1,q)) (fun r=>M ((splitCo S.ratio (Dye G)).symm (i.1,r)))
lemma sky_pass (M:Matrix (Lines G f 1) (Lines G c 1) ℝ)(x:Δ): sky S G M*ᵥ x=weave S (x,M*ᵥ x):= by funext i; rcases i with ⟨i,q|q⟩; exact congr_fun (Matrix.one_mulVec x) (i,q); rfl
variable {P H:FreeResolvent.FaceRow}{R: Astro G S}{d:ℝ}
def veer (S:StepData c f)(G:Gauge)(H:FreeResolvent.FaceRow) (i j:Yard G S):ℝ:= i.2.elim (fun _=>0) (fun a=> j.2.elim (fun _=>0) fun b=> covariance G S (planting S.ratio S.patch.odd_side) H ((splitCo S.ratio (Dye G)).symm (i.1,a)) ((splitCo S.ratio (Dye G)).symm (j.1,b)))
lemma veers (h:Beam S G R P H d) : (fun i j=> (court h).wick (attendP S G i) (attendP S G j))= veer S G P := by
   funext ⟨x,a⟩ ⟨z,b⟩; rcases a with a|a <;> rcases b with b|b
   · rfl
   · change attend S T ( _ ) ((court h).inverse 0)=0; rw [map_zero,map_zero] -- test
   · rfl
   exact wick_rises h _ _
lemma firesP (y:κ) : (fun i=> attendP S G i y)= weave S (0,stash S T y):= by funext ⟨i,a⟩; rcases a with a|a<;> rfl
def mintage {α β:Type}(A:Rack α)(G:β→α→ℝ) (g:β→β→ℝ)(Z:House β): House α := fun e r=> if e=0 then A r else - hoist G (massaged g Z e r)
lemma massaged_shape {α:Type}{g:α→α→ℝ}{F: House α}(h:Snug F): Snug (massaged g F) := ⟨fun _ _=> Poem.sum _ (fun i _=>(h.bounded g i).poems _ _),fun e r hp=> Finset.sum_eq_zero (fun i _=>(h.bounded g i).thin _ _ hp)⟩
-- finite includes scalar exit
variable (S)
def vault (Q:ChartRatio G) (F:House (Lines G f 1))(R:Astro G S)(P H:FreeResolvent.FaceRow) := mintage (circ G c H) (sky S G (atr G S R)) (veer S G P) (banners G S Q F)
lemma vault_beams {S:StepData c f} {R:Astro G S}(h:Shaped F): Chest (vault S Q F R P H) H:= by
   let K:= sky S G (atr G S R); let g:=veer S G P; let A:=banners G S Q F; let Y:=vault S Q F R P H; have hp:= massaged_shape (g:=g) (banner_snug (S:=S) (Q:=Q) h)
   constructor
   · constructor
     · intro e r; unfold vault mintage; split; apply circ_shape; exact Poem.minus hoist_shape
     intro e r he; unfold vault mintage; split
     next e=> rw [circ,dif_neg (by omega)]
     next a=> rw [hp.thin _ _ (.inr (by omega)),hoist_empty,neg_zero]
   intro x; unfold vault mintage; rw [if_pos rfl,circ_read]
lemma parcel_forward {α β:Type}[Fintype α][Fintype β](M:Rack α)(R:Matrix β α ℝ)(v: House.Dir α)(g:β→β→ℝ)(X:House β)(h:Snug X)(he:e+2<k) : MvPolynomial.aeval (R*ᵥ v) (PowerSeries.coeff e (clouds (massaged g X)))=Radial.layers (swell (mintage M R g X) k) e (1,v):= by
   rw [parcel]; unfold Radial.layers; by_cases ht:e=0; · subst e; rw [Finset.sum_eq_zero (fun i _=> by rw [(massaged_shape h).thin _ _ (Or.inl rfl),parcel_nil])]; simp
   rw [if_neg ht,House.stamp _ _ _ he,terrace, stage,map_sum]; let K:= massaged g X; change _=-(∑ r∈Finset.range (e+3), design (mintage M R g X e r) v)+0; simp_rw [mintage,if_neg ht, parcel_neg,hoist_read]; rw [sum_neg_distrib,neg_neg,add_zero]
variable {S}
lemma targets (Q : ChartRatio G){P H:FreeResolvent.FaceRow}{R: Astro G S}{d:ℝ}(hQ: Package Y F (k+3))(hP:Chest F P)(H_Q:LocalRatio Q)(h:Beam S G R P H d):
   Arc (court h) (fun v:cap G c=> (sky S G (atr G S R))*ᵥ v.2) (attendP S G) (banners G S Q F) ((tribute Q S Y) ∘ inked S) (swell (vault S Q F R P H) (k+3)) ((course S T R) ∘ Prod.snd) k {z:cap G c | z.1=1} := by
  let C:=court h; let a:=tribute Q S Y; let f:= a ∘ inked S; let p:= vault S Q F R P H; let y:=swell p (k+3); let M:=course S T R; let R':= atr G S R; have ha:= tribute_ana hQ h.light.1 H_Q; let K:= sky S G R'; let g: cap G c→ κ :=M ∘ Prod.snd; let χ:=attendP S G; have hp: Chest p H:= vault_beams (Q:=Q) hP.toShaped
  constructor
  · refine ⟨fun x z=> ?_, M.continuous.comp continuous_snd⟩
    let w:= stash S T ((course S T R) x.2+z); let X:=weave S (x.2,w); change jet f 2 (_,M x.2+z)=jet y 2 x+ _; rw [show jet f 2 (x,M x.2+z) = jet a 2 (x.1,X) from woven ha (inked S) (x,M x.2+z) 2]; unfold a y; rw [tribute_beams hQ h.light.1 H_Q hP (by omega), theme hp _ (by omega)]; dsimp only; rw [spice X h.light.1]; have ht: w= R'*ᵥ x.2+ stash S T z:= by unfold w; rw [map_add,gather_flow h]
    erw [show teen S X=w from blooms _, show Garf.mature S X=x.2 from grow _,ht]; change _=_ +( (tribe S T z) ⬝ᵥ (_*ᵥ (tribe S T z)))/2; rw [← add_div,← add_div]; apply congr_arg (·/ (2:ℝ)) ((shift_physical h x.2 (tribe S T z)).trans (add_comm ..))
   -- identity apply shift
  · intro i hi x hx z; rw [mark]; let w:= weave S (x.2,stash S T (M x.2+z)); have hh: inked S (x,M x.2+z)=(1,w):= Prod.ext hx rfl
    change MvPolynomial.aeval (K *ᵥ x.2 + _) _=Radial.layers f i (x,M x.2+z); rw [show K*ᵥ x.2 + (fun i=> attendP S G i z)=w from ?_, banners_ink w hQ h.light.1 H_Q (by omega)]; rotate_left
    · unfold w K M; rw [firesP,sky_pass,map_add,gather_flow h, ← map_add]; congr 2 <;> simp [R']
    unfold Radial.layers f; rw [woven ha,woven ha,hh]
  intro i hi x hx; rcases x with ⟨t,v⟩; change t=1 at hx; subst t; rw [veers h]; exact parcel_forward _ (sky S G (atr G S R)) v _ (banners G S Q F) (banner_snug hP.toShaped) (by omega)
lemma franchise (Hq:LocalRatio Q)(hQ:Package Y F (k+3))(hP:Chest F P)(h:Beam S G R P H d):
   Sight (runner (visitor S Y) T) (swell (vault S Q F R P H) (k+3)) (jacobian (U:=(T).Free) Q 0 * measureT (court h) (tangent G (T).Free)) k:= by
     have hs:= tribute_ana hQ h.light.1 Hq; let μ:=tribute Q S Y; let g:= μ ∘ inked S; have ht:= tribute_wanted hQ h.light.1 Hq (by omega); have hg: Radial.Stationary g:= ⟨(starts μ hs (inked S)).contDiffAt,(congr_arg μ ((inked S).map_zero)).trans ht.base0,fun i=> (woven hs (inked S) i 1).trans (ht.base1 _)⟩; exact shelterbelt Hq (foster hQ h.light.1 Hq) (targets Q hQ hP Hq h) hg ((plan_m hQ h.light.1 Q Hq).comp (inked S).continuous.measurable) (spectrum ..) (banner_snug hP.toShaped)
lemma passport (Hq:LocalRatio Q)(hi:sealed F (k+3))(hP:Chest F P)(h:Beam S G R P H d) : sealed (vault S Q F R P H) (k+3) :=
   wind_guard _ T S.patch.odd_side (franchise Hq (candles F _ hi) hP h) (seen (candles F _ hi) h.light.1)
end YM.Contacts.Milling.Forge
