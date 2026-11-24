import YM.LocalLTE.Roost.Blades
/-! Primitive short=stream bulbs on all `v` excursion. Count in μ Canvas lower order. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
variable {v z r W s y η γ B : ℝ} {j n m : ℕ}
local notation "E"=> Disk G c
local notation "E₀"=> ZipP G c f
-- displacement pairing high.
section
variable (X:Coat T F)
def orbitΛ (s:Signed)(x:E₀): E₀ := (displacement s x.1 (1:Config G c), displacement s x.2 (replica S.ratio (increment (1:Config G c) x.1)))
lemma orbitingΛ (s:Signed)(x:E₀): ‖orbitΛ (S:=S) s x‖≤ ‖x‖:= max_le ((displacement_bounded s 1 _).trans (le_max_left ..)) ((displacement_bounded s _ _).trans (le_max_right ..))
lemma ceilings {P:Teller G}(D : Patch)(hd:D.Branches P.bind G)(j:ℕ):∃ A r:ℝ,0<r∧ ∀ (c f:Side)(S:StepData c f)(T:Tube G S), P.Funds S T → S.patch=D →∀ (s:Signed)(x:ZipP G c f),‖x‖≤r→ Brush j A 1 (orbitΛ (S:=S) s) x:=by
  obtain ⟨r,v,hr,hr',hv,hX⟩:= Frond.dressed P D hd j
  let a:= royalty G; have hh:1≤a:=royalty_ge G
  let V:=v+1+v; let k:=a*(1*a); have h₁:0 ≤ k:=by unfold k; positivity
  refine ⟨(k+k)*(1+V)^j,r,hr,?_⟩; intro c f S T h hs s x hx
  have ht:Brush j 1 1 (fun v:ZipP G c f=>v.snd) x:= linearB (ContinuousLinearMap.snd ℝ (Directions G c) (Directions G f)) ((le_max_right ..).trans (hx.trans hr')) (by rw [one_mul]; exact ContinuousLinearMap.norm_snd_le ..) zero_le_one
  let H:= (reachP s G c f).toContinuousLinearMap; let Hp:= (ContinuousLinearMap.fst ℝ (Directions G c) (Directions G f)) ∘L H
  have hc (y:ZipP G c f): ‖Hp y‖≤‖y‖:= (displacement_bounded s 1 y.1).trans (le_max_left ..)
  have he': Brush j 1 1 Hp x:= linearB Hp ((hc x).trans (hx.trans hr')) (by rw [one_mul]; exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by rw [one_mul]; exact hc _)) zero_le_one
  have he : 1≤k:=by unfold k; nlinarith only [hh]
  have hV:1≤V:=by unfold V; linarith
  let U (x:ZipP G c f):= increment (1:Config G c) x.1; let i:S.Choices:=Classical.arbitrary _
  have hf:Mode U x j v:=(hX c f S T h hs x hx i).1
  have hk : Brush j k V (fun z=> (orbitΛ (S:=S) s z).snd) x:= Brush.fold (zero_le_one.trans hV) h₁ (fun p => ?_)
  · exact ((he'.climb he hV).pair hk).trim
  · let F : Directions G f→L[ℝ] G.Color:=ContinuousLinearMap.proj (edge s p); have h := ht.report F (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by rw [one_mul]; exact norm_le_pi_norm i _); rw [one_mul] at h
    exact Vine.displacement_pay s p 1 1 hf h -- h resulting value includes two royalty factors?
-- hover once masks on. Include correction independent of z, scaled by β for two updates at same monomial degree.
def sourceΛ (i:Stream c f)(z:Air f G)(p:E):=
    let Z:= timeΛ X p
    Frond.ivy T X.x (choice i.1 X.k) i.2 (orbitΛ (S:=S) i.1 (twig X z p))+ Vine.costs Z (voltage Z) i.1 i.2
end
lemma volted (L : Side)(D: Patch)(hd: D.Branches P.bind G)(j:ℕ)(hj:1≤j) {η r Q W : ℝ} {p:ℝ→ℝ}(h:Torch η r Q)(hW: W<0)(hp: Rate G L W p)(hh:∀ᶠ x in atTop,0≤p x): ∃ C:ℝ→ℝ, Rate G L 0 C ∧ ∀ᶠ t in atTop,
   ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → Works P L t S T → ∀ (F : Forest S.ratio) (X : Coat T F),X.x=t → Allow X.blank.plate (along S) (tubularPrice G L) η r Q → ∀ i : Stream c f, ∀ x:ZipP G c f, ‖x‖≤p t→ Brush j (C t) 1 (fun v=> Vine.costs (dry X v) (voltage (dry X v)) i.1 i.2) x :=by
   obtain ⟨A,Eκ,hA,hE,H⟩:= driftless P L D hd j hj hW hp hh h
   let s x:= Eκ x*Eκ x*(1+(1+1))^j; refine ⟨_,((show Rate G L 0 s by simpa only [add_zero] using! (hE.mul hE).mul_right _).mul_left 2),?_⟩; refine H.mono fun t H c f S T hs hM F X ht ha i x hx=>?_ ; have hz:= H _ _ S T hs hM F X ht ha x hx
   have hy k (hk:k∈parents i.2) : Brush j (s t) 1 (fun v=> Vine.pot (dry X v) i.1 k (voltage (dry X v))) x:= by
     simp_rw [Vine.pot]; have hh v : (dry X v).selected i.1 (spot S k):= X.blank_all i.1 _; simp_rw [if_pos (hh _)]; exact ((semi (squared (hz.2 (i.1,k)))).trim)
   refine (Brush.spree _ _ _ zero_le_one hy).climb ?_ le_rfl; rw [sum_const,nsmul_eq_mul]
   apply mul_le_mul_of_nonneg_right ?_ (by unfold s; have h:0≤Eκ t:=(hz.2 (i.1,.inr (0,0))).nonneg; positivity)
   exact_mod_cast (show (parents i.2).card ≤ 2 from by rcases i with ⟨i,k|k|k⟩ <;> simp [parents])
lemma vaulted (L : Side)(D: Patch)(hd: D.Branches P.bind G) {p d : ℝ→ℝ}(Q:YM.ConnectedActivityE6.Target G P)(W:ℝ)(o:Target.Order G W) (j:ℕ)(hj:1≤j){v:ℝ}(h : -(1/2:ℝ) ≤ v)(hW:v<0) (hp:Rate G L v p)(hk: Rate G L 0 d)(he:∀ᶠ x in atTop,0≤p x) : ∃ C:ℝ→ℝ, Rate G L 0 C ∧ ∀ᶠ t in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖≤p t →
   ∀ i, Brush j (C t) 1 (sourceΛ X i z) x:=by
  obtain ⟨C,R,hC,hR⟩:= Vine.ceilings D hd j
  obtain ⟨r,hr,hm,B,hB,H⟩:= Frond.growth P L D hd j
  obtain ⟨A,Eκ,M,hA,hE,hM,H'⟩:= thistles L D hd Q W o j hj h hW hp hk he
  obtain ⟨K,hK,hF⟩:= volted L D hd j hj o.f hW hp he
  let Y t:= (j.factorial*B t)*(1+(1+j.factorial*C)*((1+|Eκ t|)*1))^j+K t
  have he:=hE.compare (v:=fun x=> |Eκ x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  refine ⟨Y,Rate.add (by simpa only [zero_mul,add_zero] using! ((hB.mul_left (j.factorial:ℝ)).mul (((Rate.const 1).add (((Rate.const 1).add he|>.mul_right 1).mul_left _)).pow j))) hK,?_⟩
  filter_upwards [H,H',hF,hA.below hW (min r R) (lt_min hr hC)] with t ht hx hf hs c f S T hS b μ H F X hX hP z hy x hq i
  have hW:= H.funds
  obtain ⟨hv,h,h₁⟩:=hx _ _ S T hS _ _ H _ X hX hP _ hy _ hq
  let v:=orbitΛ (S:=S) i.1 (twig X z x); have he:= (orbitingΛ (S:=S) i.1 (twig X z x)).trans (hv.trans (hs.trans (min_le_left ..)))
  have hp : Room _ S T t:=H.room
  have hh : Brush j (B t) 1 (Frond.ivy T X.x (choice i.1 X.k) i.2) v:= by rw [hX]; exact ht _ _ S T hS hW.length_eq H.room i.2 _ v he
  have ha:= ((h.pine (hR _ _ S T H.room.accepted hS i.1 _ (hv.trans (hs.trans (min_le_right ..))))).pine hh).trim
  have hv':= hf c f S T hS hW F X hX (show Allow _ _ _ _ _ _ from (H.localP F X.blank hX hP (X.bowed (temp_nonneg _))).sails.scale) i (sideways x) ((tally x).trans hq)
  have hy := Brush.reading sideways hv' norm_side; rw [mul_one] at hy; exact ha.gathering hy
end YM.ConnectedActivityE6.Blaze.Vine
