import YM.LocalLTE.Ballot.Swell
import YM.LocalLTE.Vinyl.Prospects
import YM.LocalLTE.Vinyl.Hour
import YM.LocalLTE.Rate.Permit
/-! Root skeleton bill with independent coefficients, permits at true Path not homogeneous marker. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')



-- Whorl.S e_a first variant C. v ~ -(1/2), power requires upper H(i,n) chosen from jumpFee grads.V.Uniform. use p length atMost.
local notation "EC"=> Directions G c
local notation "SC"=> Disk G c
open Sienna FrameBox Grove
open PhysicalNext.Repeat.East
-- Maneuvers depend on V generic. Carrier.P.Slot all.S.Fin count.Bound independent periods.

local notation "T!"=>betaF G t L
local notation "B₀"=> radiusB t
open Height




/-! ## Ranks through arbitrary derivatives

Book the angular rank and the builder polynomial degrees once; at every
stage choose smoothness depth beyond those ranks, including enough for that
stage's physical derivative costs. Achievable: let the ball exponent approach
−1/2. This does not give estimate uniform in stage *ahead* of the post-L
schedule, which must also be bought for the orders used. Useful feature is
only this particular pre/post separation of budgets. -/

def HeightPlan (k n m:ℕ)(θ:ℝ)(q K:ℕ): Prop:=∀ ℓ:ℕ,∃ (α δ v τ θ' :ℝ)(j:ℕ), 0<K∧-(1/2:ℝ) < v ∧ v<Sienna.vow ∧ℓ<j∧ K≤j ∧ (∀ p:ℕ, p≤n → jumpFee q n m n k * ↑(p+1)+v*K ≤α) ∧ mini*q≤α ∧ α≤0 ∧ α<δ ∧ τ<0 ∧ (max ((1/2:ℝ)*j+(τ+v)*j) δ) +(v+(1/2-τ))*(ℓ:ℝ) < θ'∧ θ'<θ
-- simple tilt selector. Margin with l via τ chosen fine and j huge.
lemma swingOf (ℓ K:ℕ)(δ v₁ θ:ℝ)(h:δ<θ)(hk:-(1/2:ℝ)<v₁) : ∃ (v τ :ℝ)(j:ℕ), -(1/2:ℝ)<v ∧ v<Sienna.vow∧ v≤v₁ ∧ ℓ<j∧ K ≤ j∧ τ<0 ∧ max ((1/2:ℝ)*j+(τ+v)*j) δ + (v+(1/2-τ))*ℓ < θ:=by
    let q:= min (θ-δ) 1/(4*(ℓ:ℝ)+4)
    have hq:0<q:= by unfold q; positivity
    let w:=min (v₁+1/2) (min q ((1/2:ℝ)+Sienna.vow)/2)
    have hw:0<w:=by apply lt_min; linarith; apply half_pos; exact lt_min hq (by norm_num [Sienna.vow])
    have hx: w ≤ v₁+1/2:= min_le_left ..
    have hy: w ≤ q:=by
       unfold w; refine le_trans (min_le_right ..) ((half_le_self ?_).trans (min_le_left ..)); exact le_min hq.le (by norm_num [Sienna.vow])
    have ha:w <(1/2:ℝ)+Sienna.vow:=by
       have hp:min q ((1/2:ℝ)+Sienna.vow) ≤ _:=min_le_right ..; unfold w; refine lt_of_le_of_lt (min_le_right ..) ?_; linarith only [hp,show (0:ℝ) <1/2+ Sienna.vow from (by norm_num [Sienna.vow])]
    let v:= w-1/2; let τ:= -2*w
    let T:= (1/2:ℝ)+(τ+v); have ht:T<0:=by unfold T τ v; linarith only [hw]
    obtain ⟨j,hj⟩:= exists_nat_gt (δ/T); let L:=ℓ+j+K+1; have hi:j≤ L:=by unfold L; omega
    have he: (1/2:ℝ)*(L:ℝ)+(τ+v)*(L:ℝ)≤δ:=by
        rw [←add_mul]; apply (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hi) ht.le).trans; have hj' := div_lt_iff_of_neg ht|>.1 hj; linarith only [hj']
    have hD:(4*(ℓ:ℝ)+4) * q ≤ θ-δ:=by
        unfold q; rw [mul_comm,div_mul_cancel₀ _ (by positivity : 4*(ℓ:ℝ)+4≠0)]; exact min_le_left ..
    refine ⟨v,τ,L,(by unfold v; linarith only [hw]),(by unfold v;linarith only [ha]),(by unfold v;linarith only [hx]), (by unfold L;omega),(by unfold L;omega),(by unfold τ;linarith only [hw]),?_⟩
    rw [max_eq_right he]; unfold v τ; nlinarith only [hw,hq,hD,mul_le_mul_of_nonneg_right hy (show 0≤(ℓ:ℝ) from by positivity), show 0≤ q*ℓ from (by positivity : 0≤ q*(ℓ:ℝ))]
lemma heightPlan (k n m:ℕ)(θ:ℝ)(J:ℕ): ∃ p K:ℕ, J ≤ K∧HeightPlan k n m θ p K:=by
    let θ':=min 0 θ -1; let δ:=θ'-1; let α:=δ-1; let v₁:= -(15/32:ℝ)
    obtain ⟨q,hq⟩:=exists_nat_gt (α/Pastel.mini); have hm':mini <0:=by norm_num [mini]
    have hq': Pastel.mini*q ≤α := by rw [div_lt_iff_of_neg hm'] at hq; linarith
    let f:ℝ:= jumpFee q n m n k*(n+1:ℕ); have hv:v₁<0:=by norm_num [v₁]
    obtain ⟨K,hK⟩:= exists_nat_gt ((α-f)/v₁)
    let d:= J+K+1
    have hh: K ≤ d:= by unfold d; omega
    refine ⟨q,d,(by unfold d;omega),fun ℓ => ?_⟩
    obtain ⟨v,τ,j,h1,h2,h3,h4,h5,h6,h7⟩:= swingOf ℓ d δ v₁ θ' (by unfold δ;linarith) (by unfold v₁;norm_num)
    refine ⟨α,δ,v,τ,θ',j,(by unfold d;omega),h1,h2,h4,h5,fun p hp=>?_ ,hq',(by unfold α δ θ'; linarith only [min_le_left (0:ℝ) θ]),(by unfold α;linarith),h6,h7, (by unfold θ';linarith only [min_le_right (0:ℝ) θ])⟩
    have hx :jumpFee q n m n k *(p+1:ℕ) ≤f:=by unfold f; exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.succ_le_succ hp)) (by unfold jumpFee; positivity)
    rw [div_lt_iff_of_neg hv] at hK; apply (add_le_add hx (mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _))).trans; nlinarith only [hK,mul_le_mul_of_nonpos_left (Nat.cast_le (α:=ℝ).mpr hh) hv.le]
lemma preciseManifest (Q:ConnectedActivityE6.Target G P)(p:Q.Expense)(a:ℝ)(ht:3/8+Q.rate < a)(ha:a<0): ∃ m:ℕ,∀ (l k n q b₀ h:ℕ) (e κ d:ℝ), Reliable G κ d→ 0<e→ (e < (n:ℝ)/100) → e < (3/8:ℝ)*q → East.stagnate q Q.halo < b₀ → ∀ (α K:ℕ), HeightPlan h q n (-e-1) α K → ∀ (L:Side),m≤ L.val →∀ (W:ℝ)(o:Target.Order G W),∀ μ:ℝ,0<W→0<μ→∀ χ:Chi,∀ᶠ t in atTop,ManifestC Q L o p χ l k n q b₀ h α K κ e a t μ :=by
   have hr:Q.rate < mini:=by unfold mini; linarith
   obtain ⟨m,hp⟩:= Height.canaries P Q p hr; obtain ⟨m',hm⟩:= Daisy.early Q
   refine ⟨max m m',fun l k n q b₀ h e κ d hk he hen heq hQ α K hT=>?_⟩
   let idx:= -e -1
   obtain ⟨η,δ,v,τ,X,j,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩:= hT l
   intro L hL W o μ hW hμ χ
   have hL':m≤ L.val := (le_max_left ..).trans hL
   have he' := hm L ((le_max_right ..).trans hL)
   obtain ⟨v₀,a₀,hC,hF,HP⟩:= hp L hL' W μ o hW hμ j k q χ
   obtain ⟨v₁,a₁,hC',hF',HP'⟩:= hp L hL' W μ o hW hμ l k q χ
   let V x:=(ballCost (stagnate q Q.halo*radiusB x):ℝ); let y x:= V x * East.grand L
   let s₁ x:= (b₀*radiusB x)
   let b x:=(ballCost (s₁ x):ℝ)
   let Φ x:= phaseP p.earn b₀ (s₁ x)
   have hb:Rate G L 0 b:= by simpa only [s₁,b,Nat.add_zero] using Census.width_rate G L b₀ 0
   have hv:Rate G L 0 V:=by simpa only [V,Nat.add_zero] using Census.width_rate G L (stagnate q Q.halo) 0
   have hΨ: Rate G L 0 Φ := (Rate.const 1).add (hb.mul_right _)
   have hs:Rate G L 0 (fun x=> (s₁ x:ℝ)):=by unfold s₁; push_cast; exact Rate.radius_price.mul_left _
   let φ x:= (1+(s₁ x:ℝ))^(k*l)*(Φ x*a₀ x)
   have hι:=Rate.mul ((((Rate.const 1).add hs).pow (k*l))) (hΨ.mul hF)
   rw [zero_mul,zero_add,zero_add] at hι
   let Y x:=betaF G x L; let f x:= b x*Real.exp (p.earn*ballCost b₀)*stageQ (y x) 1 q
   let t' x:= Φ x*a₀ x
   have hf: Rate G L 0 f:=by simpa only [zero_add] using! ((hb.mul_right _).mul (Fan.springsQ q y (hv.mul_right _) 1)) -- order
   have hq:Rate G L (3/8+Q.rate) t':= by simpa only [zero_add] using! hΨ.mul hF
   let δ₀ :=max idx (-e+(3/8+Q.rate))
   let u x:=(Y x)^idx*(f x+t' x)+(Y x)^(-e)*t' x; have hR:Rate G L δ₀ u:=by
      have hv:= hf.add (hq.weaken (by linarith)); exact (((Rate.power.mul hv).weaken (by rw [add_zero]; exact le_max_left ..)).add (((Rate.power).mul hq).weaken (le_max_right ..)))
   have hw':δ₀ < -e:= max_lt (by unfold idx; linarith) (by linarith only [ht,ha])
   by_cases h': ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
   swap; · exact Eventually.of_forall fun t c f S T h => (h' ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
   obtain ⟨D,hd,hD,hZ⟩:= h'
   let M x:= East.pubFee L G Q.halo q (radiusB x); have hM:Rate G L 0 M:= hv.mul_right _
   have hp':Rate G L 0 (fun x=> ((L.val*radiusB x:ℕ):ℝ)):= by push_cast; exact Rate.radius_price.mul_left _
   let N x:=L.val*radiusB x
   have hPin(k':Fin (q+1)) := Fan.porpoisesC Q hr L D hd W o k'.val n q α h K j l k η δ X v τ h1 h2 h3 h4 h5 (h6 _ (Nat.le_of_lt_succ k'.2)) h7 h8 h9 h10 h11 idx h12 (ℒ:=s₁) hs hk (N:=N) hp' (I':=Pressure.radiusB) Rate.radius_price (N':=N) hp' hM hC
   filter_upwards [HP,HP',hR _ hw', (show Rate G L (3/8+Q.rate) φ from hι) _ ht,hF a ht,byline q p L hμ, East.recurring P L,eventually_all.mpr hPin,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx Hx hU hp ht he'₀ hg hK hδ c f' S TW hS hT R C H r₀ P₀ hCat hP hB hVp hV N' hm hΛ hρ -- edit hCat y let
   let F:= Fan.acclaim (Y x) r₀ R
   have hB':0 < Y x:=zero_lt_one.trans_le hδ
   have h':Pumps R F (1*incomingE G L x):=Fan.crowned (G:=G) r₀ _ κ _ hΛ hδ
   obtain ⟨C₁,t,a',b',V',H₁,X₁,u₁,v',e₁,T₁,hY,hX,hP₀⟩:= Hx c f' S TW hS hT R C H F h'; -- count from Borrow 10+ N
   obtain ⟨C₂,t',a'',b₂,V₂,H₂,X₂,u₂,v'',e₂,T₂,hY₂,hX₂,hP₂⟩:= hx c f' S TW hS hT R C H F h'; -- problem shadows t'
   subst V₂
   refine ⟨T₁,a',b',V',H₁,C₁,t,X₁,u₁,v',e₁,hY,hP₀.2.1,hP₀.1,?_⟩
   intro ι iM Mx Zx l' α₀ aΛ P' hΞ hα hpp hwt hM f₀ X'
   let β:= betaF G x L
   have hp':0<β:=by exact hB'
   have ha j:0≤aΛ j:=by rw [(hα j).2]; exact mul_nonneg (zero_le_one.trans (hα j).1) (hΞ j)
   have hr0:= (Fan.spentZ Mx q r₀ hδ _ ha hwt (S:=S) (G:=G) (Q:=Q)) -- order
   obtain ⟨hcub,hVbill,hΛ'⟩:= hg c f' S TW R hS.length_eq H.laws.intake
   have hz:= hP₂.2.2 ι iM Mx aΛ ha hr0
   have hG : Ac.Hit (reachability (H:=H)) (radiusB x) (fun z=> Height.beaconN H q z* Height.rocket H F z *Height.markU hY₂ Mx aΛ z P₀.power) p.earn (a₀ x) :=by rw [hB]; exact hz
   obtain ⟨hx₀,hv⟩:= Fan.oldO Mx H hδ l' aΛ α₀ (fun i=>(hα i).2) hΞ (fun i=>(hα i).1) hwt
   have hc₀:= Palette.activeB Mx H l' hΞ hx₀ he' (by rw [H.laws.intake.sizes,hS.length_eq]; exact hP₀.2.1.covers)
   let s:=phaseP p.earn b₀ (s₁ x)* a₀ x; let l₁:=stagnate q Q.halo;
   have he : l₁*(radiusB x) < b₀*radiusB x:= Nat.mul_lt_mul_of_pos_right hQ (show 0 < radiusB x from hV ▸ P₀.B_pos)
   have hs₁ : 0 ≤ (b₀:ℝ):= Nat.cast_nonneg _
   have hl:P₀.order ≤ j:= hP.trans_le h4.le
   have hf:= Fan.rawG Mx H χ q T₂ aΛ P₀ hV hY₂ _ _ F hP₂.1 h'.1 (fun i=>(hα i).1) (fun i=>(hα i).2) hΞ hδ hVp hl hG -- order!
   have hS₁:= Fan.ripeC Mx H χ q n T₂ r₀ P' aΛ P₀ hV b₀ hY₂ he _ _ F hP₂.1 h'.1 (fun i=>(hα i).1) (fun i=>(hα i).2) hΞ hδ hVp hl hG p.price
   let K':=(fun (p:Stars H Mx)=>Captain.reachability p.1)
   let t₀:=β^a
   have hf' {A X : Stars H Mx→Support c} {Y:Stars H Mx→ Config G c→ℝ} (k l:ℝ)(h:GrowsP Mx H P₀ A l' p.earn k Y X)(he:k≤l): GrowsP Mx H P₀ A l' p.earn l Y X:=by
      obtain ⟨f',ha,hp,hX⟩:= h.lights; exact ⟨f',ha,hp,fun i=> budget_loosen (hX i) he⟩
   rw [hP,hB] at hS₁ -- dependent P . maybe can't rewrite. do hp proof only.
   refine ⟨hc₀,hf' _ t₀ hS₁ ((le_abs_self _).trans hp), hf' _ t₀ hf ((le_abs_self _).trans ht),fun T' hs=>?_⟩
   obtain ⟨φ',hy,hΦ,hV'⟩:= Coup.comply hΛ hδ _ hm
   have h₁:= East.grandWay H hy hcub hδ hVbill hΛ' -- hV' shadow
   let az:=fisc (c:=c) R β φ'
   have h2 (i) (hi: R.activities.E i≠0) (hh:n<r₀ i): β^e ≤ F i:=by
      unfold F acclaim; rw [if_neg hi]; exact Real.rpow_le_rpow_of_exponent_le hδ (hen.le.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hh.le) (by norm_num)))
   have h3: β^e ≤ grow G L x^q:= by
      unfold grow; rw [← Real.rpow_natCast, ← Real.rpow_mul hp'.le]; exact Real.rpow_le_rpow_of_exponent_le hδ heq.le
   apply hf' (β^idx*((b x* Real.exp (p.earn*ballCost b₀))*stageQ (y x) 1 q+s) + (β^e)⁻¹*s)
   rotate_left
   · rw [← Real.rpow_neg hp'.le]; exact (le_abs_self _).trans hU
   refine Fan.worthierC Mx Zx H χ κ q n T₂ r₀ P' aΛ P₀ hV b₀ hY₂ he T' hs α K _ _ (β^e) F az hP₂.1 h'.1 (fun i=>(hα i).1) (fun i=>(hα i).2) hΞ hδ hVp hl hG (hS.length_eq.symm ▸ hV') (fun i hi=> hS.length_eq.symm ▸ ((hM i hi).2)) hpp h2 he'₀.1 he'₀.2 h3 _ ?_ p.price (1:ℝ) (y x) (Real.rpow_pos_of_pos hp' _) (Real.rpow_nonneg hp'.le _) hv (fun i=> (h₁.1 i).1) (?_) -- argument order! .h4 in hY
   · intro i hi X'' F' s'
     let T:= i.fst; let Xζ := originC Mx H i
     have he' k: (Field.pin (East.docket H i.1 k) H) = Fan.fibers H (i.fst.snd k):= by unfold Field.pin Fan.fibers; rw [← (hi.can.each k).lift]
     have hx' k: (Fan.fibers H (i.fst.snd k)|>.card:ℝ) ≤ East.pubFee L G Q.halo q (radiusB x):= by rw [← he']; exact caps H i.fst hi.can _ -- order
     have hL (j) (a)(hj:a∈ quietR Mx (T.snd j) (i.snd j)): Breed R r₀ φ' hCat κ (L.val*radiusB x) (radiusB x) n a:=by
         rcases a with k|k; · exact ⟨hi.loans k j hj,hΦ k (hi.loans k j hj)⟩
         have he := (hi.can.each j).stretch k (Fan.weaving Mx H i.1 i.2 q n r₀ P' hi j|>.1 hj); rcases k with k|k|k|k <;> first| exact he|trivial
     have ht:= hK ⟨T.fst,Nat.lt_add_one_of_le hi.can.length⟩ c f' S TW (hS.patch hD hZ) hT R μ C H ι Mx Zx T.snd i.2 r₀ φ' P' hi (fun i hi=>(hM i hi).1) hx' (fun j k hk=>⟨hL j k hk,h₁.1 k⟩) χ a'' b₂ H₂ C₂ t' X₂ u₂ v'' T₂ hY₂ hP₂.1 P₀ hVp hP hB (l₁*radiusB x) (b₀*radiusB x) Xζ (Fan.pinnedC Mx H _) (East.stations H q i.1 hi.can _ (Fan.pinnedC Mx H _)) he le_rfl (by omega) hs (T' i) -- signature order
     rw [show sitesPC Mx H q n r₀ P' b₀ i=_ from (if_pos (show fitsP Mx H q n r₀ P' i from hi))]
     exact ⟨AnalyticBridge.CouplingShape.reg_extend ht.1 (fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 (show _∈neighbors (l₁*radiusB x) Xζ from hi)).trans he.le)),ht.2.2⟩
   intro u; refine budget_loosen (h₁.2 (neighbors (stagnate q Q.halo*radiusB x) u)) (?_)
   exact mul_le_mul_of_nonneg_right (show _ ≤ V x from by unfold V; exact_mod_cast neighbors_card ..) (by positivity)
end YM.LocalLTE.Fan
