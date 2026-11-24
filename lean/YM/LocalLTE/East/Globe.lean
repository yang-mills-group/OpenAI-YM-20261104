import YM.LocalLTE.East.Pavement
import YM.LocalLTE.Tile.Allot
import YM.LocalLTE.Tier.Dais
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
variable {P:Teller G} {v₀ v₁ K₁:ℝ}
-- Purchase Precision for any INPUT poly grade order x≤f cutoff. Radius OUT strictly > ℓ geometry.
open LocalLTE.FrameBox LocalLTE.Inset Brush Sienna
private lemma survey (m l : ℕ) : ∃ (v η:ℝ) (k j:ℕ), -(1/2:ℝ) < v ∧ v<vow ∧ η<0∧ l<j∧ pie m+1≤ j ∧ 1≤k∧ Pastel.mini*(k:ℝ) ≤ chip (m+1)-10*slack∧
  (v+1/2)*((pie m+1:ℕ):ℝ) < 10*slack∧
  max ((1/2:ℝ)*j+(η+v)*j) (chip (m+1)-9*slack)+(v+(1/2-η))*(l:ℝ)<chip (m+1)-7*slack:=by
   let m':ℝ:= ↑(pie m+1:ℕ); let l':ℝ:=l; let A:= (1+m'+l'); let ε:=slack/(4*A); let v:=-(1/2:ℝ)+ε; let S:=chip (m+1)
   have hl:0 ≤ l':=by unfold l'; positivity
   have hm':0 < m':= by unfold m'; positivity
   have hA:m'+1≤A:=by unfold A; linarith; 
   have hA':l'+1≤ A:=by unfold A; linarith
   have hΞ:0<A:=by linarith
   have hB:0< slack:=by norm_num [Pastel.slack]
   have he:0< ε:=by unfold ε; positivity
   have he':ε*(4*A)=slack:= by unfold ε; field_simp
   have hε: ε ≤ slack:=by nlinarith
   have hρ: -(1/2:ℝ)<v:=by unfold v; linarith
   have hτ: v < vow:= by unfold v vow; unfold Pastel.slack at hε; linarith
   have h'w:ε*m'≤ slack:=by nlinarith
   obtain ⟨j,hj⟩:= exists_nat_gt ((-S+9*slack)/ε)
   obtain ⟨k,hk⟩:= exists_nat_gt ((-S+10*slack)/(-mini))
   have hz: 0 < -mini:=by norm_num [mini]
   let d:= pie m+1+l+(j+1)
   have hd: l < d∧pie m+1 ≤ d∧ j≤d := by unfold d; omega
   have ht: -(ε*(d:ℝ)) < S-9*slack:= by
      have hp':=(div_lt_iff₀ he).mp (hj.trans_le (Nat.cast_le.mpr hd.2.2)); linarith
   refine ⟨v,-(2*ε),k+1,d,hρ,hτ,(by linarith),hd.1,hd.2.1,(by omega),?_,?_,?_⟩
   · have hp':=(div_lt_iff₀ hz).mp (hk.trans_le (Nat.cast_le.mpr (Nat.le_succ k))); unfold S at hp'; linarith
   · change (v+1/2)*m'<_; unfold v; linarith
   rw [max_eq_right (by unfold v; unfold S at ht; linarith)]; change S-9*slack+(v+_)*l'< S-7*slack; unfold v; nlinarith
variable {κ:ℝ}
lemma globeAudit (Q:ConnectedActivityE6.Target G P)(A':Q.Expense) (hr: Q.rate < Pastel.mini) (m l g n ℓ:ℕ) (hn:stagnate ℓ Q.halo < n) (hk:Reliable G κ K₁) : ∃ (k₀ k:ℕ),1≤k ∧ ∀ L:Side,k₀ ≤ L.val→ ∀ (D:Patch), D.Branches P.bind G→ ∀ (W μ:ℝ)(o:Target.Order G W) (χ:Chi),0<W→0<μ→ ∀ᶠ x in atTop, let B:=betaF G x L;let R₀:= radiusB x; let r:= stagnate ℓ Q.halo* R₀; let b:= n*R₀
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D→ Stamp T→∀ (R:Rep G f) (σ:ℝ) (H:Cash W x μ L Q o σ T R)(φ:ℕ→ℝ),
    (∀ u, SumBudget (fun i=> if (R.activities.reg i).site=u then φ i else 0) 1) → ∀ (j:ℕ→ℕ)(w':BudgetPoint), w'.B=R₀ → w'.threshold=Pressure.temp x →w'.order=l→ w'.power=g → 2*b<c.val → ∀ (h:2*(2*r)≤c.val),
       ∃ f:H.fragrances→ℝ, (∀ i, 0≤f i) ∧ (∀ u:Site c,SumBudget (fun i=> if u∈Captain.reachability i∧ East.Orchestra H i ℓ then f i else 0) (B^(chip (m+1)-5*slack)))∧
       ∀ (p:H.fragrances), East.Orchestra H p ℓ → (∀ i k,Sum.inl k∈ East.docket H p i→ j k≤ m ∧ TellerF R B κ (L.val*R₀) (j k) (φ k) k) → ∀ (o: Site c), o∈Captain.reachability p→∀ (X:LocalLTE.FrameBox.Grove o), let e:= (fun v=>stream H χ v p)-LocalLTE.Fan.Field.realised H (East.docket H p) p.2 m k j χ r X κ h
        w'.Regular (neighbors r o) e ∧ w'.supBounds o (neighbors b o) e (f p):=by
    obtain ⟨d,hD⟩:= conduitΘ P Q
    obtain ⟨v,η,k',j,hv,hV,hη,hl,hp,hk',hΞ,hΩ,h₀⟩:= survey m l
    refine ⟨d,k',hk',fun L hL D hD' W μ o χ hw hμ=>?_⟩
    obtain ⟨A,a,C,d',v',t',r',E,q,k,hE,hf,-,hz⟩:=hD L hL D hD' j χ W hw _ hμ o
    obtain ⟨e,he,H⟩:= Armada.ensemble Q L hμ A'.earn A'.price (by linarith [A'.worth,A'.first,A'.second]) j k hf
    let p x:= ballCost (stagnate ℓ Q.halo*radiusB x)
    let V x:= ((p x:ℝ)* East.grand L)
    have hp': Rate G L 0 fun x=> (p x:ℝ):= by simpa [p] using! Census.width_rate G L (East.stagnate ℓ Q.halo) 0
    have ht:Rate G L 0 (fun x=> stadium (V x) ℓ) := East.masses V (hp'.mul_right _) ℓ
    let r:=chip (m+1)-6*slack
    have hᵢ : Rate G L 0 fun x=> (n*radiusB x:ℕ):= by push_cast; exact Rate.radius_price.mul_left _
    have hh (i:Fin (ℓ+1)):= LocalLTE.Fan.Field.occupancy (Z:=fun x=> n*radiusB x) L D hD' Q W o i.val m ℓ k' j l g hk' hl hp hr hΞ hΩ hv hV hη h₀ hk
       (Rate.radius_price (G:=G) (L:=L)) (M:=fun x=> pubFee L G Q.halo ℓ (radiusB x)) (N:=fun x=>L.val*radiusB x) (I:=fun x=>radiusB x) (by push_cast; exact Rate.radius_price.mul_left _) (hp'.mul_right _) hᵢ hE
    filter_upwards [H,((ht.add ((he 0 0).weaken Q.stop.le)).mul (Rate.power (G:=G) (L:=L) (a:=r))) (chip (m+1)-5*slack) (by unfold r Pastel.slack; linarith),Eventually.and -- edit
       ((YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1) hz, recurring P L,eventually_all.mpr hh]
       with x hx h hA' ht' hD'' Bx R₀ r₀ b c f S T hS hT R σ H' φ hφ u b' hU hpB hw hb hs hS'
    have hu : 0 < Bx:= zero_lt_one.trans_le hA'.1
    have hX:= H'.laws.data.funds.length_eq
    obtain ⟨hcub,hV,hΛ⟩:= ht' c f S T R hX H'.laws.intake; have he:= grandWay H' hφ hcub hA'.1 hV hΛ
    let Y:= fisc (c:=c) R Bx φ
    let M (p:H'.fragrances):= |LocalLTE.Fan.Field.speedΛ H' p.2| * LocalLTE.Fan.Field.stock (East.docket H' p) Y; have hM i : 0≤ M i := mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _=> Finset.prod_nonneg fun _ _=> (he.1 _).1)
    let N:= (hA'.2 c f S T hS hT _ _ H').some
    let U':= fun i=> (M i+N.design i)* Bx^r
    have hF i:0≤U' i:= mul_nonneg (add_nonneg (hM _) (N.pvc _)) (Real.rpow_nonneg hu.le _)
    refine ⟨U',hF,fun t=> ?_,?_⟩
    · have hp:= musicHall H' ℓ Y (fun i=>he.1 i|>.1) (V x) t (budget_loosen (he.2 _) (mul_le_mul_of_nonneg_right (show ((neighbors (stagnate ℓ Q.halo * R₀) t).card:ℝ) ≤ p x from by exact_mod_cast neighbors_card ..) (by positivity)))
      have hz:= hx.applies N 0 0 t; let C₁:= Bx^r; have hh:= budget_scale (show 0≤C₁ from Real.rpow_nonneg hu.le _) (budget_plus hp hz)
      refine budget_loosen (budget_mono hh (fun i=> ?_) (fun i=>?_)) ?_
      · split; next => exact hF _
        exact le_rfl
      · split
        next hh' =>
          have hm: 1 ≤ Real.exp (A'.earn*coverNumber R₀ (Captain.reachability i)):= Real.one_le_exp (mul_nonneg A'.price (Nat.cast_nonneg _))
          rw [if_pos hh'.1]; dsimp only; rw [if_pos (Nat.zero_le i.1), if_pos (and_comm.mp hh')]; simp only [U',Captain.markΦ,zero_mul,pow_zero,one_mul]; rw [mul_comm C₁]; apply mul_le_mul_of_nonneg_right (_root_.add_le_add (?_) (le_mul_of_one_le_right (N.pvc _) hm)) (Real.rpow_nonneg hu.le _) -- edit
          exact le_rfl
        next => exact hh.1 i
      rw [mul_comm C₁]; exact (le_abs_self _).trans h
    rintro ⟨j',p'⟩ hg h x₁ h₁ X e'
    let p₁: H'.fragrances:=⟨j',p'⟩
    have hu': Captain.reachability p₁ ⊆ neighbors r₀ x₁:= stations H' _ _ hg _ h₁
    have hh' (i):=hg.each i
    refine ⟨CouplingShape.reg_sub (CouplingShape.reg_extend ((N.gloryBudget p₁ b' hpB (hw.trans_le hl.le)).2.1) hu') (LocalLTE.FrameBox.legal X _ hk _ _), ?_⟩
    exact hD'' ⟨j', Nat.lt_succ_of_le hg.length⟩ c f S T hS hT R _ _ H' p' (East.docket H' p₁) (fun i=>⟨(hh' i).lift,(hh' i).burns,(hh' i).players,(hh' i).received,caps H' p₁ hg i⟩) χ _ _ _ _ _ _ _ _ _ N u φ (East.title H' p₁ hg) (fun i k hk'=> ⟨hatching H' _ _ _ _ _ p₁ hg h _ _ hk',he.1 k⟩) b' hpB hw hb x₁ r₀ b hu' (show r₀<b from (Nat.mul_lt_mul_of_pos_right hn (Brim.paidB H'))) le_rfl hs hS' X
end YM.PhysicalNext.Repeat.East
