import YM.MSbar.Mosaic.Transit
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Issue
variable {ι:Type}{X f' g H0:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q L:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s' e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
variable (z:(i:ι)→Site (A i).f)
variable (hR:∀ᶠ i in φ,Ore M (X i) K)
variable (P:Palisade){τ b':ℝ}(B :ℝ)
local notation "x'" i=> boxX (tip G K.L (X i)) (z i)
local notation "x₁" i=> boxY (tip G K.L (X i)) (z i)
local notation "N"=> k*(p+2)
local notation "N'" i=> Fintype.card (Lake (A i).F (boxX (α' i) (z i)) G)
local notation "N₁" i=> (keepB (A i).F (x' i) G).card
local notation "N₂" i=> (keepF (A i).F (x' i)).card
local notation "Γ" i=> Ruby.crownP (A i).F (A i).M (W i)
local notation "Φ'" i=> inkW (N₂ i)
variable (h₁:p+2≤ m)(ha:Run φ X f' 0)(hk:k=m+1)(hT:p+3≤ k)(hμ:4 ≤ m)(hb:0<τ)(hb':0≤b')
local notation "γ" i=> thorn (Y i) (k*(p+2))
variable (hK:∀ᶠ i in φ, Issue.Buy (A i) (W i) (boxX (tip G K.L (X i)) (z i)) (boxY (tip G K.L (X i)) (z i)) J P χ (tip G K.L (X i)) e s' (thorn (tip G K.L (X i)) (k*(p+2))) τ b')
include hX hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK
-- choose Local Forecast any L size; Step Sensor ACK. require Hat mask chosen.
noncomputable def regionX (W:Issue G)(j:ℝ)(x:Site W.f)(Z:Positions (Primary W.c G))(J:Voice G)(p:Palisade) := hotel W.F (boxX j x) (boxY j x) J (postcard G W.c W.fClock Z) (venueX W Z) (pillow j) (room j)
noncomputable def targetP (W:Issue G)(J:ChartRatio G)(p:ℕ)(g:ℝ→ℝ)(x:Positions (Primary W.c G))(s:Site W.f→G.Color)(L:List (Primary W.c G)):= Spruce.mainP W.F W.pre W.v J W.fClock x W.post.path W.post.clip W.ρ W.T g p s L
noncomputable def sock (W:Issue G)(Z:Positions (Primary W.c G))(L:List (Primary W.c G)):=rave W.S W.pre.beta W.fClock W.pre L Z
noncomputable def localF (W:Issue G)(j:ℝ)(x:Site W.f)(Z:Positions (Primary W.c G))(J:Voice G) := woolModel W.F (boxX j x) J W.pre (boxY j x) W.v (postcard G W.c W.fClock Z) (venueX W Z) (pillow j) (room j)
noncomputable def modelP (W:Issue G) (j:ℝ)(x:Site W.f)(Z:Positions (Primary W.c G))(p:Palisade)(J:Voice G) (f:Config G W.f→ ℝ): Config G W.f→ℝ:= Rota.resample W.F (board W.F (boxX j x)) (W.localF j x Z J) (W.regionX j x Z J p) f
structure Pays (A:Issue G)(Z:Positions (Primary A.c G))(J:Voice G)(χ:ChartRatio G)(P:Palisade)(j:ℝ)(x:Site A.f)(k p:ℕ)(g:ℝ→ℝ)(ε:ℝ): Prop where
     main : let S:=regionX A j x Z J P; ∀ L:List (Primary A.c G), L.length ≤ k → ranged A.F L x (A.S.patch.L.val * closeN j) → Envelope (S.indicator (sock A Z L)) → ∀ U:Config G A.f,U∈ S →
          |A.modelP j x Z P J (Set.indicator S (sock A Z L)) U-targetP A χ p g Z (Ruby.crownP A.F A.M Z) L| ≤ ε
variable (F:ι →ℝ→ℝ) (hG0:∀ᶠ x in φ,Lodge.Hat k (vol (tip G K.L (X x))) (g x) (F x)∧1 ≤ g x) (hg:Run φ (fun i=>tip G K.L (X i)) g 0)
include hG0 hg
set_option maxHeartbeats 450000 in
lemma offer : ∃ e:ι→ℝ, Run φ Y e (epsW p) ∧∀ᶠ i in φ,Pays (A i) (W i) J χ P (Y i) (z i) k p (F i) (e i):=by
      let Xx:= Y; have hXx:Tendsto Xx φ atTop:=(Work.E09.betaF_growth G K.L).comp hX
      obtain ⟨B,h,h0,ht⟩:= hammer hX χ J H H' K D hG hχ hp hq M i' hc h₁ ha hk hT
      have he:(∀ᶠ i in φ,0≤h i):= ht.mono fun i hi=> hi p le_rfl|>.2.1.1; obtain ⟨i,hi⟩:=ht.exists; let v(i):= (A i).fClock
      have hb':0≤B:=hi p le_rfl|>.1.1
      obtain ⟨O,T',E,E',hO,hE,hT⟩:=Issue.portion hX χ J H H' K D hG hQ hχ hp hq W hW M i' hc z hR P B h₁ ha hk hT hμ hb ‹0≤b'› hK hb' h0 he -- lexical hT
      have hγ(x):=nearB hXx 1 one_pos x K.L.val; -- shadows hG? hg overwritten! rename
      let q(i):=(A i).S.patch.L.val*closeN (Xx i)
      let y(i):= liftW (αm (Xx i)) 0 (q i); have ht':Run φ Xx y 0:=by have he:= (hγ 0).2; simp_rw [one_mul] at he; exact he.alter (hp.mono (fun i hx=>by unfold y q; rw [hx.space] ))
      let a(i):= αm (Xx i); let d(i):= (plateD (z i) (a i) p 0 N k (q i) B)^k
      have hh: Run φ Xx d 0:=by let D(i):= plateD (z i) (a i) p 0 N k (q i) B; have hD:Run φ Xx D 0:= (Run.token hXx _).addR hXx ((((ht'.mulY hXx B).mulK hXx _).mulK hXx _).mulK hXx _); exact hD.Ypow hXx _
      let f(i):=5*goalP (Xx i) p*(g i+(g i)^2); have hf:Run φ Xx f 0:=by have hZ:=Run.core hXx (pawn p)|>.mulK hXx 5; exact Run.Ymul hXx (hZ.loosen (by linarith only [(mp0 p).2.2])) (hg.addR hXx (hg.Ypow hXx 2)) -- rename
      let σ':ι→ℝ:=d+h; have hv := roundS hX J H H' K hG hp
      let A'(i):=Spruce.tower (v i) (γ i) (pillow (Xx i)) (topP J P (Xx i)) b' τ (O i).outer (σ' i) p (spotN (Xx i)) N+ Spruce.finC N (spotN (Xx i)) (v i) (γ i) (pillow (Xx i)) (topP J P (Xx i)) τ b' (f i) (σ' i) (O i).outer
      have hA : Van φ Xx A':= Run.tariffs hXx J P hv.2.1 (hh.addR hXx h0) hO hf p N τ b' -- order
      have hu:∀ᶠ i in φ, (A i).S.patch.L.val* closeN (Xx i)≤ spotN (Xx i):=by
           filter_upwards [hp, hXx.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop K.L.val)] with i hi he; rw [hi.space]; unfold closeN spotN; rw [pow_succ' (radiusB (Xx i)) 3]; exact Nat.mul_le_mul_right _ he -- note
      refine ⟨fun i=> Salary.stamp (T' i) p (N' i) (v i) (E i) (E' i)+A' i,hE.addR hXx (hA _), ?_⟩
      filter_upwards [hp,hK,hT,hG0,hu,hc, hX.eventually (Alto.broad.eventually_ge_atTop 1), (hXx.eventually_ge_atTop 2), gate hX hG hX K.L N,ht,shapeK hX J H H' K hG hp W hW, (Alto.broad.comp hXx).eventually_ge_atTop 32] with i hp hK hQ' ⟨hH,hY⟩ hu ⟨hM,hF,hP,hΓ⟩ hZ hX₁ hh' ht hz hp'
      let F_:= (A i).F; let p':= α' i; let s:= sock (A i) (W i); let g':= Ruby.crownP F_ (A i).M (W i); have hU:0<v i:=hz.2.1; have hf:0≤a i:= le_trans (mul_nonneg (Nat.cast_nonneg _) hh'.1.le) hh'.2.1
      constructor; intro C L hL hz' hc' U hU'
      obtain ⟨HB,he⟩:= hM.preT
      have hv0: h i≥0:= ht p le_rfl|>.2.1.1
      let S:= A i
      let A0:= localW F_ S.pre S.v J χ (x' i) (x₁ i) U (v i) (W i) S.T p (F i) g' (cycleP F_ S.v L)
      have hG(i'):=(ht i'); -- `∀ i ≤P`, ok
      have hB:S.pre.beta=(v i)⁻¹^2:=by have hf:=hp.payments.case_; have hp0:0<S.pre.beta:=(half_pos (zero_lt_one.trans hf.enough)).trans_le hf.beta; unfold v fClock cue; rw [inv_inv,Real.sq_sqrt hp0.le]
      have hJ:Issue.sock (A i) (W i) L=rave (A i).S ((v i)⁻¹^2) (v i) (A i).pre L (W i):=by unfold sock; rw [←hB]
      rw [hJ] at hc' ⊢
      have hi:0<thorn p' N:=hh'.1; have hχx:=hQ'.digs; let D':= p'; have hO1:1 ≤ vol p':=by change (1:ℝ)≤hatW p'/32; have hp:32 ≤ hatW p':=hp'; linarith only [hp] -- might need
      have hT: |(A i).modelP p' (z i) (W i) P J _ U-A0| ≤ Salary.stamp (T' i) p (N' i) (v i) (E i) (E' i):=Issue.pays (A i) χ J P p k (boxX p' (z i)) (boxY p' (z i)) (W i) (z i) K H H' hp.space.symm hp.payments hQ i' hM hχ hK.spot hK.price (O i) (T' i) (F i) g' hQ'.epic hz.2.2.1 L hK.hit (zoneM F_ (z i) p' L (fun v hv=>(hz' v hv).trans hu)) hf (by apply le_trans (le_of_eq (one_mul (p+2)).symm); exact Nat.mul_le_mul_right _ (by omega)) hL le_rfl hL (show Lodge.Hat k (O i).w (g i) (F i) from (hQ'.vlog.symm ▸ hH)) hQ'.digs (fun i hi' => hG i hi'|>.1) hz' (fun i hi'=> hG i hi'|>.2) (hQ'.payQ _ hL) hQ'.funds hc' U hU' -- hχ alias etc reorder
      refine (abs_sub_le _ A0 _).trans (add_le_add hT ?_)
      have hO:(0:ℝ)+(γ i) ≤ a i:=by rw [zero_add]; let b:= γ i; refine le_trans (show b ≤ ray N b from le_mul_of_one_le_left hi.le (show 1 ≤ ((3+N:ℕ):ℝ) from Nat.one_le_cast.mpr (by omega))) hh'.2.1
      have he0:= hearts F_ (A i).v L p (m:=N) (z i) (fun j hi=> ht j hi|>.1) hz' hf rfl hL le_rfl
      let P₀:= plateD (z i) (a i) p 0 N k (q i) B
      have hp0:1≤ P₀:= by unfold P₀ plateD; have he := (wpos (a i) 0 (q i)); apply le_add_of_nonneg_right; positivity
      have ht₀ : ∀ z'≤p,Vault (address F_ G) {z i} (a i) 0 N 0 (PowerSeries.coeff z' (cycleP F_ (A i).v L)) (σ' i):=by
           intro j hj; apply Quote.widen (he0 j hj|>.1) ( (pow_le_pow_right₀ hp0 hL).trans (le_add_of_nonneg_right hv0)) le_rfl
      have hw := hF.beam; have hR: (A i).passage (X i)=Xx i:= by unfold passage; rw [hp.space]; -- rfl
      have hQm:=hF.turns; rw [hR] at hw hQm
      let e':= (A i).post
      have he':FetchD (Measuring.chart S.f G) (γ i) (f i) ( (film S.pre S.T (v i) p) ∘ Lodge.Clamp (F i)):=by
           refine Spruce.tides _ M.s k (fun j hj=> (show ContDiffAt ℝ k _ _ from (by rw [hk]; exact hw j hj))) hH (by omega) (fun j hj=>?_ ) hO1 hi.le hY; exact Issue.shiftJ (n:=0) (JetTab.levelAll (zero_lt_one.trans_le hO1) hf hw hQm hμ le_rfl j (by omega)) ((le_add_of_nonneg_left (le_rfl : (0:ℝ)≤ 0)).trans hO) hi.le le_rfl
      have hd:0 < v i:=hU
      have hu : ‖meetVar (W i) (berth F_ S.pre S.v J (x' i) (x₁ i) U (W i) (v i) 0)‖ ≤ (O i).outer := (hQ'.funds.receipt U hU' 0 (Lapaz.born _ _ _ _ _ _ _ _ _ _ hK.spot hd hU')).1
      have hew: Issue.targetP (A i) χ p (F i) (W i) g' L= mainP (A i).F S.pre S.v χ (v i) (W i) e'.path e'.clip S.ρ S.T (F i) p g' L:=rfl
      refine Spruce.coke F_ S.pre S.v J χ (x' i) (x₁ i) U (v i) (W i) S.post.path S.post.clip S.ρ hK.spot (z i) S.T (F i) g' L he.bond hM.critical hM.classical_ hχ he.quiet hp.payments.bends.1 hK.price.first.extendsX hU' hQ hd (housing F_ (z i) p') hi.le hu hQ'.throne he' (le_rfl : (0:ℝ) ≤0) hK.fast hK.fast ?_ ?_ hz.2.2.1 ?_ ?_ -- signature
      · exact (he0 0 (by omega)).2.trans (Nat.mul_le_mul_right _ hL)
      · exact Quote.cooled (mul_nonneg (Nat.cast_nonneg _) hi.le) hh'.2.1 (ht₀ _ (Nat.zero_le _))
      · intro k hk; obtain ⟨_,hv,hQ⟩:=ht _ hk; exact ⟨Tokew.delta (Tokew.soft hv hO (add_nonneg le_rfl hi.le)) le_rfl (le_add_of_nonneg_left (show 0≤ d i from pow_nonneg (zero_le_one.trans hp0) _)), hQ⟩
      intro j hj; exact ⟨Quote.cooled (add_nonneg le_rfl hi.le) hO (ht₀ j hj), (he0 j hj).2.trans (Nat.mul_le_mul_right _ hL)⟩
end Issue
end YM.MSbar.Mosaic
