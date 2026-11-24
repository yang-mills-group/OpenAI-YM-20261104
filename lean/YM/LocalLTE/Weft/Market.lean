import YM.LocalLTE.Weft.Plaza
/-! relative charges for all inlet log letters. Uses any admissible secants independently of
actual history. `b : packet projection cost` polynomial Rate0 can recover more reserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Fan Brush Foramen Pastel
variable {v z r W w s t y η γ B a ε α : ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open Weft AnalyticBridge.VerifiedReset FrameBox
variable {κ k₁:ℝ}
structure CanX (κ:ℝ) (l a k:ℕ) (e : ℝ→ Config G f→ℝ) (s:Site f) (C:ℝ) : Prop where
   basis : ∃ (i:ℕ),i≤l∧ ∃ V:Grove s, Weft.Scene V κ i a k e C
-- Budget coefficient shape fixed at unconditional-V point for public.L. Individual symbolic path weights; `stock` via afd address from real H/W, DOES NOT inspect R's E,K,v,beta.
def labelGrade (R : Rep G f)(κ:ℝ)(T:ℕ→ℝ→ Config G f→ℝ)(ζ:ℕ→ℝ) (N M K j:ℕ)(q:ℝ) : Veil c f → Prop:= Sum.elim (fun i=> Fan.CanX κ N K j (T i) (R.activities.reg i).site (ζ i*q)) (Sum.elim (fun i=>(R.path.cubic i.2.2).length≤M)
    (Sum.elim (fun i=> (R.path.quartic i.2.2).length ≤ M) (Sum.elim (fun i=> (R.path.loop i.2.2).length ≤ M) fun _=> True)))
def ratioCash (A:Rep G f)(b:ℝ)(φ:ℕ→ℝ) : Veil c f→ℝ:= let H {d:ℕ} (p:ℕ→Atom G d)(i:Trans f):=(p i.2.2).magnitude/b
    Sum.elim φ (Sum.elim (H A.path.cubic) (Sum.elim (H A.path.quartic) (Sum.elim (H A.path.loop) fun _=> 1)))
-- inlet read with E at ζ/g(s). Auditor predictor disc reads only `path` & `budget_t`; vest inject not typical virtual beta. K deliberately empty amplitude
-- Keep ALL predicates/bar readers by copying R even though no evaluation by formulas.
def vest (R:Rep G f)(Φ:ℕ→ℝ→ Config G f→ℝ) (s:ℝ) := { R with beta:=(s^2)⁻¹, activities:= {R.activities with E:=fun i=> Φ i s, K:=fun _=>0}, v:=0 }
lemma fadesA (X:Coat T F)(A:ℕ→Atom G m)(i:Trans f)(q:ℝ)(z:Air f G)(s:ℝ): atomΛ X A i (-((s^2)⁻¹)*Raw.orientation*q) z=(s^2)⁻¹ • atomΛ X A i (-Raw.orientation*q) z:=by funext x; unfold atomΛ; change _ = (s^2)⁻¹* _; ring
set_option maxHeartbeats 200000 in
lemma weftCross {P:Teller G}(Q:ConnectedActivityE6.Target G P) (W:ℝ)(o:Target.Order G W) (L:Side)(D:Patch)(hd:D.Branches P.bind G){p:ℝ→ℝ}(hk: v<0)(hv: -(1/2:ℝ) ≤ v) (hp: Rate G L v p) (he:∀ᶠ x:ℝ in atTop,0 < p x) {d b b':ℝ→ℝ}{N I:ℝ→ℕ}(hD:Rate G L 0 d)(hB:Rate G L 0 b)(hz: Rate G L 0 b')(hI:Rate G L 0 fun t=>(I t:ℝ))(hN:Rate G L 0 fun t=>(N t:ℝ))(hκ:Reliable G κ k₁) (hG:G.Simple) (j K k:ℕ)(h₀:1≤j):
    ∃ E:ℝ→ℝ, Rate G L 0 E∧∀ᶠ t in atTop, 0<b t→0≤ b' t →∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D→∀(R:Rep G f) (η α:ℝ)(_H : Cash W t η L Q o α T R),∀ (F:Forest S.ratio)(X:Coat T F), X.x=t→ X.width=o.K→∀ (q:Air f G), (∀ i,|q i|≤ |d t|)→∀(φ:ℕ→ℝ)(Φ:ℕ→ℝ→ Config G f→ℝ), ∀ i:Veil c f,
       0 ≤ ratioCash R (b t) φ i → labelGrade R κ Φ φ (N t) (I t) K k (b' t) i → Plume (max 2 K) j (max k 2) (fun s x=> Fan.coming Q.table (Fan.vest R Φ s) X x q i) (ratioCash R (b t) φ i * (E t)) (p t):=by
   have hp': ∀ᶠ x:ℝ in atTop,0≤p x:= he.mono fun _ h=> h.le
   obtain ⟨A,hA,hp₁⟩:= cloudCard L D hd Q o j h₀ hv hk hp hp' hκ hD hN
   obtain ⟨V,hV,hP⟩:= vaulted L D hd Q W o j h₀ hv hk hp hD hp'
   obtain ⟨U,hU,hP'⟩:= freezeBase L D hd j h₀ o.f hk hp hp'
   obtain ⟨W',hW,hP₀⟩:= sunlit Q L D hd o j h₀ hv hk hp hD hp'
   obtain ⟨M,Z,E₁,hZ,hL,hE,H⟩:= thistles L D hd Q W o j h₀ hv hk hp hD hp'
   have hw: |-Raw.orientation| ≤ 1:=by rw [abs_neg,abs_of_pos orientation_range.1]; exact orientation_range.2
   obtain ⟨T₁,h₁,H₁⟩:= tassels L D hd Q o j 3 h₀ hv hk hp hp' (Rate.const (1:ℝ)) hD hI
   obtain ⟨T₂,h₂,H₂⟩:= tassels L D hd Q o j 4 h₀ hv hk hp hp' (Rate.const (1:ℝ)) hD hI
   obtain ⟨T₃,h₃,H₃⟩:= tassels L D hd Q o j 2 h₀ hv hk hp hp' (Rate.const (1:ℝ)) hD hI
   obtain ⟨H₄,r,hr,h₄⟩:= Vine.ceilings D hd j
   obtain ⟨R,hr',hr₂,Ω,hω,H'⟩:= Frond.growth P L D hd j
   obtain ⟨Z₀,E,hV₀,hE',HZ⟩:= driftless P L D hd j h₀ hk hp hp' o.f
   let f x:= b' x * Scene.scoreBp k j (A x)
   let t x:= b x* (|T₁ x| + |T₂ x| + |T₃ x|)
   let E' x := |f x| + (|t x| + (|V x| + |U x| + |W' x|))
   have hmax (v:ℝ→ℝ)(h:Rate G L 0 v):Rate G L 0 (fun x=>|v x|):= h.compare (Eventually.of_forall fun x=> (abs_abs _).le)
   refine ⟨E',Rate.add (hmax _ (by unfold f Scene.scoreBp; simpa only [add_zero,zero_mul] using! (hz.mul (((hA.pow k).mul_left (k:ℝ)).mul_right ((1+(k:ℝ))^j))))) ((hmax _ ((hB.mul (((hmax _ h₁).add (hmax _ h₂)).add (hmax _ h₃))).weaken (by linarith))).add (((hmax _ hV).add (hmax _ hU)).add (hmax _ hW))),?_⟩
   filter_upwards [hp₁,hP,hP',hP₀,H,H',H₁,H₂,H₃,HZ,he] with t' hP'₁ hv hU hw' hT hZ' h₁ h₂ h₃ hZ hp hb hb' c f' S T hk' R η α H' F X hx hK v hB g Φ i hh he
   let C:= p t'; have hL:= H'.laws.data; let V':=(0:Disk G c); have hx': ‖V'‖<C:= norm_zero.trans_lt hp
   have hθ:= hL.funds.funds; have hu':= hL.localP F X.blank hx hK (X.bowed (temp_nonneg _)); have hm:=hT c f' S T hk' _ _ hL F X hx hK v hB _ hx'.le; have A₁: max 1 j=j:=max_eq_right h₀
   let R':=R.path
   let A':= Raw.orientation
   have ht (d:ℕ)(F:ℕ→ Atom G (d+1))(i:Trans f') (U:ℝ) (he : (F i.2.2).Invariant) (HP:U*b t' ≤ E' t')(h:∀ z:Disk G c,‖z‖<p t' → Brush j ((F i.2.2).magnitude*U) 1 (atomΛ X F i (- A') v) z):
       Plume (max 2 K) j (max k 2) (fun s=> atomΛ X F i (-((s^2)⁻¹)* A') v) ((F i.2.2).magnitude / (b t')*(E' t')) C :=by
        have hh: Null 2 j (atomΛ X F i (-A') v):= chargeAtom (n:=j) X hG v hθ F i (-A') R.p j he (A₁.symm ▸ (Blaze.turn hm.2.2 i.1))
        have hT:= Plume.fade (f:=atomΛ X F i (-A') v) (show 0 < p t' from hp) hh h -- edit
        rw [show (fun s=> atomΛ X F i (-((s^2)⁻¹)* A') v)=(fun s:ℝ=> (s^2)⁻¹ • atomΛ X F i (-A') v) from funext fun s=>by simpa only [mul_one] using! fadesA X F i 1 v s];
        exact hT.esteemed (le_max_left ..) (le_max_right ..) ((by rw [div_mul_eq_mul_div,mul_div_assoc]; exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hb).mpr HP) (sum_nonneg fun _ _=> abs_nonneg _))) le_rfl
   have f0:f t'≤ E' t':= (le_abs_self _).trans (le_add_of_nonneg_right (by positivity)); have hK':= H'.laws.intake.cap.paths
   have ht': t t' ≤ E' t':= by unfold E'; linarith only [abs_nonneg (f t'), le_abs_self (t t'),abs_nonneg (V t'),abs_nonneg (U t'),abs_nonneg (W' t')]
   rcases i with i|i|i|i|i
   · obtain ⟨N,hN,x,hQ⟩:= (show CanX .. from he).basis
     have he:= fun x'' (hx'':‖x''‖<C)=> hP'₁ c f' S T hk' _ _ hL F X hx hK v hB x'' hx'' _ N x hN
     have ht:=climbing X hθ (R.activities.reg i).site x v R.p hQ hκ j hp (fun u hu=> (he u hu).2) (he _ hx'|>.1)
     exact ht.negative.esteemed (le_max_right ..) (le_max_left ..) (show _≤_ from mul_assoc (g i) _ _|>.trans_le (mul_le_mul_of_nonneg_left f0 hh)) le_rfl
   · refine ht 2 R.path.cubic i |T₁ t'| (hK'.invariant i.2.2|>.2.1) (le_trans (?_) ht') (fun z hz=>h₁ c f' S T R.path.cubic hk' _ _ hL F X hx hK v hB _ hz.le i (-A') (by exact_mod_cast (show _ ≤ I t' from he)) hw); unfold t; have hx:= abs_nonneg (T₂ t'); have hy:= abs_nonneg (T₃ t'); nlinarith
   · refine ht 3 R.path.quartic i |T₂ t'| (hK'.invariant i.2.2|>.2.2) (le_trans (?_) ht') (fun z hz=>h₂ c f' S T R.path.quartic hk' _ _ hL F X hx hK v hB _ hz.le i (-A') (by exact_mod_cast (show _ ≤ I t' from he)) hw); unfold t; have hx:= abs_nonneg (T₁ t'); have hy:=abs_nonneg (T₃ t'); nlinarith
   · have he₁:= Plume.unchanged (f:=atomΛ X R.path.loop i (-A') v) (Q:=max k 2) hp fun z hz =>h₃ c f' S T R.path.loop hk' _ _ hL F X hx hK v hB _ hz.le i (-A') (by exact_mod_cast (show _ ≤ I t' from he)) hw
     refine he₁.esteemed (Nat.zero_le (max 2 K)) le_rfl (show _≤ (R.path.loop i.2.2).magnitude/b t'*E' t' from ?_) le_rfl; rw [div_mul_eq_mul_div,mul_div_assoc]; refine mul_le_mul_of_nonneg_left ((le_div_iff₀ hb).mpr (le_trans (?_) ht')) (sum_nonneg fun _ _=> abs_nonneg _); unfold t; have hx:= abs_nonneg (T₁ t'); have hy:=abs_nonneg (T₂ t'); nlinarith
   change Plume _ _ _ _ (1*E' t') _; rw [one_mul]; rcases i with i|i|i
   · have hg z (hz:‖z‖<C):= hv c f' S T hk' _ _ hL F X hx hK v hB z hz.le i
     have hp' : (j:WithTop ℕ∞)≠0:=by exact_mod_cast (show j≠0 from (by omega))
     have hTZ:= hZ c f' S T hk' hL.funds F X hx hu'.sails.scale (0:ZipP G c f') (by rw [norm_zero]; exact hp.le)
     have he := workIvy X hG hθ v i (hm.2.1.smooth.differentiableAt hp') ((h₄ c f' S T hθ hk' i.1 0 (by rw [norm_zero]; exact hr.le)).smooth.differentiableAt hp') ((show Brush j (Ω t') 1 (ivy T X.x (choice i.1 X.k) i.2) 0 from (by rw [hx]; exact hZ' _ _ _ _ hk' hL.funds.length_eq hL.room i.2 (choice i.1 X.k) 0 (by rw [norm_zero]; exact hr'.le))).smooth.differentiableAt hp') (fun k _=> ?_) j
     swap
     · let p0:= sideways (f:=f') (G:=G) (c:=c)
       have hx:= ((hTZ.2 (i.1,k)).smooth.differentiableAt hp'); rw [← map_zero p0] at hx; exact hx.comp _ p0.differentiableAt
     let K0:=fun s:ℝ=> (-A') • (((s^2)⁻¹:ℝ) • sourceΛ X i v)
     have hh:= Plume.fade (m:=2) (k:=j) (f:= sourceΛ X i v) hp he (fun z hz=> hg z hz)
     have hz: Plume 2 j 2 K0 (|-A'| * V t') C:= ⟨hh.jet.scales (-A'),fun i hi x hx=> ((hh.scope i hi x hx).smul (-A')).climb (le_of_eq (mul_div_assoc _ _ _|>.symm)) le_rfl⟩
     change Plume _ _ _ (fun s x=> -((s^2:ℝ)⁻¹)* A'* (sourceΛ X i v x)) _ _
     rw [show (fun s :ℝ=>fun x=>-((s^2:ℝ)⁻¹)* A'* (sourceΛ X i v x))=K0 from funext fun s=>funext fun x=>by dsimp only [K0,Pi.smul_apply,smul_eq_mul]; ring]
     have hf: V t' ≤ E' t':= by unfold E'; linarith only [abs_nonneg (f t'), abs_nonneg (t t'), le_abs_self (V t'), abs_nonneg (U t'), abs_nonneg (W' t')]
     exact hz.esteemed (le_max_left ..) (le_max_right ..) ((mul_le_of_le_one_left hh.jet.nonneg hw).trans hf) le_rfl
   · refine (Plume.unchanged (f:=fun z=> (timeΛ X z).undercurrent i) hp (fun z hz=> hU c f' S T hk' hL.funds F X hx hu'.sails.scale z hz.le i)).esteemed (Nat.zero_le _) le_rfl (?_) le_rfl; unfold E'; linarith only [abs_nonneg (f t'), abs_nonneg (t t'),abs_nonneg (V t'),le_abs_self (U t'),abs_nonneg (W' t')]
   refine (Plume.unchanged (f:=fun z=> Vine.solar X v Q.table z i) hp (fun z hz=> hw' c f' S T hk' _ _ hL F X hx hK v hB z hz.le i)).esteemed (Nat.zero_le _) le_rfl (?_) le_rfl; unfold E'; linarith only [abs_nonneg (f t'), abs_nonneg (t t'),abs_nonneg (V t'),abs_nonneg (U t'),le_abs_self (W' t')]
end YM.LocalLTE.Fan
