import YM.LocalLTE.Weft.Reap
import YM.LocalLTE.Motion.Half
/-! Wt locality sampler Ψ conditional cost. -/
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
variable (X:Coat T F) (Φ:ℕ→ℝ→ Config G f→ℝ) {μ:ℝ}
open Bakers
-- stage.LT.Demand. convergence in saint.Append.D holds R only, craft arbitrary.He.Taylor.
def cubeF (q p j:ℕ)(V W:ℝ):= V*(W^q)^p*(1+(1+(p:ℝ)*q))^j
lemma latticePins {P:Teller G}(Q:ConnectedActivityE6.Target G P) (W:ℝ)(o:Target.Order G W) (L:Side)(D:Patch)(hd:D.Branches P.bind G){b b' M:ℝ→ℝ}{N I:ℝ→ℕ}(hB:Rate G L 0 b)(hz: Rate G L 0 b')(hI:Rate G L 0 fun t=>(I t:ℝ))(hN:Rate G L 0 fun t=>(N t:ℝ))(hM:Rate G L 0 M)(hκ:Reliable G κ k₁) (hG:G.Simple) (j K k p q:ℕ)(h₀:1≤j):∃ E:ℝ→ℝ, Rate G L 0 E∧∀ᶠ t in atTop, 0<b t→0≤ b' t →0≤ E t∧∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D→∀(R:Rep G f) (η α:ℝ)(_H : Cash W t η L Q o α T R),∀ (F:Forest S.ratio)(X:Coat T F), X.x=t→ X.width=o.K→∀(φ:ℕ→ℝ)(Φ:ℕ→ℝ→ Config G f→ℝ), ∀ A:Finset (Veil c f), A.card≤p→ ∀ Y:Finset (Tubular f G), (Y.card:ℝ) ≤ M t → (∀ i∈A,0 ≤ ratioCash R (b t) φ i ∧ ratioCash R (b t) φ i≤1 ) → (∀ i∈ A,labelGrade R κ Φ φ (N t) (I t) K k (b' t) i)→ ∀ z: LevelsΛ A q,
          Warp (max 2 K*q*p) j ((∏ i∈A,ratioCash R (b t) φ i)* E t) (fun s x=> Bakers.curlP X (vest R Φ s) A Q.table (postponement L t o) Y x z) :=by
   let a x:= betaF G x L^(-(1/2):ℝ); have ha: Rate G L (-(1/2)) a:= Rate.power; let d t:=Fan.postponement L t o
   have hdz: Rate G L 0 d:= ((show Rate G L 0 (fun t=>Delay.fineMonitor G L t /2) from (by simpa only [div_eq_mul_inv] using! ((Rate.monitor (G:=G) (L:=L)).mul_right (2:ℝ)⁻¹))).mul_left _)
   have hp: ∀ᶠ t in atTop,0 < a t:= (Delay.shift_pos G L).mono fun t ht=>Real.rpow_pos_of_pos ht _
   obtain ⟨V,hV,hQ⟩:=weftCross Q W o L D hd (by norm_num) le_rfl ha hp hdz hB hz hI hN hκ hG j K k h₀
   obtain ⟨A,hA,hP'⟩:=Vine.newness G L D hd o.f j h₀ (by norm_num) ha hM hdz (hp.mono fun _ h=> h.le)
   let w x:= 1+|V x|; let C x:= |A x|; let E t:= cubeF q p j (C t) (w t)
   have hw: Rate G L 0 w:= (Rate.const 1).add (hV.compare (v:=fun x=>|V x|) (Eventually.of_forall fun x=>(abs_abs _).le)); have hC: Rate G L 0 C:= hA.compare (v:=fun x=>|A x|) (Eventually.of_forall fun x=>(abs_abs _).le)
   refine ⟨E,by simpa only [zero_mul,add_zero] using! ((hC.mul ((hw.pow q).pow p)).mul_right ((1+(1+(p:ℝ)*q))^j)),?_⟩
   filter_upwards [hQ,hP',hp] with t hz hv hZ hB hp' ; have hw:1≤ w t:=le_add_of_nonneg_right (abs_nonneg _); have he : 0≤ C t:=abs_nonneg _; have hP:0≤E t:=by unfold E cubeF; positivity; -- edit
   refine ⟨hP,fun c f S T hS R η α H F X hx hK φ Φ A Y Y' hM hL hD z=>?_⟩
   let I':= cabinet Y' (postponement L t o); let u(s:ℝ)(x:Disk G c)(y:Body (↥Y')):=songP X (vest R Φ s) A Q.table Y' x y z
   let V s (x:Disk G c):= (I').indicator (u s x)
   let πZ i:=ratioCash (c:=c) R (b t) φ i; let K':=max 2 K; let L₀:=max k 2; let M:= K'*q*p; let P' := ∏ i∈A, πZ i
   have hPt: 0≤P':=prod_nonneg fun i hi=> (hL i hi).1
   have ht:0 ≤ postponement L t o:= by unfold postponement; have hv:=(Delay.monitor_pos G L t); have hh:=o.rare; positivity -- edit
   let S'(u:ℝ):= P'*cubeF q p j (C t) u
   let U(y:Body (↥Y')) (s:ℝ) (x:Disk G c):= coming Q.table (vest R Φ s) X x (Pond.spill Y' y)
   have HH y (hi:y∈I') (i:Veil c f)(hh:i∈A): Plume K' j L₀ (fun s x=> U y s x i) (πZ i*(w t)) (a t):=by
      refine (hz hB hp' c f S T hS R η α H F X hx hK _ (fun i=> (fur Y' hi ht i).trans (le_abs_self _)) φ Φ i (hL i hh).1 (hD i hh)).esteemed le_rfl le_rfl (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) (hL i hh).1) le_rfl
   let f (y:Body (↥Y')) (x:Disk G c):= pledgeΛ X Y' y (Vine.pass x)
   have hL' y (hi:y∈I')(x:Disk G c)(hu:‖x‖< a t): Brush j (C t) 1 (f y) x:= by
       have h' := Brush.reading sideways ((hv _ _ S T F X Y' hx hS H.laws.data.funds (H.laws.data.localP F X.blank hx hK (X.bowed (temp_nonneg _))).sails.scale hM y (fun i=> (show ∀ i₀, _ ≤ postponement L t o from fun i₀=> hi i₀|>.trans le_rfl) i|>.trans (le_abs_self _)) (Vine.pass x) ((Vine.tally ..).trans hu.le)).1) norm_side -- edit
       rw [mul_one] at h'; exact h'.climb (le_abs_self _) le_rfl
   have hF (y:Body (↥Y')): Arp M j (P'*E t) (fun s x=>V s x y):=by
       by_cases he:y∈I'
       swap; · have he' : (fun s x=>V s x y)= fun (_:ℝ)(_ : Disk G c)=> (0:ℝ):=funext fun s=>funext fun x=> Set.indicator_of_notMem he _; rw [he']; exact Arp.zero'.climb le_rfl (mul_nonneg hPt hP)
       unfold V; simp_rw [Set.indicator_of_mem he]; constructor
       · have h':Hex (K'*q*A.card) (fun s x=> lilies A (U y s x) z):= profileHex K' q A (fun i hi=> (HH y he i hi).jet.hex) z -- edit
         refine Hex.invert fun x=>?_ ; exact ((Hex.constant (k:=0) (f y x)).mul (h'.use x)).grow (by unfold M; rw [zero_add]; gcongr)
       intro s hs; have he':Brush _ _ _ (fun x : Disk G c=> lilies A (U y s (s • x)) z) 0:= cargo p A πZ (s:=s) (F:=fun s x=>U y s (s • x)) (fun i hi=> (HH _ he i hi).jet.brush s hs) hw hL q z Y
       exact ((((Weft.orb_cost s (hL' _ he 0 (by rw [norm_zero]; exact hZ)) hs).paints he').trim).climb (le_of_eq (by unfold E cubeF P'; ring)) le_rfl) -- edit
   have hp' s (hs:s∈clip) : ∃ B:ℝ,∀ᶠ y:Disk G c in 𝓝 0,∀ i, Brush j B 1 (fun y=> V s y i) y:=by
       let q':= w t/s^L₀; have hw' : 1 ≤ q' := by apply le_trans hw; exact (le_div_iff₀ (pow_pos hs.1 _)).mpr (mul_le_of_le_one_right (zero_le_one.trans hw) (pow_le_one₀ hs.1.le hs.2))
       refine ⟨S' q',?_⟩; filter_upwards [ball_mem_nhds (0:Disk G c) hZ] with x hx y; by_cases he':y∈I'; swap
       · apply Brush.zi (Eventually.of_forall fun x=> Set.indicator_of_notMem he' _) _ zero_le_one; unfold S' cubeF; positivity
       have h': ‖x‖< a t:= mem_ball_zero_iff.mp hx; have he'' i (hi:i∈ A): Brush j (πZ i*q') 1 (fun v=> U y s v i) x := ((HH _ he' i hi).scope s hs _ h').climb (le_of_eq (by unfold q'; ring)) le_rfl
       unfold V; simp_rw [Set.indicator_of_mem he']; exact ((((hL' y he' x h').paints (cargo p A πZ he'' hw' hL q z Y)).trim).climb (le_of_eq (by unfold S' cubeF P'; ring)) le_rfl) -- edit
   have hx:= Warp.load (μ:=Fan.pool Y' X 0) hF hp' (fun s hs=>Eventually.of_forall fun x=> (canvasT X Φ H hx hK hκ K (N t) (I t) k φ A hD _ hs x z Y').indicator (Fan.alive Y' _))
   rwa [show (fun t p=> Bakers.curlP X (vest R Φ t) A Q.table _ Y' p z) = (fun s x=> ∫ i,V s x i ∂Fan.pool Y' X 0) from funext fun s=>funext fun p => (MeasureTheory.integral_indicator (alive Y' _)).symm]
end YM.LocalLTE.Fan
