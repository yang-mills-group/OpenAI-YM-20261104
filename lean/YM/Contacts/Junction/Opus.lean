import YM.Contacts.Junction.Indian
/-! # per-station Rate-frame wires. T.Charge.
 Cube coordinate aftermath.Delta. Root piece. Before.Super. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} (P : ChartRatio G) {σ C e v d t K τ ω':ℝ}{n k j r:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current
open Sienna Lantern Planned.JetPort Dew
open Uniform Push.AbsoluteSums
section price
variable {W : Type} [Fintype W]
private lemma honor (f:Field (Fin (k+1)) W) (x:House.Dir W): jet (design f) (k+1) x= design f x:= by rw [radiant (design_ana f _) _ _ (design_power _),if_pos rfl]
lemma gap_exit (X:House W)(x:ℝ×House.Dir W): Radar.gap (swell X j) x=∑ i∈Finset.range j, x.1^i * ∑ k∈ Finset.range (j-i), if 0< k then grate X i k x.2 else 0 := by
   unfold Radar.gap swell stake; rw [← sum_sub_distrib]; apply sum_congr rfl; intro i hi; unfold conjunct; rw [← mul_sub]; apply congr_arg; unfold wind; rw [← sum_sub_distrib]; apply sum_congr rfl; intro k hk; rcases k with _|k
   · unfold grate; split; next h=> rw [if_neg (by decide)]; rw [design_spec, design_spec]; simp
     simp
   rw [if_pos (Nat.zero_lt_succ _)]; unfold grate; split; · rw [show design (X _ _) 0=0 from ?_,sub_zero]; let f:= X (i+(k+1)-2) (k+1); simpa using design_power f 0 0
   simp
end price
variable {U:Teller G}{D:ℕ→Dew G}{g v f K a w:ℕ→ℝ}{b:ℕ→BudgetPoint}{L:Side} {M:Uniform.ChartPrices}
variable {N:Meter} (hp:Pouch N (- (1/2:ℝ)) g)
local notation "Φ" => (fun i=>Dew.Q (D i))
variable (ht: ∀ᶠ i in atTop,Pearl U (v i) (f i) L σ C M n (b i) (D i)) (hv:N.Rush 0 v) (he: N.β=ᶠ[atTop] (fun i=> betaF G (f i) L)) (hh:Tendsto f atTop atTop)
local notation "Z" => (N.pow stashp)
section fallback
variable {E F γ I : ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i, Fintype (I i)]
    {V:∀ i, House (I i)}{X: Shelf E γ (fun i=>ℝ×House.Dir (I i))}{Zr:Frame γ E}
structure Spectrum (N:Meter)(k:ℕ)(S:∀ i, House (I i)) (p:ℝ):Prop where
   pays (j e:ℕ)(h:e+j<k+3) (hv:e≠0): N.Funds (fun i r=> Rooted (Range.cheap _) (S i (j+e-2) e) r) p
   card : N.Rush 0 fun i=> (Fintype.card (I i):ℝ)
lemma gap_shield (hx:Budget N Zr n 0 X)(h: Spectrum N k V τ): Budget N Zr n τ (fun i j x=> Radar.gap (swell (V i) (k+3)) (X i j x)):= by
   simp_rw [gap_exit]; let t i j x:= (X i j x).1; let Y i j x:= (X i j x).2; let a i e r j x:= if 0< e then grate (V i) r e (Y i j x) else 0; let B(r:ℕ)(e:ℕ):= fun i j x=> a i e r j x;
   have he r e (hh:e+r<k+3): Budget N Zr n τ (B r e):= by
       by_cases hp:0<e ∧ 2≤r+e; swap; · unfold B a grate; refine Arms.cheaper ?_ Budget.zero; funext i j x; split_ifs <;> tauto
       cases e; · omega
       rename_i e; let W i:= V i (r+(e+1)-2) (e+1); let J(i:ℕ) := design (W i); have hO : B r (e+1)=fun i j x=>jet (J i) (e+1) (Y i j x):= by funext i j x; rw [honor]; change (if _ then _ else _)=_; simp only [if_pos hp.1,grate,if_pos hp.2,W];
       obtain ⟨f,hf,H⟩:= (h.pays r _ hh (by omega)).cap; let t(i:ℕ):=(Fintype.card (I i):ℝ)*f i; rw [hO]; refine Arms.lo (Budget.jetcap (f:=Y) (sndD hx) (Current.jetBudget (O:=J) (H:=t) (j:=e+1) (H.mono ?_) (h.card.times hf (zero_add _)))) (le_of_eq (by ring)) le_rfl; intro i h; refine ⟨design_ana ..,fun x=> ?_⟩; rw [honor]; exact tail_price (Range.cheap _) _ h.2 -- should h.2
   refine Budget.spike (a:=fun r i j x=>(t i j x)^r * ∑ e∈Finset.range (k+3-r),B r e i j x) (fun r h'=>Budget.mul _ _ (Budget.power (A:=t) (fstD hx) r) (Budget.spike (a:=B r) (fun i (hi:i∈ Finset.range (k+3-r))=>he r i (by simp only [Finset.mem_range] at h' hi; omega))) ?_); ring
lemma gap_analytic {i:ℕ}(_w:Spectrum N k V τ) : AnalyticAt ℝ (Radar.gap (swell (V i) (k+3))) 0:= by -- remove d and i error
   let x:ℝ × House.Dir (I i)→L[ℝ] ℝ × House.Dir (I i):=(ContinuousLinearMap.fst ℝ _ _).prod 0; let t:= swell (V i) (k+3); exact (orchestra ..).sub (g:=t ∘ x) (starts t (orchestra ..) x)
lemma gap_root (h:Spectrum N k V τ) : Root N (fun i=> Radar.gap (swell (V i) (k+3))) n τ (N.pow stashp):= ⟨gap_shield (Current.meetP Meter.Rush.any (by norm_num [stashp])) h, Eventually.of_forall fun i=>gap_analytic h⟩
lemma registry {W : Type}[NormedAddCommGroup W][NormedSpace ℝ W][FiniteDimensional ℝ W](P:ℝ× W→ℝ) : AnalyticAt ℝ P 0 → Radial.Stationary P → Radial.Stationary (Radar.gap P):= by
   intro hp h; let f: ℝ × W →L[ℝ]ℝ × W:=(ContinuousLinearMap.fst ℝ _ _).prod 0; have hz:Radar.gap P=P-P∘f:=rfl; have hf:= starts P hp f; refine ⟨(hz ▸ (hp.sub hf).contDiffAt), sub_self (P 0),fun x=>?_⟩; rw [hz,jet_minus _ _ _ _ hp hf, Milling.Garf.woven hp f,h.base1,h.base1,sub_self] -- FiniteDim W needed
end fallback
section frame
variable {m n:ℕ}{E V:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
    {γ:ℕ→ℝ}
-- d:B.Stamp eaves
lemma t_scale (h:N.Rush fit f)(hs:N.Rush fit γ)(hu:N.Rush 0 a) (hv:N.Rush 0 g) : Narrow (E:=E) (V:=V) N k fit g a (fun i (z:V i) (x:E i)=> ((γ i, f i • x), γ i • z)) := by -- g=frame radius possibly fixed (>0).
    let Ξ(i:ℕ):Type:=stepIn E V g a i; let x i (p:Ξ i):= Loom.Patch.arm p; let y i (p:Ξ i):= leg p;
    have he: Budget N x k fit (fun i _ (z:E i)=> f i • z):= Arms.weighted (Budget.id (x:=x) (E:=E) ?_) h (zero_add _); swap; · exact ⟨_, absolute hv, (Eventually.of_forall fun i=>⟨ abs_nonneg _, fun j=> (mem_ball_zero_iff.mp (belongs j).1).le.trans (le_abs_self _)⟩) ⟩ -- want choose |g|
    have h' : Budget N x k fit (fun i j _=> γ i • y i j):= Arms.weighted (Budget.const y (Funds.mk ⟨_,absolute hu, Eventually.of_forall fun i=>⟨abs_nonneg _,fun j=> (mem_closedBall_zero_iff.mp (belongs j).2).trans (le_abs_self _)⟩⟩)) hs (by ring); exact (Budget.stack (Budget.stack (Budget.tally γ hs) he) h') -- syntax fixed
private lemma packetP {X Q Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Q][NormedSpace ℝ Q][NormedAddCommGroup Y][NormedSpace ℝ Y]{f:X→Q}{g:X→Y}{a b:ℝ}{x:X}(h:Brush k a 1 f x)(ht:Brush k b 1 g x): Brush k (a+b) 1 (fun x=> (f x,g x)) x:= by
   have hh := h.report (ContinuousLinearMap.inl ℝ Q Y) (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp [Prod.norm_def])); have hc := ht.report (ContinuousLinearMap.inr ℝ Q Y) (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp [Prod.norm_def])); have he := hh.gathering hc; simpa using! he
lemma t_full (h:N.Rush fit f)(hs:N.Rush fit γ)(hv:N.Rush 0 g) : Loom.Patch.Joint (E:=E) (V:=V) N k fit g (fun i (z:V i) (x:E i)=> ((γ i, f i • x), γ i • z)) := by
   obtain ⟨p,hp,H⟩:= (Budget.id (k:=k) (Frame.head (E:=E) (d:=g) hv)).cap;
   let q i := (‖γ i‖+ ‖f i‖*p i)+‖γ i‖; have hq: N.Rush fit q := ((absolute hs).blend ((absolute h).times hp (add_zero _))).blend (absolute hs); refine ⟨1,_,hq,H.mono fun i hi=>?_⟩; have ht :0≤q i:= add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hi.1)) (norm_nonneg _); refine ⟨ht,fun v x hx=>?_⟩; let Φ':= buoy v; have he (a:ℝ)(ha:0≤a): a≤ a*Φ':= le_mul_of_one_le_right ha (hovering _)
   rw [pow_one];  let o: Frame.Bank E g i:= ⟨x,hx⟩; have hx' :=  (packetP (Brush.certified zero_le_one (x:=x) (k:=k) (γ i)) ((hi.2 o).smul (f i))); apply (packetP hx' (Brush.certified zero_le_one (γ i • v))).climb _ le_rfl; unfold q; rw [add_mul,norm_smul]; refine add_le_add (he _ hx'.nonneg) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
end frame
end Provision
end YM.Contacts.Junction
