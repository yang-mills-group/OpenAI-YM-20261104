import YM.Juniper.Mulberry.Uplink
/-!
 # Interval price for ALL Tilt. Explicit penalty of extra order for using scale
 larger than the shrinking actual fields. Copies (before Φ projections!)
 uniform every fixed r. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern RG Wilson Pressure Lattice
open ConnectedActivityE6 Blaze Brush Poll Sienna
open Work.G05 WilsonStartup Analysis Tensor
open LocalAtlas
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {G:Gauge} {c f L:Side}{q M s l p w Z d C A W V:ℝ} 
open Push Push.AbsoluteSums
section cost
variable {v r t y P g:ℝ→ℝ} (k n:ℕ)
local notation "r!"=> Rate G L
private lemma unit_mul (h:r! 0 v)(hp:r! p t):r! p (fun x=> v x*t x):= by simpa only [zero_add] using! h.mul hp
private lemma mul_unit (h:r! p v)(hp:r! 0 t): r! p (fun x=> v x*t x):= by simpa only [add_zero] using! h.mul hp
local notation "λ"=> vow
noncomputable def sacred : ℝ:= -(3/8:ℝ) -- in β_hat
local notation "T"=> betaF G
noncomputable def shadow (G : Gauge)(L:Side)(x:ℝ):= betaF G x L ^ sacred
local notation "ε"=> shadow G L
local notation "E"=> eaves G L
-- Effective PAID radius for all-order confirmation
noncomputable def silver : ℝ:= vow-sacred
local notation "V"=> (fun x=> E x / ε x)
noncomputable def drive (n:ℕ):ℝ:= silver*(n+1:ℕ)
noncomputable def puff (G:Gauge)(L:Side)(x: ℝ)(n:ℕ):ℝ:= betaF G x L ^ drive n
local notation "H"=> (fun x=>puff G L x n)
lemma pitch : ∀ᶠ x in atTop,V x= T x L ^ silver:= by
     filter_upwards [Delay.shift_pos G L] with x hx; unfold silver shadow eaves; exact (Real.rpow_sub hx ..).symm
private lemma revenue : Rate G L silver V:= by refine Rate.congr Rate.power pitch
lemma toll : ∀ᶠ x in atTop,H x=(V x)^(n+1):= by
    filter_upwards [pitch (G:=G) (L:=L),Delay.shift_pos G L] with x hx hp; rw [hx]; unfold puff drive; rw [Real.rpow_mul hp.le,Real.rpow_natCast]
lemma downhill : silver < 0:= by norm_num [silver,sacred,vow]
lemma downhill2 : drive n<0:= mul_neg_of_neg_of_pos downhill (by exact_mod_cast (Nat.succ_pos _))

lemma cabin (h:r! 0 v)(Z:ℝ): Rate G L 0 (fun x=> gamut (v x) Z k):= Brim.bell (Brim.prep ((Rate.const 1).add h) k) ((Rate.const 1).add (h.mul_right _)) -- adaptive from LocalAtlas
lemma mores (h:r! 0 r)(hp:r! 0 v)(ht:r! 0 t): Rate G L 0 (fun x=> Mulberry.travelW k (r x) (v x) (t x)):= by
    let z x:= spanE (r x) (v x); have hY := ((Rate.const 1).add h).add hp
    have hL: Rate G L 0 z:= hY.add hY; have hM:= Brim.bell hp (Brim.bell hp (lumpRate k hL h)); exact ((fareRate k h hp).add (hM.mul_left 2)).add (ht.mul_right _)
variable (h:Rate G L 0 r)
variable (hp : Rate G L 0 v) (ht: Rate G L 0 t) (hu: Rate G L 0 P)
local notation "F"=> (fun x=> travelW k (r x) (v x) (t x))
local notation "f'"=> (fun x=> freightJ k (r x) (v x) (t x) C Z (puff G L x n) (P x))
local notation "v'"=> (fun x=> tokens k (r x) (v x) (t x) C Z (P x))
local notation "y'"=> (fun x=>clump k (fee k (r x) (v x)+t x) Z)
local notation "g'"=> (fun x=> cost0 k n (y' x) (V x) (f' x))
local notation "w'"=> (fun x=> puff G L x n)
local notation "Q'"=> (fun x:ℝ=> overhead n k * v' x)
local notation "λ!"=> (fun x=> ticket k n (r x) (v x) (t x) C Z (w' x) (P x) s (V x))
include h hp ht hu
lemma rightForce (s₀ C : ℝ) : Rate G L 0 (fun x=> clump k (travelW k (r x) (v x) (t x)) s₀ * (gamut (P x) C ((k+2)*k))):= Brim.bell (lumpRate k (Mulberry.mores k h hp ht) (Rate.const _)) (cabin _ hu C)
lemma rescue : Rate G L (drive n) f':= by
    have hw:r! (drive n) H:= Rate.power; refine unit_mul (lumpRate k (mores k h hp ht) (Rate.const _)) ((mul_unit hw (cabin _ hu C)).add ?_); refine hw.congr ?_; filter_upwards [Delay.shift_pos G L] with x hx; let i:= puff G L x n; have h:0 < i:= Real.rpow_pos_of_pos hx _; change i^2*i⁻¹=i; field_simp
omit hu in
lemma homegrown : Rate G L 0 y':= lumpRate k ((fareRate k h hp).add ht) (Rate.const _)
lemma budged : Rate G L (drive n) g':= by
    have hh : r! 0 y':= homegrown k h hp ht; exact (unit_mul (hh.add (hh.mul_left _)) ((revenue (G:=G) (L:=L)).pow (n+1))).add ((rescue k n h hp ht hu).mul_left _)
lemma wealth : Rate G L (drive n) λ! := by
    have hh : r! 0 y':= homegrown k h hp ht; have hf : r! 0 Q':=(rightForce k h hp ht hu Z C).mul_left _; have hg : Rate G L 0 (fun x=>clump k (Q' x) s):= lumpRate k hf (Rate.const s); exact ((mul_unit (budged k n h hp ht hu) (lumpRate k ((hh.add hf).mul_left _) (Rate.const s))).mul_left _).add (unit_mul (hg.add (hg.mul_left _)) ((revenue (G:=G) (L:=L)).pow (n+1)))
-- BUILD status. Covenant for some rate. inputs Tilt T later. need choose χ
omit hp
variable (hC:0<C)(hw:0 < d)
local notation "D"=> wick G L d
include hw hC
lemma staple (hS : Bolt G L P) (X:ℝ)(hX:drive n < X) : ∃ z a:ℝ, ∀ᶠ x in atTop,
    Status k n (r x) (t x) z (E x) (D x) a (H x) (P x) (ε x) C ∧
       ticket k n (r x) (D x) (t x) C z (H x) (P x) a (V x) ≤ betaF G x L ^ X ∧
       ∀ (ι: Type)[Fintype ι][DecidableEq ι] (Q:Matrix ι ι ℝ),(Fintype.card ι:ℝ)≤ P x → Q.PosDef→ (∀ y:ι→ℝ, dotProduct y (Q *ᵥ y) ≤ C*dotProduct y y) → (sweep Q).real (closedBall (0:Poll.Body ι) (D x))ᶜ≤(puff G L x n)^2 := by
    obtain ⟨Z,hZ,hZ'⟩:=Brush.compact (f:=Real.exp) (k:=k) isCompact_Icc (fun x (_:x∈ Set.Icc (-1:ℝ) 1)=> Real.contDiff_exp.contDiffAt)
    obtain ⟨B,hB,H'⟩:= LocalAtlas.treasury k (Real.exp (-1)*(1/2:ℝ)/2) (Real.exp 1+ Real.exp (-1)*(1/2:ℝ)/2) (by positivity)
    have h': Rate G L 0 D:= gen G L d; let Q:= H; have hQ:Rate G L (drive n) (fun x=> puff G L x n):= Rate.power
    have hG: Rate G L (drive n*(2:ℕ)) (fun x=> (Q x)^2):= hQ.pow 2
    have hY: ∀ᶠ x in atTop,1 ≤ D x:= by filter_upwards [ (Bolt.still (G:=G) (L:=L) (1/d)).listens zero_lt_one ] with t ht; rw [Real.rpow_one] at ht; exact ((div_le_iff₀ hw).mp ((le_abs_self _).trans ht)).trans_eq (mul_comm ..)
    have he:= revenue (G:=G) (L:=L); refine ⟨Z,B,?_⟩; filter_upwards [hY,wealth (Z:=Z) (C:=C) (s:=B) k n h h' ht hu X hX, Delay.shift_pos G L, (Work.E09.betaF_growth G L).eventually_ge_atTop 1, he.below downhill 1 zero_lt_one, ((unit_mul ((fareRate k h h').add ht) he).below downhill 1 zero_lt_one), hG.below (mul_neg_of_neg_of_pos (downhill2 n) (by norm_num)) _ (by norm_num : 0 < (1/2:ℝ)), (budged k n h h' ht hu (C:=C) (Z:=Z)).below (downhill2 n) _ (LocalAtlas.fee_sign), Lantern.walls G L hS hC hw (drive n*(2:ℝ))] with x hx hL hJ h𝕌 hf hE hv hD hA
    have hl : (ε x) ≤1:= Real.rpow_le_one_of_one_le_of_nonpos h𝕌 (by norm_num [sacred])
    refine ⟨⟨hx,hZ',H',Real.rpow_pos_of_pos hJ sacred,hl,(le_abs_self _).trans hf,(le_abs_self _).trans hE,Real.rpow_pos_of_pos hJ _, (le_abs_self _).trans hv, (le_abs_self _).trans hD⟩,(le_abs_self _).trans hL, fun ι _ _ Q hP hQ hr=>?_⟩
    rw [measureReal_compl measurableSet_closedBall,probReal_univ]; apply (hA _ _ hP hQ hr).trans_eq; rw [Real.rpow_mul hJ.le,Real.rpow_two]; rfl
end cost
section rise
variable {r t P:ℝ→ℝ}(k n:ℕ)(hp:Rate G L 0 P)(hP:Bolt G L r)(ht:Rate G L 0 t)(hd:0<d)(hC:0<C)(X:ℝ)(hX:drive n < X)
local notation "S"=> wick G L d
local notation "V"=> shadow G L
local notation "Z"=> eaves G L
include hp hP ht hC hd hX
lemma fits (hn:n+1≤k) : ∃ f:ℝ→ℝ, Rate G L 0 f∧ ∀ᶠ x in atTop,
    let u:=eaves G L x; let D:= wick G L d x; let q:= shadow G L x;
    ∀ (ι E :Type)[Fintype ι][DecidableEq ι][NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](p g:E × Poll.Body ι → ℝ)(r': E→Poll.Body ι)(M:E→Matrix ι ι ℝ)(h:Poll.Body ι→ (ℝ×E)→ℝ), Golf p g r' M k D u u (P x) → Tilt k u D q (t x) h → (Fintype.card ι:ℝ) ≤ r x → (∀ z:ι→ℝ,dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ C*dotProduct z z) →
       let F:= Lantern.grace p g r' M + h; let s:=closedBall (0:Poll.Body ι) D; let μ:=sweep (M 0)⁻¹; let π₁ := sampleLog μ s F;
       (∀ z:Poll.Body ι,F z 0=0)∧1 ≤ D∧0<q∧q≤1∧
       ∀ y:ℝ × E, ‖y‖<u → Real.exp (-1)* (1/2:ℝ) ≤ Mulberry.cut μ s F y∧ Brush k (f x) q⁻¹ π₁ y∧ Brush k (betaF G x L ^ X) u⁻¹ (π₁ - Mulberry.clean μ F n) y := by
    obtain ⟨z,u,h⟩:= staple (C:=C) (d:=d) k n hp ht hP.uses hC hd hP X hX; let y x:= receiptQ k (P x) (S x) (t x) z u
    refine ⟨y,?_,?_⟩
    · apply lumpRate k (homegrown k hp (gen G L d) ht) (Rate.const u)
    filter_upwards [h] with x hx v D R ι E _ _ _ _ _ p g ρ M f H hT ht hr
    obtain ⟨hK,hL,hD⟩:= hx; intro F s μ π; have hv:‖(0:E)‖<v:=norm_zero.trans_lt H.pos
    refine ⟨fun i=> congr_arg₂ (·+·) (show Lantern.grace p g ρ M i 0=0 from Lantern.zeroC p g ρ M i) (hT.flat _) |>.trans (add_zero 0), hK.tuition,hK.possible,hK.sane,fun y hy=>?_⟩
    obtain ⟨hp,hq,hz⟩:= bureau H hT hn hK (hD _ _ ht ((H.gram _ hv).1.inv) hr) ht hr hy; exact ⟨hp,hq,hz.climb hL le_rfl⟩
end rise
end YM.Juniper.Mulberry
