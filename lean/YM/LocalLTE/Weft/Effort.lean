import YM.LocalLTE.Weft.Loom
/-! # Uniform proposal over all unreindexed ancestry -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {χ : Chi}
local notation "B" => radiusB s
open PhysicalNext.Repeat Roost
open YM.LocalLTE FrameBox Inset PriceCompiler
open LocalLTE.Fan Field Fan.Bakers Vine Weft
variable {κ :ℝ}
open Tensor
lemma organZ {ι D:Type}[NormedAddCommGroup D][NormedSpace ℝ D][Fintype ι][Nonempty ι](u:ℝ→D→ι→ℝ)(h:∀ k:ι,Warp j n C (fun s x=> u s x k)): Warp j n C (fun s (x:D)=> likely (u s x)) :=by
   let q:ℝ:= Fintype.card ι; have he:0<q:= by unfold q; positivity
   have hp:= Warp.sumQ univ _ _ (fun k _=> h k)|>.smul q⁻¹; simp only [sum_const,card_univ,nsmul_eq_mul] at hp; rw [abs_of_pos (inv_pos.mpr he),inv_mul_cancel_left₀ he.ne'] at hp
   refine (show (fun s:ℝ=>fun (x:D)=> likely (u s x))= (fun s=> q⁻¹ • (∑ k:ι, fun x=>u s x k)) from funext (fun s=>funext fun x=>by change _ = q⁻¹ * ((∑ i:ι, fun x=> u s x i) x); rw [Finset.sum_apply]; rfl)).symm ▸ hp
lemma paddedCard (D: Option (Fin j)→Finset (Veil c f)) (h:∀ i,(D i).card≤n) (m:ℕ) : Fintype.card (Gains D m) ≤ ((m+1)^n)^(j+1):=by
    refine (le_trans (b:=∏ i:Option (Fin j),(m+1)^n) ?_ (le_of_eq (by simp)))
    unfold Gains; rw [Fintype.card_pi]
    apply prod_le_prod'; intro i _
    unfold LevelsΛ; rw [Fintype.card_fun,Fintype.card_coe,Fintype.card_fin]; exact (pow_le_pow_left' (le_of_lt (Nat.lt_succ_self m)) _).trans (pow_le_pow_right₀ (by omega : 1 ≤ m+1) (h i))
lemma mayhem (J K p:ℕ) (r:ℕ→ℕ)(χ:Chi) (Φ:ℕ→ℝ→ Config G f→ℝ) (D:H.fragrances)(q:Veil c f→ℝ) (V:ℝ)(hV:1≤V) (h: Orchestra H D J) (hz:∀ i∈⋃j:Option (Fin D.fst),(↑(docket H D j):Set (Veil c f)),0 ≤ q i)
   
   (hQ:∀ i:Option (Fin D.fst),∀ z: LevelsΛ (East.docket H D i) m, ∀ (F:Forest S.ratio)(X₀:Coat T F), X₀.x=s→X₀.width=o.K→ Warp K j ((∏ i∈ East.docket H D i,q i)*V) (fun t x=> Bakers.curlP X₀ (vest R Φ t) (East.docket H D i) X.table (postponement L s o) (Field.pin (East.docket H D i) H) x z)) : Warp (K*(J+1)) j ((stock (East.docket H D) q)* ((V^(J+1)*(1+(J+1:ℕ))^j)* (((m+1:ℕ):ℝ)^J)^(J+1))) (fun s=> maypole m H r D χ p (vest R Φ s)):=by
    let p':= D.fst; let v:ℝ:= (↑(J+1:ℕ))*1; let Y:= Option (Fin D.fst); let C (i:Y):= ∏ j∈ docket H D i, q j; let P' (w:Gains (East.docket H D) m) s x:= if built (East.docket H D) w (Fan.levy r) ≥ chip (p+1)-10*Pastel.slack then ∏ i, East.felix H D χ (vest R Φ s) i (w i) x else 0
    have hc i:0≤ C i:= prod_nonneg (fun j hj=> hz j (Set.mem_iUnion.mpr ⟨i,hj⟩)); let D':=stock (East.docket H D) q; have hD:0≤D':= prod_nonneg fun j _=> hc j
    let T':=D'*(V^(J+1)*(1+(J+1:ℕ))^j); have HJ:0 ≤ T':=by unfold T'; positivity
    letI : Nonempty (Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
    have hp z: Warp (K*(J+1)) j T' (P' z):=by
       unfold P'; split_ifs
       next hB=>
          let f(i:Option (Fin D.fst))(s:ℝ):= East.felix H D χ (vest R Φ s) i (z i)
          have hp i:Warp K j (C i * V) (f i):= by
            unfold f East.felix; refine organZ (fun s x F=> _) (fun F=> ?_); exact organZ _ (fun k=> hQ i _ _ ((prism T s χ o.K (1:Config G c) (Greenbelt.allot F)).taggedL k) rfl rfl)
          have hx:= Warp.ballads univ (fun i _=> hp i); rw [card_univ,Fintype.card_option,Fintype.card_fin,prod_mul_distrib,prod_const,card_univ,Fintype.card_option,Fintype.card_fin] at hx
          refine hx.grow (Nat.mul_le_mul_left _ (Nat.succ_le_succ h.length)) (?_)
          have hk: 1+(↑(D.fst+1:ℕ):ℝ) ≤ 1+(J+1:ℕ):= add_le_add_right (by exact_mod_cast Nat.succ_le_succ h.length) _
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ hV (Nat.succ_le_succ h.length)) (pow_le_pow_left₀ (by positivity) hk _) (by positivity) (by positivity)) hD
       exact Arp.zero'.warp.grow le_rfl HJ
    have hx:= Warp.sumQ univ _ _ (fun i _=> hp i); simp only [sum_const,card_univ,nsmul_eq_mul] at hx
    rw [show (fun s=> _)= (fun s=> ∑ w: Gains (East.docket H D) m,P' w s) from funext (fun s=> funext fun x=> by rw [Finset.sum_apply]; rfl)]; refine hx.grow le_rfl (?_)
    have hh:=paddedCard (docket H D) (fun i=>h.each i|>.received) m
    have ht: 1 ≤ (((m+1:ℕ):ℝ)^J):=one_le_pow₀ (by exact_mod_cast (show 1 ≤ m+1 by omega))
    apply (mul_le_mul_of_nonneg_right (_root_.le_trans (Nat.cast_le.mpr hh) (show ↑(((m+1)^J)^(D.fst+1:ℕ))≤ ((((m+1:ℕ):ℝ)^J)^(J+1)) from (by exact_mod_cast (pow_le_pow_right₀ (one_le_pow₀ (show 1≤ m+1 by omega)) (Nat.succ_le_succ h.length) : ((m+1)^J)^(D.fst+1) ≤ ((m+1)^J)^(J+1))))) HJ).trans; unfold T' D'; apply le_of_eq; ring
-- shell scalar to output frame. radius.Pkt graded.
-- ray Ω fold. same physical sail.
def legendF (W:ℝ)(J m i j:ℕ):= let k:= pie i+1
    ((k:ℝ)*(((W^(J+1)*(1+(J+1:ℕ))^k)* (((m+1:ℕ):ℝ)^J)^(J+1))*2^k*(1+(k:ℝ))^j))
lemma rimWheel (Z n:ℕ)(Φ:ℕ→ℝ→ Config G f→ℝ)(z:H.fragrances)(t:ℕ→ℕ)(χ:Chi)(L':Directions G c→L[ℝ] Directions G c)(hL:‖L'‖≤1)(p:ℕ)(i:ℕ)(V:ℝ)(hV:1≤V)
    (q:Veil c f→ℝ)(hz:∀ i∈⋃ j:Option (Fin z.fst), (↑(docket H z j):Set (Veil c f)), 0 ≤ q i)(ho: Orchestra H z n)
    (he:∀ i':Option (Fin z.fst),∀ u:LevelsΛ (docket H z i') k,∀ (F:Forest S.ratio)(X':Coat T F),X'.x=s→X'.width=o.K→ Warp Z (pie i+1) ((∏ j∈ docket H z i', q j)*V) (fun t x=> Bakers.curlP X' (vest R Φ t) (docket H z i') X.table (postponement L s o) (Field.pin (docket H z i') H) x u)) : Arp (Z*(n+1)+(pie i+1)) p (|Field.speedΛ H z.snd| * (stock (docket H z) q)*legendF V n k i p) (fun s=> East.flying k H t z χ (Fan.vest R Φ s) i L'):=by
    let f:=(0:Directions G c→L[ℝ]ℝ).prod L'; let Q: Disk G c:=(1,0); have hq: ‖Q‖≤1:=max_le (by simp : ‖(1:ℝ)‖≤1) (show ‖(0:Directions G c)‖ ≤ 1 from by rw [norm_zero]; linarith)
    have hf : ‖f‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound f zero_le_one (fun i=> by rw [one_mul]; exact max_le (show ‖(0:ℝ)‖≤‖i‖ from by simp) ((L'.le_opNorm i).trans (mul_le_of_le_one_left (norm_nonneg _) hL)))
    let P':= pie i+1; have hg:= (Warp.stencil Q hq hf p (mayhem H n Z i t χ Φ z q V hV ho hz he) (le_refl P'))
    refine ((hg.scales (Field.speedΛ H z.2)).climb le_rfl (le_of_eq (?_))).adjust (fun i hi=> funext fun v=>?_); · unfold legendF; ring
    let u:ℝ:=gStep (Fan.vest R Φ i).beta; have hu : u=i := by change (Real.sqrt ((i^2)⁻¹))⁻¹=i; rw [Real.sqrt_inv,Real.sqrt_sq (show 0 ≤ i from hi.1.le),inv_inv]
    change _*_=_*(LocalLTE.stem _ _ (u,L' v)); rw [hu]; apply congr_arg; apply congr_arg; unfold Q f; simp -- edit
end YM.PhysicalNext.Repeat.East
