import YM.FormalBulk08.Taft.Revolve
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Taft
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Avenue Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{I:Type}{W:Lab G K I}{ρ:ChartRatio G}{E e r d D R n:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
variable {P:Page I}{C:Pin P} {Q:Deck C→ℝ}{f L : Turn C→ℝ}{θ:ℝ}
open Dove
lemma wide_factor (x:Turn C): (((P.mesh x.a).block x.b).val:ℝ)⁻¹ = Turn.rad 1 x:= by unfold Turn.rad ringR sowing; rw [Schedule.scale_succ,add_sub_cancel_left,neg_mul,one_mul,Real.exp_neg,Real.exp_log]; positivity
lemma vanishing_coin (h:Years P)(hp:θ<1)(hs:Soft ((sage C).reach (peak C)) (fun x=>Q (peak C x)))(hk:Faint (Dove.tide C) (Dove.bump θ) L)(hv:∀ i, 0≤ f i ∧ f i ≤ Turn.rad 1 i)(hh:∀ i:Turn C,Q i.bed=f i*Q i.ups+L i) : Faint (sage C) (Degree θ) Q:= by
   let τ:=sage C; let k x:= wideA (x:Turn C).toLeaf
   obtain ⟨B,b,H,V⟩:=hk; have hB:= b.times (h.blocks.reach (fun i:Turn C=>i.toLeaf)); let A x v:= |Q (x:Deck C)|≤v*Degree θ x; have he : ∀ x:I,A (peak C x) |Q (peak C x)|:= fun i=> by
       unfold A Degree ratioR; change |Q (peak C i)|≤|Q _| *(_ / (P.mesh i).a (C.N i))^θ;rw [show (P.mesh (peak C i).a).a _=(P.mesh i).a (C.N i) from rfl,div_self (Schedule.a_pos ..).ne',Real.one_rpow,mul_one]
   apply upward (f:=A) h (sub_pos.mpr hp) (fun i a hp b h=> hp.trans (mul_le_mul_of_nonneg_right h (ratioR_pos ..).le)) hs.radius he hB
   intro x a ha hv'
   let u:=Turn.rad (1-θ) x; have H':0 <Degree θ x.ups:= ratioR_pos ..; have hl:0< Degree θ x.bed:=ratioR_pos ..; obtain ⟨v,p,hy,q⟩:= adjust_rate (P.mesh x.a) hp.le x.b (C.N x.a); unfold A; rw [hh, add_mul]; refine (abs_add_le ..).trans (add_le_add ?_ ?_)
   · rw [abs_mul,abs_of_nonneg (hv _).1]; refine (mul_le_mul (hv _).2 ha (abs_nonneg _) (le_trans (hv x).1 (hv x).2)).trans_eq ?_; rw [mul_left_comm, show Turn.rad 1 x * Degree θ x.ups=_ from adjusted .., mul_left_comm, mul_assoc];rfl
   change _≤B x * (k x:ℝ)*Degree θ x.bed; refine (V x).trans ?_; change B x*Degree θ x.ups≤ _;rw [show Degree θ x.ups=v * Degree θ x.bed from q,←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy (H x)) hl.le
lemma balance_coin (h:Years P)(hs:Soft ((sage C).reach (peak C)) (fun x=>Q (peak C x)))(hk:Soft (Dove.tide C) L)(hv:∀ i,0≤ f i∧ f i≤Turn.rad 1 i)(hh:∀ i:Turn C,Q i.bed=f i * Q i.ups + L i) : Soft (sage C) Q:= by
    obtain ⟨A,p,t,ht⟩:= upward (f:=fun x v=>|Q x| ≤ v) h zero_lt_one (fun _ _ h _ v=> h.trans v) hs.radius (fun _=>le_rfl) hk.radius (fun i w h p=>by
       rw [hh]; refine (abs_add_le ..).trans (add_le_add_left (?_) _);rw [abs_mul,abs_of_nonneg (hv i).1]; exact mul_le_mul (hv i).2 h (abs_nonneg _) ((hv i).1.trans (hv i).2)); exact p.below (fun _=> (ht _).trans (le_abs_self _))
lemma nonroad {X:Type}{τ: Time X}{δ:X→ℝ}{Z M:X→Tilework F}{b:X→Letter F→ℝ}(h:∀ i,Colfax (slots F) (Pose.weight F) (Z i) (b i))(p:∀ i,Colfax (slots F) (Pose.weight F) (M i) (b i))(hp:∀ i j:Letter F, Pact τ δ (fun x=>coeff 0 ((Z x)⁻¹ i j)) (fun x=>coeff 0 ((M x)⁻¹ i j)))(i j:Letter F): Pact τ δ (fun x=>(noncontract F (Z x))⁻¹ i j) (fun x=> (noncontract F (M x))⁻¹ i j) := by
   simp_rw [nc_revert (h _),nc_revert (p _),noncontract];by_cases he:Pose.slots F i=Pose.slots F j; simp_rw [if_pos he];exact hp i j; all_goals simp_rw [if_neg he]; exact Pact.coin .. -- tactic
end YM.FormalBulk08.Taft
