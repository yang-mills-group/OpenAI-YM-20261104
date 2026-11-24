import YM.AllOrder.Ink.Slab
import YM.AllOrder.Horizon.Dust
/-!
# Purchases at arbitrary gauges. Additional selection indices fit used after horizon bookings. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Trio Lapis Bid Planned.JetPort
open Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open AbsoluteSums Fare Shellac Work.G05
open Ink Ink.Money Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {V : Type*}
def Claim (G:Gauge) (L:Side)(A : ℝ→V→Prop)(a:ℝ)(f:ℝ→V→ℝ) : Prop:= ∃ F:ℝ→ℝ, Rate G L a F ∧ ∀ᶠ t:ℝ in atTop, ∀ y,A t y → |f t y|≤ F t
namespace Claim
variable {G:Gauge}{L:Side}{A:ℝ→V→Prop}{a b:ℝ}{f g:ℝ→V→ℝ}
local notation "𝒢"=>Claim G L A
lemma absolute {f:ℝ→ℝ}(h:Rate G L a f): Rate G L a (fun x=> |f x|):= h.compare (Eventually.of_forall (fun x=> (abs_abs _).le))
lemma opal {F : ℝ→ℝ}(h:Rate G L a F)(he:∀ᶠ t:ℝ in atTop, ∀ y,A t y→|f t y|≤|F t|):𝒢 a f:=⟨fun i=>|F i|, absolute h,he⟩
lemma hires {f:ℝ→ℝ}(h:Rate G L a f): 𝒢 a (fun x _=> f x):= opal h (Eventually.of_forall (fun _ _ _=>le_rfl))
lemma eve_path (f:ℝ): 𝒢 0 (fun _ _=>f):= hires (Rate.const _)
lemma zeroC (a:ℝ): 𝒢 a (fun _ (_:V)=>0):= opal Rate.power (Eventually.of_forall (fun _ _ _=> by simp only [abs_zero]; exact abs_nonneg _))
lemma bill (h:𝒢 a f)(he:a<b): ∀ᶠ x:ℝ in atTop, ∀ u, A x u→|f x u|≤ betaF G x L ^ b:= by obtain ⟨f,h,h'⟩:=h; filter_upwards [h',h b he] with i hi he; exact fun u hU=> (hi u hU).trans ((le_abs_self _).trans he)
lemma weaken (h:𝒢 a f)(he:a ≤ b): 𝒢 b f:= by obtain ⟨f,h,h'⟩:=h; exact ⟨f,h.weaken he,h'⟩
lemma congr (h:𝒢 a f)(he:∀ᶠ x in atTop,∀u,A x u→ |g x u| ≤ |f x u|):𝒢 a g:= by obtain ⟨f,h,h'⟩:=h; refine ⟨f,h,?_⟩; filter_upwards [h',he] with x hx ht; exact fun u he=>(ht u he).trans (hx u he)
lemma square (h:𝒢 a f): 𝒢 a (fun x u=>|f x u|):= h.congr (Eventually.of_forall fun x _ h=> (abs_abs _).le)
lemma mul (h:𝒢 a f)(he:𝒢 b g): 𝒢 (a+b) (fun x u=> f x u*g x u):=by
 obtain ⟨t,h,H⟩:=h; obtain ⟨s,he,K⟩:=he; refine ⟨fun i=>t i*s i,h.mul he,?_⟩; filter_upwards [H,K] with x hx ho u ht; rw [abs_mul]; exact mul_le_mul (hx u ht) (ho u ht) (abs_nonneg _) ((abs_nonneg _).trans (hx u ht))
lemma add (h:𝒢 a f)(he:𝒢 a g): 𝒢 a (fun x u=> f x u+g x u):= by
 obtain ⟨t,h,H⟩:=h; obtain ⟨s,he,K⟩:=he; refine ⟨fun i=> t i +s i,h.add he,?_⟩; filter_upwards [H,K] with x hx ho u ht; exact (abs_add_le ..).trans (add_le_add (hx u ht) (ho u ht))
lemma l_scale (h:𝒢 a f)(c:ℝ): 𝒢 a (fun x u=>c*f x u):= (eve_path c|>.mul h).weaken (zero_add _).le
lemma r_scale (h:𝒢 a f)(c:ℝ): 𝒢 a (fun x u=> f x u*c):= (h.mul (eve_path _)).weaken (add_zero _).le
lemma power (h:𝒢 a f)(k:ℕ): 𝒢 (a*k) (fun x u=> f x u^k):= by
 obtain ⟨F,h,h'⟩:=h; refine ⟨fun i=> F i^k,h.pow k,?_⟩; filter_upwards [h'] with x hx u ht; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hx u ht) _
lemma sprocket {ι:Type*} (s:Finset ι) {f: ι→ℝ→V→ℝ}(h:∀ i∈s,𝒢 a (f i)): 𝒢 a (fun x y=>∑ i∈s,f i x y):= by induction s using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; exact zeroC a | insert i j hi hj=> simp_rw [Finset.sum_insert hi]; exact (h i (mem_insert_self ..)).add (hj (fun k ht=>h k (mem_insert_of_mem ht)))
end Claim
section region
variable {G:Gauge}{V:Type}{L:Side}{f s: ℕ}{γ:ℝ}
abbrev Area (V:Type) := V×Side×ℝ
-- proof sufficient geometry speeds. schedules can demand more. keep `n=B*` only for mirrors. D purchased above `Quilt` & Ledger.
structure region (G:Gauge)(L:Side)(b:ℕ)(Λ:V→ℝ)(x:ℝ)(z:Area V) : Prop where
 grant : |Λ z.1| ≤ ConnectedActivityE6.loopBill G L x
 size : z.2.1.val≤ Trio.most b x
 front : Stores.till x≤ z.2.1.val
 flit : betaF G x L /2≤ z.2.2 ∧ z.2.2≤ 2*betaF G x L
variable (U:V→ℝ) {u v:ℝ} (p:ℕ) (L G)
local notation "ℍ" => Claim G L (region G L p U)
lemma in_area : ℍ 0 (fun _ i=> U i.1):= ⟨_,loopBill_rate G L, Eventually.of_forall fun _ _ h=> h.grant⟩
lemma Grade.area {f:V→ℝ}(hf:Grade U f): ℍ 0 (fun _ i=> f i.1):= by
 obtain ⟨a,k,hk,h⟩:= hf; have ht(t:ℝ)(z:Area V)(hh:region G L p U t z): |f z.1|≤ |a*(1+|U z.1|)^k|:= by have hv:=h z.1; rw [abs_of_nonneg hv.1]; exact hv.2.trans (le_abs_self _)
 refine ((Claim.l_scale ((Claim.add (Claim.eve_path 1) (in_area G L U p|>.square)).power _) a).congr (Eventually.of_forall ht)).weaken ?_; simp
lemma val_area : ℍ 0 (fun _ z=> (z.2.1.val:ℝ)):= ⟨_,(Trio.rows G L p|>.2.2.2).uses, Eventually.of_forall fun x z h=> by simp only [Nat.abs_cast]; exact_mod_cast h.size⟩
lemma Pay.area {f:V→Side→ℝ}(hf:Pay U f): ℍ 0 (fun _ z=> f z.1 z.2.1):= by
 obtain ⟨f',hh,k,h⟩:=hf; refine (((Grade.area G L U p hh).mul ((val_area G L U p).power k)).congr ?_).weaken (by simp); apply Eventually.of_forall; intro t z hZ; have h':= h z.1 z.2.1; rw [abs_of_nonneg h'.1]; exact h'.2.trans (le_abs_self _)
lemma dearth_area (b:ℝ)(h:0<b)(a:ℝ): ℍ a (fun _ z=> dearth b z.2.1):= by
 refine ⟨fun x=>Real.exp (-b*Stores.till x),Rate.cutoff h,Eventually.of_forall (fun x z hz=>?_)⟩; change |Real.exp (-b*(z.2.1.val:ℝ))| ≤ Real.exp _; rw [abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (Nat.cast_le.mpr hz.front) (by linarith)
lemma dearth_rate (b:ℝ)(h:0<b)(a:ℝ): Rate G L a (fun x=> Real.exp (-b*radiusB x)):= by
 refine (Rate.cutoff (G:=G) (L:=L) (a:=a) h).compare (Eventually.of_forall fun x=>?_); rw [abs_of_nonneg (Real.exp_nonneg _),abs_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_le_exp.mpr; exact mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (Nat.div_le_self ..)) (by linarith)
set_option quotPrecheck false
local notation "β"=> (fun (z:Area V)=>z.2.2)
lemma hats : ℍ 1 (fun _ z=> β z):= by
 refine ⟨_, Rate.hat.mul_left 2, ?_⟩; filter_upwards [Delay.shift_pos G L] with t ht z h; rw [abs_of_pos ((half_pos ht).trans_le h.flit.1)]; exact h.flit.2
lemma beta_area : ℍ (-(1/2:ℝ)) (fun _ z=>gStep (β z)) := by
 refine ⟨_,Sienna.glim G L,?_⟩; filter_upwards [Delay.shift_pos G L] with x hx z hz; rw [abs_of_pos (Fare.gS _ ((half_pos hx).trans_le hz.flit.1)).1]; exact (lamp G L hx _ hz.flit.1).2
lemma reverse_area : ℍ (1/2:ℝ) (fun _ z=>(gStep (β z))⁻¹):= by
 refine ⟨_,burst_rate G L,?_⟩; filter_upwards [Delay.shift_pos G L] with x hx z hz; rw [abs_of_pos (inv_pos.mpr (Fare.gS _ ((half_pos hx).trans_le hz.flit.1)).1)]; exact burst_h hz.flit.2
end region
end YM.AllOrder.Plateau
