import YM.RGLocalTaylor.Retain.Till
import YM.RGLocalTaylor.Retain.Mill
/-!
# Inherited Sales purchase BEFORE forecasts
Costly actual geometry (WG & calendar ξ), permits *any* `Profile` and common
stage roles. No FK hypotheses on perturb kernels from a forecast oracle.
Important to pay when MAYA expansion uses at-least-two perturbative handles and
at least one E input; also for μ-mark service.
Proofs adapted from Yard, Rate & Weights in CONNECTED_ACTIVITY_JETS_E6.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Retain
open Mayer goodK Post
namespace Fort

open PhysicalNext PhysicalNext.Repeat
variable {M i :ℕ} {f₁ f₂ : glyph G f} {X : Cash W s μ L Q o C T (impulse R f₂ a)}
variable {e vJ uJ K θ α γ β Z r' d' ρ:ℝ}{w w':ℕ→ℝ}
   {Ξ : Utopia H j v d r C' χ}
   {N : Captain H j C' d v Y A b r B q n χ}

open Push.AbsoluteSums
set_option quotPrecheck false
local notation "Ξ'" => N.conduit
local notation "κ" => Opacity.key S

-- exponents at any booking history. 9/16 from E per-Sales, usable before poly overheads.
abbrev vest (G:Gauge)(L:Side)(s:ℝ) := betaF G s L ^ (9/16:ℝ)
abbrev dust (G:Gauge)(L:Side)(s:ℝ) := betaF G s L ^ (-(17/16:ℝ))
local notation "U" => vest G L s
local notation "D₀" => dust G L s
local notation "b'" => radiusB s
local notation "κ'" => garment S
local notation "e'" => Q.relative

lemma combination {A:Type} {f g:A→ℝ} {X:A→Support c} {e:A→ℕ} (h:Sales l d a X f e γ)(hF:Sales l d a X g e β) : Sales l d a X (f+g) e (γ+β):= by
   refine ⟨fun i=> add_nonneg (h.nonneg i) (hF.nonneg i),fun i=>?_⟩
   convert budget_plus (h.hit i) (hF.hit i) using 2 with i; dsimp only [Reserves.tariff,Pi.add_apply]; split_ifs <;> ring

abbrev outlets (_H :Cash W s μ L Q o C T R)(w:ℕ→ℝ)(C:ℝ): Prop:= Sales (radiusB s) Q.relative Q.ε (regularFoot S.ratio Q.halo (radiusB s) R) w (Raw.regularExtra R) C
-- unused H natural type mark _

abbrev Pmark (_H :Cash W s μ L Q o C T R) : Head S→ℝ:=fun i=> Q.mark L μ s*Mixed.shares S i
abbrev Pextra (_H :Cash W s μ L Q o C T R) (C':ℝ) : Head S→ℝ:= Mixed.lengths S (Q.costs L μ R.beta s C') (ConnectedActivityE6.lengths T R)
abbrev Pay (H : Cash W s μ L Q o C T R) (v:ℝ)(g:Head S→ℝ) := Reserves.tariff g (Pextra H v) (Pmark H) Q.ε

lemma shops (A b:ℝ) (h:outlets H w b)(he:0≤A) : Ac.Hit H.supportP (radiusB s) (Pay H C' (κ' w A)) Q.relative (A*b):=by
   let f:= κ' w A; let F:ℕ↪Head S:=⟨κ,lifts _⟩; let t:=fun i:ℕ=> A*w i; have hv i:f (F i)=t i:= (lifts _).extend_apply _ _ i
   have hp':Sales b' Q.relative Q.ε (regularFoot S.ratio Q.halo b' R) t (Raw.regularExtra R) (A*b):= h.shift he (fun i=>mul_nonneg he (h.nonneg i)) (fun i=> le_rfl)
   intro x; refine Beam.wallet F ?_ fun v hv=>?_ 
   · apply budget_mono (hp'.hit x); intro i; split; next h'=> exact mul_nonneg (mul_nonneg (show 0 ≤ f (F i) from (hv i).symm ▸ hp'.nonneg i) (Real.exp_pos _).le) (Real.exp_pos _).le
     rfl
     intro i; split
     next h'=>
        rw [if_pos (show x∈ Raw.regularFoot S.ratio Q.halo b' R i from h')]
        unfold Pay Reserves.tariff; rw [show κ' w A (F i)=_ from hv i,show Pmark H (F i)=0 from ?_]; exact le_rfl
        unfold Pmark; rw [show Mixed.shares S (F i)=0 from rfl,Nat.cast_zero,mul_zero]
     exact (hp'.hit x).1 i
   split; next h=> unfold Pay Reserves.tariff garment; rw [extend_apply' _ _ _ (show _ ∉ Set.range (Opacity.key S) from hv)]; exact mul_eq_zero.mpr (Or.inl (mul_eq_zero.mpr (Or.inl rfl)))
   rfl

structure Upkeep (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P)(L:Side)(x:ℝ) : Prop where
   scale : 1≤ vest G L x
   sizes : 0 < dust G L x
   tall : dust G L x ≤ 1/8
   pays : vest G L x*(dust G L x+dust G L x) ≤ Q.goal L x
   enough : (dust G L x+dust G L x)*Mayer.arcRadius G L x ≤ 1
   appointments (W μ:ℝ) (o:Target.Order G W) {c f:Side}{S:StepData c f}{T:Tube G S}{R:Rep G f} (C:ℝ)(H:Cash W x μ L Q o C T R):
     ∃ w:ℕ→ℝ, shelved H w ∧ outlets H w (dust G L x)

open YM.Merge Palette Laminate
lemma rents (Q : YM.ConnectedActivityE6.Target G P): ∃ n:ℕ,∀ L:Side,n≤L.val → ∀ᶠ x in atTop, Upkeep P Q L x:= by
   have hp:0≤Q.relative:= by unfold Target.relative; linarith [Q.usable,Q.pos,Q.bound]
   obtain ⟨n,h⟩:= Raw.core_bills P Q.halo Q.usable hp Q.grants.1
   refine ⟨n,fun L hz=>?_⟩
   let v:= vest G L; let t := dust G L; have hv : Rate G L (9/16:ℝ) v:= Rate.power; have ht : Rate G L (-(17/16:ℝ)) t := Rate.power
   have hy: Rate G L Mayer.height (Mayer.arcRadius G L):=Rate.power
   filter_upwards [h L hz _ 0 (by norm_num : -(11/10:ℝ)< -(17/16:ℝ)), (Work.E09.betaF_growth G L).eventually_ge_atTop 1, (ht.below (by norm_num) (1/8) (by norm_num)), hv.mul (ht.add ht) Q.rate (by linarith [Q.start]), ((ht.add ht).mul hy).below (by norm_num [Mayer.height]) 1 zero_lt_one] with x hx he hK hL hL'
   have hy:0< betaF G x L:= zero_lt_one.trans_le he
   have hT := (le_abs_self _).trans hK
   refine ⟨(Real.one_le_rpow he (by norm_num)),Real.rpow_pos_of_pos hy _,hT, le_trans (le_abs_self _) (hL: _ ≤ Q.goal L x), le_trans (le_abs_self _) hL', fun W μ o _ _ S T R C H=>?_⟩ -- infer hL?
   obtain ⟨u,w,h,hb,_,_⟩:= hx S T R H.laws.data.funds.length_eq H.laws.intake
   exact ⟨u,⟨fun i=> (hb.atom hp Q.usable.le i (Raw.space_ne S T Q.halo _ R (Sum.inl i))).trans hT,h⟩,hb⟩

abbrev γprice (Q : YM.ConnectedActivityE6.Target G P)(L:Side)(s μ:ℝ) := Laminate.width Q μ L s + Q.goal L s
local notation "Y'" => γprice Q L s μ
local notation "T₀" => Trees.degreePrice b' Y' Q.δ

open Trees
variable (hU:Upkeep P Q L s)
include hU
lemma skyline (h₀:a≤1)(ha:0<a)(X:Cash W s μ L Q o C T (impulse R f₂ a)) : ∃ w w':ℕ→ℝ, dual H f₂ a w w' ∧ outlets H w D₀ ∧ outlets H w' D₀ ∧ ∀ i,(w i+w' i)*Mayer.arcRadius G L s ≤ 1:=by
   obtain ⟨w,h,hF⟩:= hU.appointments W μ o C H; obtain ⟨w',hX',ht'⟩:= hU.appointments W μ o C X; have he : outlets H w' D₀:= ht'
   have hx:0 < Mayer.arcRadius G L s := Real.rpow_pos_of_pos (by rw [← H.laws.data.funds.length_eq]; exact zero_lt_one.trans H.laws.intake.height) _
   refine ⟨w,w',⟨h,⟨X,hX'⟩,ha,h₀⟩,hF,he,fun i=>?_⟩; have hv : 0≤Q.relative:=by unfold Target.relative; linarith [Q.pos,Q.usable,Q.bound]
   exact (mul_le_mul_of_nonneg_right ((combination hF he).atom hv Q.usable.le i (Raw.space_ne S T Q.halo _ R (Sum.inl i))) hx.le).trans hU.enough

variable {ι:Type} [Fintype ι] (M':ι→Lotus.Leaf R) (rA:ι→ℝ) (hP: Plot M' H rA)
variable (Ξ:Utopia H j v d r C' χ) (hw:outlets H w (dust G L s+dust G L s)) (ht:Trees.degreePrice (radiusB s) (γprice Q L s μ) Q.δ ≤ 1/2)
    (hz:degreePrice (radiusB s) (Laminate.width Q μ L s) Q.δ ≤1/2)
abbrev readyBook (H: Cash W s μ L Q o C T R)(w:Head S→ℝ)(C':ℝ)(q:ℝ):Prop:= Ready H.supportP (radiusB s) (Pay H C' w) (Q.exp+2*Q.ε) q Q.δ (1/2)
include hw ht
-- Ready positions for both boosted OR actual weight
lemma nice {w':Head S→ℝ} {a:ℝ}(hF : Ac.Hit H.supportP (radiusB s) (Pay H C' w') Q.relative a)
   (ha : a ≤ Laminate.width Q μ L s) (hc : 0 ≤ a) (hb : ∀ i,0≤Pay H C' w' i): readyBook H (w' + κ' w U) C' (γprice Q L s μ):= by
   have hp(i): 0≤garment S w U i:= by
     unfold garment; by_cases hz:i∈Set.range κ
     · obtain ⟨i,rfl⟩:=hz; rw [(lifts S).extend_apply _ _ i]; exact mul_nonneg (zero_le_one.trans hU.scale) (hw.nonneg _)
     rw [extend_apply' _ _ _ hz]; exact le_rfl
   have he:0<Y':=add_pos_of_nonneg_of_pos (hc.trans ha) (Daisy.arable H)
   refine ⟨he,Q.pos,ht,by norm_num,fun i => ?_,fun x=> ?_⟩
   · unfold Pay Reserves.tariff; rw [Pi.add_apply,add_mul]; exact add_nonneg (hb _) (mul_nonneg (hp i) (Real.exp_pos _).le)
   refine budget_loosen ?_ (add_le_add ha hU.pays)
   convert! budget_plus (hF x) (shops U (D₀+D₀) hw (zero_le_one.trans hU.scale) (C':=C') x) using 1; ext i; dsimp only [Pay,Reserves.tariff,Target.relative,Pi.add_apply]; split_ifs <;> ring

abbrev crestP (rA:ι→ℝ)(v:Head S→ℝ)(i:Head S):= v i + Tickets.extra (Palette.sign M' S) (Palette.wages M' rA) i
local notation "w_" => Fiber Ξ w U

lemma funding : readyBook H w_ C' (γprice Q L s μ):= by
   let f:= (Q.costs L μ R.beta s C'); let y:=f.rootHit
   have hr : Ready H.supportP (radiusB s) (Pay H C' Ξ.fare) (Q.exp+2*Q.ε) y Q.δ (1/2):= Mixed.ready_vertices S Q.halo (radiusB s) f H.birth Ξ.flair (ConnectedActivityE6.lengths T R) (steamP S f) Ξ.lives Ξ.accrues
   have hd:y≤Laminate.width Q μ L s:= le_add_of_nonneg_right (add_nonneg (Daisy.arable H).le (mul_nonneg (Daisy.arable H).le (Real.exp_pos _).le))
   exact nice hU hw ht (C':=C') hr.2.2.2.2.2 hd hr.1.le hr.2.2.2.2.1 -- order?
include hP hz
lemma payroll : readyBook H (crestP M' rA w_) C' (γprice Q L s μ):= by
   have hr:=Laminate.rich M' rA Ξ hP hz
   rw [show crestP M' rA w_= projectedWeight M' rA Ξ + κ' w U from ?_]; exact nice hU hw ht hr.2.2.2.2.2 le_rfl hr.1.le hr.2.2.2.2.1
   ext x; unfold crestP projectedWeight Fiber;dsimp only [Pi.add_apply]; ring
end Fort
end Retain
end YM.RGLocalTaylor
