import YM.LocalTaylorR2.Marker.Checks
import YM.LocalTaylorR2.Marker.Primula
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Little
import YM.LocalTaylorR2.License
import YM.LocalTaylorR2.Scaling
import YM.LocalTaylorR2.Grafting.Berry
/-! Adapt Steno to upsized charge. 
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
open Tail Mallow Blush
variable {v B w σ a e s δ : ℝ}
def Trailer (Q:YM.ConnectedActivityE6.Target G P)(Γ:Target.Expense Q)(L:Side)(W μ x:ℝ)(o:Target.Order G W)(j h l:ℕ)(χ:Chi)(ε U:ℝ):Prop :=
    let e:=Γ.one/2
    ∃ A₀ a' C d v t r B k D x' b y K θ ρ w l' n, RoofMark G Q L W μ x ε e w D x' B r y K θ ρ (b+b) j n h l U ∧ b+b ≤ Q.goal L x ∧
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Stamp T → ∀ R C' (H:Cash W x μ L Q o C' T R),
      ∃ N:Captain H j C d v t A₀ a' r B k (n+j) χ, LocalBookingsR2 (l+1:ℝ) b N.conduit ∧ StoresR2 H j v d A₀ D l' x' n χ ∧ Herd H N.conduit A₀ B (n+j) ∧ Tinted G x K d o.a L χ j
-- issued before L. charges array of windows.Rep selected then numeric consumed without reconverging lower budgets.
lemma missive (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(Γ:Target.Expense Q): ∃ n:ℕ,∀ L:Side,n≤L.val→ foam Q L ∧ ∀ W μ o j h l χ ε U, (0:ℝ)<ε→0<W→0<μ→
      (∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j) → ∀ᶠ x in atTop, Trailer Q Γ L W μ x o j h l χ ε U :=by
   obtain ⟨k,H⟩:= scripts P Q; obtain ⟨p,H'⟩:=Daisy.early Q
   refine ⟨max k p,fun L hx=> ?_⟩; have H₀:=H' L ((le_max_right ..).trans hx)
   refine ⟨H₀,fun W μ o j h l χ ε U he hw hμ hoff=>?_⟩
   obtain ⟨D,hd,hL,hX⟩:=hoff; obtain ⟨θ,hθ,hΘ⟩:= Series.allowance l j
   obtain ⟨e,hp,hh,hl⟩:= Tail.plan l (ε/2) (half_pos he)
   obtain ⟨s,hs,hE⟩:= exists_between (show -(1/2:ℝ)< min Q.rate (-e) from lt_min Q.start (by linarith)); obtain ⟨hS,hE⟩:= lt_min_iff.mp hE
   obtain ⟨a,a',C,d,v,w,r,B,k,D',x',b,K,l',n,hB,hr,hb,hD,hA,hK,hM⟩:= H L ((le_max_left ..).trans hx) s (l+1) hs hS (by positivity) D hd j χ W hw μ hμ o
   obtain ⟨t,ht,h'⟩:= exists_between (show max (e+s) Q.rate<0 from max_lt (by linarith) Q.stop)
   obtain ⟨u,hu,H₁⟩ := exists_between (show t < min 0 (t+ε/4) from lt_min h' (by linarith)); obtain ⟨hx',hh'⟩:= lt_min_iff.mp H₁
   let Y:= fun x=> betaF G x L; let g x:=Y x^(t-Q.rate); let ρ x:=Y x^e; let q x:=Y x^u; let δ:=Γ.one/2
   let B₂s x:= b x + b x; have hBW:=hb.add hb; obtain ⟨hm,hx⟩:= rootGauge (η:=θ) D' B B₂s x' r K g ρ l n j Rate.power hBW (show Rate G L (t-Q.rate) g from Rate.power) hμ ((le_max_left ..).trans ht.le) ((le_max_right ..).trans ht.le) (a:=t) (by linarith) hD hB hA hr hK
   have hc := Tail.incline (θ:=θ) ρ l (show Rate G L e ρ from Rate.power) hBW hμ ((le_max_left ..).trans ht.le) ((le_max_right ..).trans ht.le)
   have hg: Rate G L (-t) (fun x=> (Q.goal L x*g x)⁻¹):= by
      apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; rw [show Q.goal L x*g x= betaF G x L^t from (Real.rpow_add hx Q.rate (t-Q.rate)).symm.trans (by rw [add_sub_cancel]), Real.rpow_neg hx.le]
   have hy(i:ℕ)(hp:i ≤l+1):= ((hg.mul (Tail.height (L:=L) G i j h 1 e δ u)).mul_left U) (requested i ε) (by have h:= hl i hp; unfold requested at *; linarith)
   have hy':= eventually_all.mpr (fun i:Fin (l+2)=> hy i (Nat.le_of_lt_succ i.isLt))
   have hr': Rate G L (-Q.rate) (fun x=>(Q.goal L x)⁻¹):= by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; rw [Real.rpow_neg hx.le]; rfl
   have hF:= (hr'.mul_left U).mul (efferv (G:=G) (L:=L) hμ (Q.rate-l-2)) (- ( (l:ℝ)+1)) (by linarith)
   have hN:= AbsoluteSums.Fees.horizons G L 0 (ε:=Q.ε) Q.usable (le_refl 0) (show 2*Q.ε < P.top.supportExponent from by linarith [Q.grants.1,Q.usable])
   filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,(Tail.meters _ hm Q.δ).below h' (1/2) (by norm_num), (Tail.meters _ hc Q.δ).below h' (1/2) (by norm_num), (Tail.meters (G:=G) q (show Rate G L u q from Rate.power) δ).below hx' (1/2) (by norm_num), ((Rate.power (a:=e)).mul hBW).below (by linarith) 1 zero_lt_one,
    Tail.marked (L:=L) Q hμ (l+1:ℝ), hx u hu,hy',hF,hM,hBW Q.rate hS,hN] with x hh0 he0 he1 he2 ht1 hp0 hx h' hy hz hF0 hN
   have hρ : 1≤ ρ x:= Real.one_le_rpow hh0 hp.le
   have hg0 : 1≤g x:= Real.one_le_rpow hh0 (sub_nonneg.mpr ((le_max_right ..).trans ht.le))
   have hg : ρ x ^ (l+1) ≤ betaF G x L^(l+1:ℝ):= by
     rw [show ρ x ^(l+1)=_ from (Real.rpow_mul_natCast (zero_le_one.trans hh0) e (l+1)).symm]; apply Real.rpow_le_rpow_of_exponent_le hh0
     push_cast; exact mul_le_of_le_one_left (by positivity) (by linarith)
   refine ⟨a,a',C,d x,v x,w x,r x,B x,k x,D' x,x' x,b x,g x,K x,θ,ρ x,q x,l',n,?_,(le_abs_self _).trans hF0,fun _ _ S T hT R C H=>?_⟩
   · refine ⟨hh0,hg0,hθ,hρ,Real.rpow_pos_of_pos (zero_lt_one.trans_le hh0) _, H₀,hN.2.1,hΘ,(le_abs_self _).trans ht1,hg,hp0,(le_abs_self _).trans he1,(le_abs_self _).trans he0,(le_abs_self _).trans hx,(le_abs_self _).trans he2,fun i hi=>(le_abs_self _).trans (h' (⟨i,Nat.lt_succ_of_le hi⟩:Fin (l+2))),?_⟩
     rw [←mul_assoc U]; exact (le_abs_self _).trans hy
   exact hz _ _ S T ((H.laws.data.funds).patch hL hX) hT R C H
section market
variable {q₀:Reel.Scroll G f}{H':Cash W x μ L Q o C T (Reel.bend R q₀)}
variable {b b₀:ℝ} (U':Utopia H' j v₀ d r C' χ) (h:1≤betaF G x L)(hζ:0≤ζ)(hA: LocalBookingsR2 ζ b Ξ)(hv: LocalBookingsR2 ζ a U')(he:b+a≤ Q.goal L x)
local notation "ξ₀"=> Grafting.upSize Ξ U' h hζ hA hv he
include h hζ hA hv he
lemma enlarged1 (hm:0≤b₀) (hX: Herd H Ξ A b₀ k): Herd H (ξ₀) A b₀ k:= by
   refine ⟨Grafting.flares Ξ U' h hζ hA hv he hX.unmarked hm,?_⟩
   intro M E _ _ _ F' X' Y z p hζ' hM ht hK hr hu hN htM hf hy m
   obtain ⟨f,hp,hY,hF⟩:= hX.nil M E F' X' Y z p hζ' hM ht hK hr hu hN htM hf hy
   refine ⟨f,hp,hY.trans (mul_le_mul_of_nonneg_left ?_ hm),hF⟩
   rw [photo M H Ξ k hN htM,photo M H (ξ₀) k hN htM]
   apply mul_le_mul_of_nonneg_right _ (pow_nonneg (add_nonneg zero_le_one (H.positive_volume _)) _)
   exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=> Ξ.tagged i) (fun i _=> Grafting.stool Ξ U' _ _ _)) M.profit) (pow_nonneg Ξ.awake _)
end market
end YM.LocalTaylorR2.Marker
