import YM.Qlocal.LightHouse
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
variable {ι:Type*}{S':Catch.Clock ι}{P:Patch}{T:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J T (k+3+3)}
open Aux.Name Presented Poll
local notation "I"=>Aux.Name G P T u κ v (k+3) F
variable (Q : Aux.Name G P T u κ v (k+3) F)(R: reed G Q.f) (b:ℝ)
set_option quotPrecheck false
local notation "H★"=> changes Q.Fs Q.shape R b (Aux.scope κ)
local notation "w"=>Q.Θ
local notation "Zed"=>Q.Fs.Slice G
local notation "V"=> Desk.night (G:=G)
local notation "X"=>Q.X
local notation "N"=> Poll.Body Q.Vx
variable (O:ChartRatio G)(hO:LocalRatio O) (hR:Flute R q) {s:Age→ℝ} (h:Q.Civil s) {x0 y:Q.X} (D C:ℝ) (hQ: Q.goods O D C x0)(hx: ‖y‖ < eaves G P.L Q.whenP)(he: ‖y - x0‖≤ furl G P.L Q.whenP)
namespace Aurum
variable (W':ι → Aux.Name G P T u κ v (k+3) F) (V':∀ i, reed G (W' i).f) (H': Horn.Lane W' V' S' (k+3) q) (hW: Aux.Name.Proper W' S')
local notation "S₀"=> S'.Meter
local notation "V₀"=> changes
variable (a:ℝ)
variable {p:ι→ℝ}{x y:∀ i,(W' i).X}(ht : ∀ᶠ i in S'.rail, (W' i).goods O D (p i) (y i))(hv:S'.Meter p 0)(hp:(S').Meter (fun i=> ‖x i‖) (-(1/2))) (hy:∀ᶠ i in S'.rail,‖x i-y i‖ ≤ furl G P.L ((W' i).whenP))(hD:0<D)
local notation "U"=>fun i:ι=> (W' i).Θ
variable {l m N' n':ℕ}
local notation "s[i]"=> False
local notation "K"=> fun i:ι=> model (W' i) (V' i) O hO (H'.tells i)

local notation "A"=>fun i:ι=> actual (W' i) (V' i) q
local notation "L[" j "]" => fun i:ι=> bonnet (W' i) (V' i) O hO (H'.tells i) j
local notation "Q'"=> Catch.Cover
include hp ht hv H' hD
variable (b':ι→ℝ) (hζ:S'.Meter b' (-(1/2:ℝ))) (hh:∀ᶠ i in S'.rail,0<b' i)
local notation "Δ"=> fun i=>(b' i)⁻¹
local notation "H"=> Q' S' j
local notation "Z[" n "]"=> fun (i:ι)=> fun u=> ((W' i|>.Θ)^n) • (K i u n)
include hW hζ hh hO
lemma tariff (hℓ:l+(q+1)≤k): H (graded l) Δ Z[l] x:= by
 let u:=spool O hO D W' V' H' hW ht hv hp hD j l hℓ b' hζ hh; exact (u.caliber (Proper.meter W' hW|>.1.pow l)).weak (by simp [graded])
lemma cortex (hv':l+(q+1)≤k) : H 0 Δ L[l] x:= by
 let p(n:ℕ) (i:ι):=(Z[n]) i; have hs(n:ℕ)(hn:n≤l):H 0 Δ (p n) x:=(tariff (l:=n) O hO D W' V' H' hW ht hv hp hD b' hζ hh (by omega)).weak (by unfold graded; have hr :=Nat.cast_nonneg (α:=ℝ) n; linarith)
 apply ((Catch.Cover.booking (F:=p) (range (l+1)) (fun n hn=> hs n (Nat.le_of_lt_succ (mem_range.mp hn))) (hh.mono fun _ hi=> inv_nonneg.mpr hi.le))).home; filter_upwards with i; ext1 y; exact Finset.sum_apply ..
lemma tail (hl:l ≤ m)(hT:m+(q+1)≤k): H (graded (l+1)) Δ (fun i=> L[m] i-L[l] i) x:=by
 induction hl with
 | refl=> simp_rw [sub_self]; exact Catch.Cover.fixed (fun _=>(0:ℝ)) (hh.mono fun _ hi=> inv_nonneg.mpr hi.le) (by simp only [norm_zero]; exact Meter.nil _ _ )
 | @step u hv' ih=>
    let v:= ih (by omega); let h' : H (graded (l+1)) Δ (Z[u+1]) x:= (tariff O hO D W' V' H' hW ht hv hp hD b' hζ hh hT).weak (by unfold graded; have hh:= Nat.cast_le (α:=ℝ)|>.mpr hv'; push_cast; linarith)
    apply (v.add h').home; filter_upwards with i; ext1 y; change (_-_) + ((Z[u+1]) i) y= (L[u+1]) i y- (L[l]) i y; rw [show (L[u+1]) i y=(L[u]) i y+Z[u+1] i y from Finset.sum_range_succ ..]; abel -- Lean timeout.Provision via ring identities if needed.
omit hζ hh
abbrev debt (l:ℕ)(x:X):= actual Q R q x - bonnet Q R O hO hR l x
local notation "G'"=> roughMark (j+1) q + (j+1:ℕ) -- coarser
local notation "tξ"=> fun i:ι=> debt (W' i) (V' i) O hO (H'.tells i)
include hy in
lemma gross (hj:j ≤ k) (hz:m+(q+1) ≤ k) : Q' S' (j+1) G' (fun _=>1) (fun i=> tξ i m) x:= by
 obtain ⟨h1,h2⟩:= Proper.meter W' hW; let z:= tξ; let u:=cortex (j:=j+1) O hO D W' V' H' hW ht hv hp hD (U) h1 (Eventually.of_forall fun i=>(W' i).Θp) hz; apply Cover.sub (f:=A) (g:= L[m]); swap
 · refine ((u.trim h2 (by norm_num)).weak ?_); unfold roughMark Aux.Name.vigor; push_cast; let x' : ℝ:=j; nlinarith only [show 0 ≤ ((j:ℝ)+1)^3 by positivity, Nat.cast_nonneg (α:=ℝ) j, Nat.cast_nonneg (α:=ℝ) q]
 exact (ranked O hO D W' V' H' hW ht hv hp hy hD).weak (by linarith only [Nat.cast_nonneg (α:=ℝ) (j+1)])
local notation "κ★"=> Aux.Name.radium
-- available after L, not derivative estimate hidden. Spend Coordinate scale after.Read this request before Bake!
omit hW hp ht hv H' hD hO in
lemma lustre (G:Gauge) (L:Side) (j m q:ℕ) (e:ℝ): ∃ d:ℝ,∃ r≥ max m (j+1), graded (r+1)< d∧ ∀ᶠ x in atTop,let z:= Pressure.betaF G x L; ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] (u:E→ℝ) (y:E), (∀ p∈Metric.closedBall y (z^(-(1:ℝ))),Brush (j+1) (z^(roughMark (j+1) q+(j+1:ℕ)+1)) 1 u p)→ (∀ p∈Metric.closedBall y (z^(-(1:ℝ))),‖u p‖ ≤ z^d) → Brush j (z^e) 1 u y:= by
 obtain ⟨v,hv⟩:= Lantern.iteration G L j (m:=e) (d:=roughMark (j+1) q+(j+1:ℕ)+1) (a:=1) zero_lt_one; obtain ⟨V',hV⟩:= exists_nat_gt (-v*2); refine ⟨v,max m (j+1)+V', by omega,?_,?_⟩; · unfold graded; push_cast; linarith [(show 0 ≤ max (m:ℝ) ((j:ℝ)+1) from (Nat.cast_nonneg _).trans (le_max_left ..))];
 filter_upwards [hv] with i hi hZ x _ _ f using hi _ ℝ f
variable {e u':ℝ} (hT₂: ∀ᶠ x in (atTop:Filter ℝ),let z:= Pressure.betaF G x P.L; ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] (u:E→ℝ) (y:E), (∀ p∈Metric.closedBall y (z^(-(1:ℝ))),Brush (j+1) (z^(roughMark (j+1) q+(j+1:ℕ)+1)) 1 u p)→ (∀ p∈Metric.closedBall y (z^(-(1:ℝ))),‖u p‖ ≤ z^e) → Brush j (z^u') 1 u y) -- spender via lustre witness
variable (hz:(S').Meter (fun i=> ‖y i‖) (-(1/2)))
omit hp
include hT₂ hz
local notation "L0"=>fun i:ι=>(W' i).whenP
local notation "R"=> Aux.Name.radium W'
lemma caudle (hV: n'+(q+1) ≤ k)(hd: graded (n'+1) < e) (hj:j ≤ k) : H u' (fun _=>1) (fun i=> tξ i n') y:= by
 let s i:= Metric.closedBall (y i) (R i); let T':= S'.book s; let v:=S'.bookF s; let Z(a:Σ i:ι,{x:(W' i).X//x∈s i}):= W' a.1; let ht' := Horn.music W' V' H' T' Sigma.fst v; let q':= Proper.sail W' hW T' Sigma.fst v; let u(x:Σ i:ι,{x:(W' i).X//x∈s i}):=x.2.1; have hu := Aux.Name.aux_burden (b:=R) hz ((hW.look.bill (Sienna.belt G P.L)).weak (by norm_num)) -- namespace
 have hh:=gross O hO D Z (fun i=>V' i.1) ht' q' (y:=fun i=>y i.1) (x:=u) (v.tends.eventually ht) (hv.pays _ v) hu (Eventually.of_forall fun i=>mem_closedBall_iff_norm.mp i.2.2) hD hj hV
 have hβ:= recovers O hO D Z (fun i=>V' i.1) ht' q' (y:=fun i=>y i.1) (x:=u) (v.tends.eventually ht) (hv.pays _ v) hu (Eventually.of_forall fun i=>mem_closedBall_iff_norm.mp i.2.2) hD hV
 let f i:= tξ i n'; have hsS:T'.Meter (fun i=> f i.1 (u i)) (graded (n'+1)):= hβ.2.stamps n' le_rfl; let R' i:= (W' i).due; intro p hp; filter_upwards [S'.booked s (fun i x=>Brush (j+1) (S'.cost i^(G'+1)) 1 (f i) x)|>.1 (hh _ (lt_add_one _)), S'.booked s (fun i x=> |f i x| ≤ S'.cost i ^e)|>.1 (hsS _ hd), hW.look.tends.eventually hT₂, S'.pos,hW.look.same] with i hi hI hm hv hx; let H0:=hm ((W' i).X); have ht : S'.cost i= R' i:=hx
 apply (H0 (f i) (y i) ?_ ?_).climb ?_ le_rfl
 · rw [ht] at hi; exact hi
 · rw [ht] at hI; exact hI
 change (R' i)^u' ≤ _; rw [ht] at hv ⊢; exact Real.rpow_le_rpow_of_exponent_le hv hp.le
include hζ hh
-- on compact D-real.Step.Envelope { y} across Q. True mask not compared here, prior part for any coalition.Ph.Orbit.Frame.Bank.
lemma epigraph (hv':graded (n'+1)< e)(hA:u' ≤ graded (m+1))(hm':m ≤ n')(hV:n'+(q+1)≤k)(hj:j≤k): H (graded (m+1)) Δ (fun i=> tξ i m) y:= by
 let hξ:= caudle O hO D W' V' H' hW ht hv hD hT₂ hz hV hv' hj; let p y:= tξ y n'; have he:H (graded (m+1)) Δ p y:= hξ.small le_rfl hA (((hζ.low (by norm_num) zero_lt_one).and hh).mono fun _ hi=> (one_le_inv₀ hi.2).2 ((le_abs_self _).trans hi.1.le)); apply Cover.home ((he).add (tail O hO D W' V' H' hW ht hv hz hD b' hζ hh hm' hV)); filter_upwards with i; let V':= he; ext1 x; exact sub_add_sub_cancel ..
end Aurum
end YM.Qlocal.Bind
