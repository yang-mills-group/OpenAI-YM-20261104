import YM.Qlocal.Squall.Ripple
import YM.Qlocal.Feud.Cayenne
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Squall
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open AllOrder Floe Step Step.PlanV Iron
open Response Ink Ink.Method Ink.Money
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Pace PriceCompiler Further.PhysicalPeriodLimitF933
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
namespace Dredge
open Aero StateE Rent Laurent Shingle Macrame PhysicalNext ThroughLaunch Pane Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Quipu Quipu.Tilt Quipu.Sonnet Tern Quipu.Eluder Incline Incline.Bookworm
variable {X:Org.Metals G}
variable (D:RG.Supply.Rolls X.p)(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y k N:ℕ) (hx:4≤x)
open Catch Aux Aux.Name Extra.Iteration Sienna ConnectedActivityE6.Coat
open Feud Feud.Peak Feud.Shelter Bind
local notation "uℓ"=> Burn.horizon k
local notation "T"=> Aux.scope k
set_option quotPrecheck false
local notation "p"=>X.p.profile x
local notation "L0"=>D.L x
local notation "ʻP"=>Mural.sheet X.p D hx
local notation "𝒪"=> X.O
local notation "K₁"=> X.p.kernel
variable (α:Type)[Fintype α][DecidableEq α](B:Marker.Census α)(g:α→ℕ)(r t:ℕ)
local notation "S"=> Sail α D R x y uℓ N hx B g r t
variable [Nonempty (Card D R x y hx (Burn.horizon k))] (Q: Dredge.Pose D R x y (Burn.horizon k) N hx α B g r t)
namespace Starboard
open Feud.Peak
variable {w:ℝ→ℝ}{j L l:ℕ}{d a:ℝ}(U:Uniform.Before G (X.p.profile x).width (X.p.profile x).paths (Mural.sheet X.p D hx).J X.p.kernel (l+3+3))
    {δ:Type} [Fintype δ] (D₀:δ→ Senses B) (hP:Canopy.Button.Ideal D₀ univ) (s:Senses B)(hs:s.val=Canopy.Button.pin D₀ univ hP)
local notation "I"=> Aux.Name G ʻP K₁ w k p (l+3) U
abbrev silent (W:S):= Peak.Quiet D₀ (W.credit.son t) W.wake
local notation "Ψ"=> silent D R x y k N hx α B g r t D₀
-- attention to Gauge step.Location.Calendar.O.Scope. Shopper cert for ΩSend starts. Stamps can vary.Camera. Power inherited debt. All rooted η. y∈… for ANY x not chosen.
variable (F F' E:ℝ→ℝ)
local notation "ξ"=> atLevel α g D₀
local notation "X0"=> Bind.Aurum.Shackle -- unused
structure Frame (F F' E:ℝ→ℝ)(d:ℝ)(a:ℝ) where
    moon : Sail α D R x y uℓ N hx B g r t
    chart : I
    since : chart.whenP=a
    shelf : silent D R x y k N hx α B g r t D₀ moon
    symbol : α→ Site chart.c
    fine : α→ Site chart.f
    keys : ∀ i,(chart.data).ratio.parent (fine i)=symbol i ∧ HEq ((chart.data).ratio.residue (fine i)) (moon.chart i)
    trajectory : chart.tube.up=moon.ticket.self.north
    age : chart.shape=moon.ticket.extra
    lends : chart.Civil (R.pre (Burn.horizon k) x)
    life : moon.ticket.self.paid= strengthP (chart.due)
    roof : Stores.till chart.whenP ≤ chart.c.val
    W : chart.X
    stone : chart.goods 𝒪 d (F chart.whenP) W
    pay : δ→ℝ
    exacting : ‖W‖≤ E chart.whenP * chart.Θ
    bill : |∏ j, pay j| ≤ F' chart.whenP
    mask : Config G chart.c → ℝ
    duty : let Γ₀:=Stanza.son moon.credit t; let p':= Tale.short Γ₀ moon.wake (Stores.till chart.due); Shelter.Dock.Cargo chart (atLevel α g D₀) pay (fun j=> Γ₀.markℓ p' fine (D₀ j)) W mask
-- Avoid lens builder assuming brush. cost conditions from clock.
local notation "Uℓ"=> Frame D R x y k N hx α B g r t (w:=w) U D₀ F F' E d
local notation "A"=> fare G L0
set_option quotPrecheck false
local notation "Θ"=> Sigma Uℓ
noncomputable abbrev tagρ (X₀: Frame D R x y k N hx α B g r t (w:=w) U D₀ F F' E d a):= X₀.moon
abbrev head (V:Frame D R x y k N hx α B g r t (w:=w) U D₀ F F' E d a):= (Q.issue V.moon).son t
abbrev model (V:Frame D R x y k N hx α B g r t (w:=w) U D₀ F F' E d a) := let U':=(Q.issue V.moon).son t; (∏ i,V.pay i) • Tale.wake s U' (U'.short (Anthem.statement U') (Stores.till V.chart.whenP)) V.symbol V.chart.Θ
variable (hH:Lantern.Bolt G (D.L x) w)(hE:Rate G (D.L x) 0 E)(he:∀ᶠ i in (atTop:Filter ℝ),0<E i)(hL:Rate G (D.L x) 0 F)(hL':Rate G (D.L x) 0 F')
   (hZ:∀ a: Finset δ,Bind.Aurum.Version G (D.L x) j l (Flute.size (atLevel α g D₀) a) r) (hv:Lagger.dues g s.val+r<j)
local notation "H₀"=>Prior.yard R (Burn.horizon k) N x
local notation "H'"=>Prior.yard R (Burn.horizon k) N y
local notation "T₀"=> (A).stage Uℓ
local notation "ℍ"=> ((A).stage Uℓ).Meter
include hE he hH hL hL' hP hs hZ hv
set_option maxHeartbeats 1800000 in
lemma shines {z:ℝ} (hd:0<d)(hz:graded (r+1)< z): ∀ᶠ a in atTop,∀ V: Uℓ a, Brush j (betaF G V.chart.whenP L0 ^ z) (E V.chart.whenP * V.chart.Θ)⁻¹ ((V.mask- model D R x y k N hx α B g r t Q U D₀ s F F' E V)∘ Boulevard.actual) V.W:= by
 let X':=Θ; let M(v:X'):= v.2; let T':=(A).stage Uℓ
 let I':= {V:S // silent D R x y k N hx α B g r t D₀ V}; let g0(i:X') : I':=⟨i.2.moon,i.2.shelf⟩
 by_cases hN:Nonempty I'; swap; · exact Eventually.of_forall fun a x=> (hN ⟨g0 ⟨a,x⟩⟩).elim
 let θ(i:I'):=i.val; let «W»(i:X'):=i.2.chart; let w0(i:X'):= E (W i).whenP * (W i).Θ; let y0(i:X'):=(M i).W
 let Z0 i:=(Sigma.fst (β:=Uℓ) i); have hy(i:X'): (W i).whenP=Z0 i:= i.2.since;
 have hW : Proper W T':= ⟨⟨tendsto_comap.congr (fun i=>(hy i).symm), Eventually.of_forall (fun i=> show betaF G (Z0 i) L0= betaF G (W i).whenP L0 from congr_arg (fun s=> betaF G s (D.L x)) (hy i).symm)⟩,hH,R.pre (Burn.horizon k) x,(R.shape _).pos _,Eventually.of_forall fun i=> i.2.lends⟩
 have he₀ := hW.look; have hE' : ℍ w0 (-(1/2)) := ((he₀.bill hE).mul (hW.meter W).1).weak (by simp); have hxv :∀ᶠ i in T'.rail,0<w0 i:= (he₀.tends.eventually he).mono fun i hi=> mul_pos hi (W i).Θp
 let u₀:=(H₀); let u₁:= (H'); let wY:= Prior.stipend R uℓ N x / 4; let Z:= Pose.focused D R x y uℓ N hx α B g r t Q θ -- check
 let Λ : I'→α→ Site (ʻP).L := fun v=> Sail.chart (θ v)
 let Ω':= fun i:I'=>Sail.ticket (θ i); let L:=fun i:I'=> (Ω' i).self.north; let Γ₁:= fun i=> (Ω' i).self.paid; let η:= fun i:I'=> (Ω' i).extra; let iD := fun i s=> Q.halo i s ∘ θ
 have ha : u₀/2+u₀/2=u₀:= add_halves _; have ha' : 2*u₁+2*u₁=4*u₁:= by ring
 have hG: Feud.Peak.License (ʻP) K₁ X.O α B g T (p).clip η L Γ₁ Λ (Sail.credit∘θ) t (fun i=> (θ i).wake) (Q.issue∘ θ) t wY (2*u₁+2*u₁) (Tilt.insure (Prior.core R uℓ N x) N (Bent uℓ)) (Tilt.insure (Prior.core R uℓ N x) N (Bent uℓ)+Anthem.rankC t) iD (Q.thin∘θ):= by rw [ha']; exact Z
 let o(i:X'):= (M i).symbol; let o'(i:X'):= (M i).fine; let v:=fun i:X'=>F (W i).whenP; let Y:= fun i:X'=> (M i).pay; let C:=fun i:X'=> (M i).mask
 have hB:∀ i:I',(Stanza.son ((θ i).credit) t).Allows (u₀/2+u₀/2) 1:= by rw [ha]; exact fun i=> (θ i).cost
 have h0:0<u₀/2:=half_pos (Prior.yard_p ..); have h1:0<2*u₁:=mul_pos (by norm_num) (Prior.yard_p ..)
 have hΓ: ℍ (Γ₁ ∘ g0) 0 := (he₀.transfer (f:=strengthP) (Burn.hats_rate (G:=G))).eq_mem (Eventually.of_forall (fun i : X'=> (i.2.life).symm))
 have hn:ℍ (fun i:X'=> ((W i).c.val:ℝ)) 0:= (hW.counts W).smaller (Eventually.of_forall fun i=> by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact (W i).loom.step.trans (le_abs_self _))
 have hw:0<wY:=div_pos (soprano _ (Prior.core_p ..) _) (by norm_num)
 have hh:ℍ (fun i:X'=>dearth wY (W i).c) (graded (r+1)):= (he₀.bill (Rate.cutoff hw)).smaller (Eventually.of_forall fun i=> by rw [abs_of_pos (Real.exp_pos _)]; exact (Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (M i).roof) (neg_nonpos.mpr hw.le))).trans (le_abs_self _))
 have hM:ℍ (fun i:X'=>∏ j, Y i j) 0:= (he₀.bill hL').smaller (Eventually.of_forall fun i=> (M i).bill.trans (le_abs_self _))
 have hp:=Peak.spectator (p).clip L η Γ₁ α g (Sail.credit ∘ θ) (fun i=> (θ i).wake) Λ (Q.issue ∘ θ) (Q.thin ∘ θ) iD g0 W w0 y0 hG o o' D₀ hP s hs (fun _=>1) hB h0 h0.le (Clock.Meter.const T' 1) (fun i=> i.2) hW (Eventually.of_forall fun i=> (M i).stone) (he₀.bill hL) (hE'.smaller (Eventually.of_forall (fun i=> (abs_of_nonneg (norm_nonneg _)).trans_le ((M i).exacting.trans (le_abs_self _))))) hd hxv hE' (Eventually.of_forall fun i=>⟨(M i).age, (M i).trajectory,(W i).high,(M i).keys⟩) hΓ hn hh (fun i=> Stores.till (W i).due) (fun i=> Stores.till (W i).whenP) X.oga le_rfl hZ h1 h1.le (he₀.transfer (Rate.cutoff h0)) (he₀.bill (Rate.cutoff h1)) Y hM C (Eventually.of_forall fun i=> (M i).duty) hv le_rfl
 have h₁ : ∀ᶠ i in T'.rail, Brush j (betaF G (W i).whenP L0 ^ z) (w0 i)⁻¹ ((C i - model D R x y k N hx α B g r t Q U D₀ s F F' E (M i)) ∘ Boulevard.actual) (y0 i):= by filter_upwards [hp z hz,he₀.same] with i hw hA; change T'.cost i=_ at hA; change Brush j (T'.cost i ^ z) (w0 i)⁻¹ ((C i - model D R x y k N hx α B g r t Q U D₀ s F F' E (M i)) ∘ Boulevard.actual) _ at hw; rw [hA] at hw; exact hw
 exact (A).everybody _ |>.mp h₁ -- specialization
end Starboard
end Dredge
end YM.Qlocal.Squall
