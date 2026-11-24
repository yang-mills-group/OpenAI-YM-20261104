import YM.AllOrder.Floe.Pit
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a b C D Λ σ:ℝ}{k N l:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
set_option quotPrecheck false
local notation "Q[" n "," hn "]"=> (arbitrate P K (n:=n) hn)
variable {ι:Type} [Nonempty ι] (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i)) (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
set_option quotPrecheck false
local notation "A[" i "," n "]"=> clay P K (x i) p n
local notation "u[" i "," n "]"=> Lapis.orbit T[n] (F i n)
variable (V:ι→ Layout G) (T:Finset Age) (hV:∀ i,Legal T (V i)) (Γ:ι→ℝ)
local notation "D[" i "," n "," hn "]"=> (startup T[n] O (label S[n]) (x i) p Q hn (hx i) (h i n hn) hO)
local notation "W"=> License (Ad G P K) Γ
namespace Aero
open Haiku Echo StateE Further.PhysicalPeriodLimitF933 Shingle Macrame
local notation "u'" => prePhase P K p O x L Q hx hO F h V T hV
local notation "f₀"=> Function.swap (u')
variable (i:Age) (hi:i∈T)
include hi hV
lemma prereq_valid (t:ι): Legal (i.prereq T) (V t):= tickets _ _ _ (hV t) hi -- include
variable {μ ε:ℝ} {Γ' : ι→ℝ}
local notation "R₀"=> i.prereq T
local notation "v'" => prePhase P K p O x L Q hx hO F h V (i.prereq T) (prereq_valid V T hV i hi)
variable {A B:Snap ι G}{M:ℕ}(W' : Scores (Ad G P K) Γ σ l N (Function.swap (prePhase P K p O x L Q hx hO F h V T hV)) A)
    (X':Scores (Ad G P K) Γ' μ M N (Function.swap (prePhase P K p O x L Q hx hO F h V (i.prereq T) (prereq_valid V T hV i hi))) B)
-- Link rank at κ doesn't consume higher. Price transition through Period Moment at ALL True Calls along any χ.Min crossing leg base.
include W' X' Q hV hB hi
lemma equalH {k:ℕ}(hk:k < i.e)(hv:k≤N)(j:ι) (n:Side) : snap A k j n=snap B k j n:= by
 funext y

 let H:=dock_larger P K hB; let η:= Ink.LinTest.eval (k+2) y; let w:=Echo.amplify n; let W₀:=Echo.arm n
 refine tendsto_nhds_unique_of_eventuallyEq (W'.crossover hv j H w (Echo.limitless n) (fun j=>(j+1)^4) W₀ (fun i=> by positivity) _ η) (X'.crossover hv j H w (Echo.limitless n) (fun j=>(j+1)^4) W₀ (fun i=>by positivity) _ η) ?_
 obtain ⟨d,H⟩:=dock_larger P K hB; filter_upwards [(Echo.limitless n).eventually (eventually_ge_atTop d)] with a ha; let v:= w a; have hh:Ad G P K v:=H _ ha; let f:= D[j,v,hh]; let L:= u' j k; let V':= v' j k; have he:L v=V' v:= by unfold L V' prePhase; rw [dif_pos hh,dif_pos hh]; have ht:= orient T[v] (V j) T f (hV j) R₀ (i.prem T) (orders _ _ i (hV j) hi) hk; rw [ht]
 let C': (rule E v→ℝ)→ℝ:=fun p=> ((↑((a+1)^4:ℕ):ℝ)⁻¹) * p (convey (W₀ a) y); exact congr_arg C' he
omit X' W' hi Q hB hV in
lemma variet (j:ℕ)(n m:Side)(x':Macrame.Window n m k) (u:ℕ→Atom G l)(ha:0<a)(he:Extra.Iteration.Charged u a C)(v:rule E n): Radial.jet (Stationary.turnSeries (m:=m) u) j (convey x' v)= (k:ℝ)*jet (Stationary.turnSeries (m:=n) u) j v:= by
 let f(c:Side):= Stationary.turnSeries (m:=c) u; let X:=convey (α:=E) x'; have hf(z:Side):= Stationary.turns_analytic (m:=z) u ha he; have hp : f m ∘ X = (k:ℝ) • f n:= by funext v; unfold f Stationary.turnSeries; rw [Function.comp_apply]; simp_rw [show Stationary.input G m (X v)=x'.links (Stationary.input G n v) from (billing x' v)]; simp_rw [x'.signed, Macrame.Window.unc]; unfold Patch.average; simp_rw [← Finset.mul_sum]; simp only [Pi.smul_apply, smul_eq_mul]; ring
 rw [← Kinetic.pivot X (f m) v (hf m).contDiffAt j]; -- unfolding f fail
 unfold jet; rw [hp,iteratedFDeriv_const_smul_apply (a:=(k:ℝ)) ((hf n).contDiffAt),_root_.smul_apply]; simp only [smul_eq_mul]; ring
-- leading tip χ via Mentor.Please.True period `Offers①` ensures every overlap.
variable {K':ℕ→Atom G i.r}
-- for any Ad n with mentor
lemma centersH (hn: I₀ n)(t:ι)(u:ℕ→Atom G i.r)(hh: Mentor (F:=trees P K n) (ρ:= F t n) (V t i) u) (ho:AnalyticAt ℝ (Stationary.turnSeries u (m:=n)) 0) (x':rule (Coarse G) n) : jet ((v' t i.e n)-(u' t i.e n)) i.r x'=jet (Stationary.turnSeries (m:=n) u) i.r x':= by
 let Vε:= D[t,n,hn]; let U:= augment T[n] (V t) T Vε (hV t); let vB:=augment T[n] (V t) R₀ Vε (tickets _ _ _ (hV t) hi); let g:=distilled U i.e; let w:=distilled vB i.e; let c:rule E n≃L[ℝ] Apex n G:= exteriorL G n; let L' (x:Apex n G):= (x,(0:R[n])); let L:= note_n (i:=i) T[n] (V t) Vε i.e ∘ L';
 have hl: ContDiffAt ℝ ω L 0:= ((((spine_cost ..):Plausible (note_n (i:=i) T[n] (V t) Vε i.e)).app (LinearMap.inl ℝ (Apex n G) R[n])).smooth.contDiffAt)
 have hp:= advances T[n] (V t) T i Vε (hV t) hi; let y:= c x'; have ht : w=-(g-w+L)+g+L:= by abel
 have he: jet L i.r y=jet (Stationary.turnSeries (m:=n) u) i.r x':= by
      have hx:=tariff_match T i (V t) Vε rfl (hV t) hi hh; let v:= (Stationary.turnSeries (m:=n) u); let M:=(c.symm).toContinuousLinearMap
      have hΛ:AnalyticAt ℝ v 0:= ho
      have ht : L=jet v i.r ∘ M:= by funext a; have hz:= hx (c.symm a); exact (c.apply_symm_apply a) ▸ hz; -- syntax
      rw [ht,Kinetic.pivot M (jet v i.r) _ ((Haiku.Project.maturity v i.r).read.smooth.contDiffAt),show M y=x' from c.symm_apply_apply x',jet,Haiku.Project.self v hΛ.contDiffAt]; rfl
 unfold prePhase; have hs:i.e≠0:= by unfold Age.e; omega
 rw [dif_pos hn,dif_pos hn,if_neg hs,sub_zero,sub_zero]; change jet ((w-g) ∘ c.toContinuousLinearMap) i.r _=_; rw [Kinetic.pivot c.toContinuousLinearMap (w-g) _ ?hd]; swap
 · let hε:ContDiffAt ℝ ω (w-g) 0:=by rw [show w-g= L - (g-w+L) by abel]; exact hl.sub hp.read.smooth.contDiffAt
   exact hε
 rw [show w-g=L-(g-w+L) by abel]; have hr :Plausible L:= by exact (show Plausible (note_n (i:=i) T[n] (V t) Vε i.e) from spine_cost ..).app (LinearMap.inl ℝ (Apex n G) R[n]); -- include hp f'_u
 rw [jet_minus hr hp.read,breakR hp (show i.r-1 < i.r by unfold Age.r; omega),sub_zero]; exact he
end Aero
end YM.AllOrder.Floe
