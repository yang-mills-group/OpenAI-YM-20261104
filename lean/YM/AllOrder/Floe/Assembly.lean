import YM.AllOrder.Floe.Assemble
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
namespace Step
open Rent Aero StateE Extra.Iteration Pace
-- τ/m.R.Use-in-Folio. Unmasked true pupils Calendar. Height σ.C.param either Lift.Book.View.x Epoch.
variable (q:Clip) (y:ι→ PathData G)(L':ι→ℝ) {C' B C0 ψ ξ σ' ε' ε δ η Ω Ω' :ℝ} (hy:∀ i,(y i).Bounds q ψ C' (L' i))
    (Y Y':ι→Bed) (D':ι→Towers P.L) (hι:∀ i,(Y' i).metric.strip ξ Ω') (hF : ∀ i,Attached (Y' i) (y i)) (hfloor:∀ i n,Floor (Y' i) q n ε' Ω') (hD:∀ i n,Bid.Sworn (Y' i) n G) (hε:0<ε') -- ξ can be any width-m.Currency. Note uses lexical Y.* Floor not input!
    (s s' : Fees)(u:Age)
-- cofinal crossing geom Supply.Can buy any.L. Need figures.
variable {M:Snap ι G}(X':Scores (Ad G P K) Γ σ l N (Function.swap (prePhase P K p O x L Q hx hO F h V T hV)) M) (A0:PortPre P K p x b B C0)
variable (hρ:∀ i:ι,∀ n:Side,Aero.ContinuousLife (fun n=> Ad G P K n ∧ (Towers.Diagonal (dock P K n) (Y i) (Y' i) (D' i)) ∧ Precision.Guessed (S:=dock P K n) (trees P K n) (installed ((dock P K n).ratio) (D' i).A0) (F i n)) n)
variable (hf:0<ε)(hf₀:∀ i n,Floor (Y i) p n ε Ω)(hφ:∀ i n,Bid.Sworn (Y i) n G)
-- cash invariants. kernel resolved all widths; manpower `Holder` not chance α. Permitting full-snap local choices.One call.
def Fleet (Γ:ι→ℝ)(v:Age→ℕ)(N:ℕ)(V:ι→Layout G)(T:Finset Age)(B:Age→ι→ℝ)(s:Fees):Prop:= ∀ i∈T, CreditF Γ (gateE (v i) N+1) (B i) ∧∀ t,Quoted (V t i) (s i) (B i t)
lemma Fleet.legal {Γ v B s} (A:Fleet (ι:=ι) Γ v N V T B s) (xs:∀ i,0<s i) (i:ι) : Legal T (V i):= by constructor <;> intro x hx; exact ⟨s x,B x i,xs x,(A x hx|>.2 i).pay⟩; exact (A x hx|>.2 i).symm -- signature xs parsed.Nonempty
lemma decay (A:PortPre P K p x b B C0) {c}(hb:c≤b): Nonempty (PortPre P K p x c B C0):= ⟨A.peak,A.deep,A.nonneg,(fun i=>(A.peak_bound i).debt hb le_rfl),(fun i=>(A.deep_bound i).debt hb le_rfl),A.sheet,A.put⟩
structure PriorDue (G:Gauge)(q:Clip)(a ψ C':ℝ)(s s' : Fees)(b ξ :ℝ)(N:ℕ)(u:Age)(B σ':ℝ):Prop where
 reach : ClearUp G q ψ C' s' u σ' B
 good : ∃ c:ℝ,0<c ∧ c ≤ leaseF a N∧c≤b ∧σ' ≤ mills c N u ∧ σ' ≤ ξ ∧∀ i, Age.before i u→ c ≤ leaseF (s i) N
-- Season scheduling assembled later.
variable {S:Age→ι→ℝ}(v:Age→ℕ)(α:ι→ℝ)(hv:Aligned v N)(hh: Fleet Γ v N V T S s)
variable (hs:∀ i,0<s i)(hz:∀ i,0<s' i)(ht: T=tape N) (hα: Pace.Cost Γ 1 α) (hL: CreditF Γ 1 L)(hL':CreditF Γ 1 L') (hΩ:0≤Ω)(hΩ':0≤Ω') (hN: k+2=N)
variable {u':Fees}(hu:∀ i∈ Age.scope N,PriorDue G q a ψ C' s s' b ξ N i Ω' (u' i))(hX:∀ i∈ Age.scope N,∀ t,StateE.Kernel (s i) (s' i) Ω Ω' P.L (Y t) (Y' t) (D' t)) (hl:∀ i n,Channels P K p O x F q y α i n)
local notation "K₀"=>fun i:Age=> StateE.career i.r P.L.val (s i) (s' i) Ω Ω'
local notation "f₀"=>fun (i:Age) (x:ι)=> K₀ i*S i x
private lemma car_ge (L:Side)(v x Ω Ω':ℝ)(T':Towers L) (P Q:Bed)(k:ℕ)(h:Odd L.val) (hk:2≤k)
    (G:Gauge)(hp:StateE.Kernel v x Ω Ω' L P Q T') : 0≤ StateE.career k L.val v x Ω Ω':= by
 let V:= fun _ : ℕ=> Extra.Iteration.blank G k; have he : Quoted V v 1 := ⟨Extra.Iteration.Charged.mono (blank_cost v) le_rfl zero_le_one,fun _=>blank_sym,fun h=> (by subst k; exact blank_silent)⟩; obtain ⟨A,H,-⟩:=sustain G L hp h he hk; simpa only [mul_one] using H.pays
include X' v hv α hα hL hs hz hh ht hu A0 hL' hι hfloor hφ hf hF hf₀ hD hρ hl hN hX hΩ hΩ' hx hy hB hO h
-- α.v etc
variable (g:G.Simple)
local notation "X"=> vista M
include g
lemma towerbook : ∃ U R,Sustained Γ v α N s' (vista M) y f₀ k q U R:= by
 have ho(i:Age)(hi:i∈tape N) : Spirit Γ q y (vista M) s' i ψ C' (u' i) Ω' (v i) N (f₀ i):= by
    have hw:= hu i hi; obtain ⟨c,hc,hv₀,hT,hP₁,hP₂,hk⟩:=hw.good; have hL₀:=hv.firstF i; let H(i):=S i; obtain ⟨A'⟩:= decay P K p x A0 hT; have hI:= (ht.symm ▸ hi : i ∈ T); have hr l (h':l∈ i.prereq T): request c Γ (v i) N V l := by
       obtain ⟨hl,hν⟩:= mem_filter.mp h'; exact ⟨S l,s l,hs l, (hh l hl|>.1).up (hv.fareF hν), hk l hν, fun k=> (hh l hl|>.2 k).pay⟩
    exact evokes P K p O x L Q hB hx hO F h V T hV Γ q y L' hy Y Y' D' hι hF hfloor hD s s' i X' A' hc hv₀ v (hL.up hL₀) hI (Age.in_scope.mp hi) (hX i hi) (S i) (hh i hI|>.2) hr hw.reach hP₁ hP₂ hρ hf hf₀ hφ
 have hU:Haiku.Coat.strict ((fun i k n=>snap M k i n)+ fun i=> Haiku.Coat.Stipend q (y i) (α i)) 3:= cloudy P K p O x L Q hB hx hO F h V T hV Γ X' q y L' hy D' α hl g (by omega);
 have hh'' : Sustained Γ v α N s' X y f₀ 0 q V (sloping ∘ α):= practice g hy v Γ hU -- compare defeq orientation grouping. 
 have hc i (hi:i∈Age.scope N) : CreditF Γ (gateE (v i) N+1) (f₀ i):= by have hWi:= hX i hi (Classical.arbitrary _); exact CreditF.up ((freeC _ (car_ge _ _ _ _ _ _ _ _ i.r P.odd_side (by unfold Age.r; omega) G hWi)).mul (hh i (ht.symm ▸ hi)|>.1)) (by omega)
 apply resume Γ hy g v α hΩ' ho hz hL' hv hc hα (fun i j hj n=> ⟨X'.plaus hj _, reign P K p O x L Q hB hx hO F h V T hV X' hj⟩) (V) (sloping ∘ α) hh'' (by omega)
end Step
end YM.AllOrder.Floe
