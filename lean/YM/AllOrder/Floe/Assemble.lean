import YM.AllOrder.Floe.Hull
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
abbrev mills (b:ℝ)(N:ℕ)(i:Age):= let k:= i.r-1; small_a (weaker (k+1) (Rail.widthG (chant b N (3*N)) (k+1)))
variable {M:Snap ι G}(X':Scores (Ad G P K) Γ σ l N (Function.swap (prePhase P K p O x L Q hx hO F h V T hV)) M) (A0:PortPre P K p x b B C0)
abbrev vista (M:Snap ι G)(i:ι): Scene G:= fun k n=> snap M k i n
variable (h0:0<b)(hs:b≤leaseF a N) (v:Age→ℕ)(hΛ: CreditF Γ (v u) L) (ht:u∈T) (hN:u.e≤ N) (he:∀ i,StateE.Kernel (s u) (s' u) Ω Ω' P.L (Y i) (Y' i) (D' i))
variable (β:ι→ℝ)(hβ:∀ i,StateE.Quoted (V i u) (s u) (β i))(hγ:∀ i∈ Age.prereq u T, Aero.request b Γ (v u) N V i)(hc:ClearUp G q ψ C' s' u σ' Ω')
variable (hΨ:σ'≤ mills b N u)(hΦ:σ' ≤ ξ)
variable (hρ:∀ i:ι,∀ n:Side,Aero.ContinuousLife (fun n=> Ad G P K n ∧ (Towers.Diagonal (dock P K n) (Y i) (Y' i) (D' i)) ∧ Precision.Guessed (S:=dock P K n) (trees P K n) (installed ((dock P K n).ratio) (D' i).A0) (F i n)) n)
variable (hf:0<ε)(hf₀:∀ i n,Floor (Y i) p n ε Ω)(hφ:∀ i n,Bid.Sworn (Y i) n G)
local notation "Wx"=> u.prereq T
local notation "K₀"=>StateE.career u.r P.L.val (s u) (s' u) Ω Ω'
include h0 hc X' hs ht hΛ hN hι hF hfloor hD hΨ hΦ he hβ hγ A0 hρ hf hf₀ hφ hO hy hB
lemma evokes : Spirit Γ q y (vista M) s' u ψ C' σ' Ω' (v u) N (fun i=>K₀*β i):= by
 refine ⟨hc,⟨Y',fun i=>?_⟩,?_⟩
 · have hh i : (Y' i).metric.strip σ' Ω':= fun j k=> ((hι i) j k).mono hΦ le_rfl; exact ⟨hh i,(hfloor i 1).starts,fun n=> living Y' hh hF hfloor hD hy i n hc.pos⟩
 obtain ⟨B',⟨B⟩⟩:= solo P K p O x L Q hB hx hO F h V Wx (prereq_valid V T hV u ht) Γ A0 h0 hs hΛ hγ
 choose KX hK hμ using fun i:ι=> sustain G P.L (he i) P.odd_side (hβ i) (show 2≤ u.r by unfold Age.r; omega)
 refine ⟨vista B', fun j hj i=>?_,fun i j hj n=>?_,?_,KX, fun i=> ⟨hK i,?_⟩⟩
 · funext n; exact (equalH P K _ _ _ _ _ hB hx hO _ h V T hV Γ u ht X' B hj (hj.le.trans hN) i n).symm -- K shadow
 · exact ⟨B.plaus hj i, Aero.reign P K p O x L Q hB hx hO F h V Wx (prereq_valid V T hV u ht) (G₀:=Γ) B hj⟩
 · exact money.squeeze (Pace.money.species (fun i=>(B.earns u.e i hN).1) B.pos (B.pay u.e hN).1) hΨ hc.pos le_rfl
 intro n; refine affords P K p O x L Q hB hx hO F h V T hV Γ u ht X' B hN i _ (he i).beam (hK i).pay ?_; obtain ⟨Yx,d,H,hL,hx₁⟩:= hρ i n; refine ⟨Yx,d,H,hL,fun j=>?_⟩; obtain ⟨hfN,hn,hZ,hL'⟩:=hx₁ j; exact ⟨hfN,hn,hμ i (Yx j) (Progress.ClassicalKin.Tent.below P (Yx j)) (dock P K (Yx j)) rfl _ p (x i) ε Ω (hf₀ i (Progress.ClassicalKin.Tent.below P _)) (hφ i _) hn.1 hZ hf (F i _) ((h i (Yx j) hn).critical) hL'⟩
end Step
end YM.AllOrder.Floe
