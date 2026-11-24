import YM.Contacts.Junction.Catalog
/-! # analytic transfer to real frame. `Caps..` -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω':ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform
open Push.AbsoluteSums
section pilot
variable {V X:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
variable {F G: V → ℝ}{S: X→ℕ→ℝ}
lemma berg (hf:AnalyticAt ℝ F 0)(hg:AnalyticAt ℝ G 0)(h:Rays (k+3) (F-G))(i:ℕ)(hi:i≤k)(x:V): Radar.beats F x i=Radar.beats G x i:= by
    let f:=Radial.layers F; let g:=Radial.layers G; have hp j (hh:j≤k): f j=g j:= by unfold f g; ext x; unfold Radial.layers; erw [nightwalk hf hg h (j+2) (by omega) x,nightwalk hf hg h 2 (by omega) x]
    have he s j (hh:j ≤ k): Zone.TaylorPow f s j x=Zone.TaylorPow g s j x:= by
       induction s generalizing j with|zero=> rfl|succ s ih=> rw [Zone.TaylorPow,Zone.TaylorPow,Zone.mul,Zone.mul]; apply sum_congr rfl; intro y hy; have ht := HasAntidiagonal.mem_antidiagonal.mp hy; rw [ih _ (by omega),hp _ (by omega)];
    exact sum_congr (s₂:=Finset.range (i+1)) rfl fun k _=> congr_arg ((k.factorial:ℝ)⁻¹ * ·) (he k i hi)
end pilot
open StagePort
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "Xr" => (fun i=> Dew.Q (ι i))
local notation "K₀" => (fun i=> StagePort.bench (Φ i))
local notation "O₀" => (fun i=> StagePort.eternal (Φ i))
local notation "O₁" => (fun i=> StagePort.targetY (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
abbrev courier (Φ:ℕ→StagePort G U P X k L σ C M n) :Trunk (fun i=>(Φ i).dew.X) (fun i=>(Φ i).dew.Y) := let b i (z:(Φ i).dew.Y) (x:(Φ i).dew.X):= (Φ i).crab x z; Loom.Capture.expn (Loom.Capture.pulse (fun i=>(Φ i).bench) (fun i=>(Φ i).dew.grad) b)
local notation "μ" => (fun i=>StagePort.μ (Φ i))
def summitK (Φ:ℕ→StagePort G U P X k L σ C M n)(d:ℝ): Lamp (fun i=>(Φ i).dew.X):= Loom.Patch.stay (fun i=>(Φ i).μ) (fun i=> wick G L d (Φ i).pearlRide) (courier Φ)
local notation "δ" => (fun i=> StagePort.bare (Φ i))
local notation "π" => (fun i=> StagePort.smooth (Φ i))
local notation "α" => (fun i z x=> StagePort.crab (Φ i) x z)
namespace Travel
variable (p:Travel N Q Φ) (hG:G.Simple)(hk:2≤k)(hn:k ≤ n)(hp:LocalRatio P)
    (hd:0<d)(hr:Loom.Capture.race < τ)(hτ:τ<0)(hu:τ*((k:ℝ)+1)<K)(hv: K<0)
local notation "W" => fun i=> Radar.beats (K₀ i)
local notation "Z" => (fun i=> Radar.beats (δ i))
include p hG hk hn hp
lemma pilot : ∀ᶠ i in atTop, Radar.Alive volume (μ i) (settle (Dew.c (ι i))) (O₀ i) (O₁ i) (Dew.℘ (ι i)) k ∧ ∀ j≤k,∀ x, W i x j= Radar.beats (O₀ i) x j:= by
   obtain ⟨d,e,j,_,_,H⟩:=p.ship; filter_upwards [H,(presentFee p hk hG hp hn).1.analytic] with i hi hp'; let q:=Φ i; let D:= q.dew; obtain ⟨h₀,he,c,hc⟩:= hi.2.port; have h:= hi.2.truePE; obtain ⟨T,hT,h₁⟩:= h.service; have hs:= Cove.estate P D.B D.T D.label D.L h.staples h.stitches.large hp he h₀; refine ⟨Cove.bears P D.B D.T h.staples h.stitches.large hp he h₀ hc hT (House.spectrum q.outB _),fun j hj x=>?_⟩; let U:= hand (hair q.importB D.f) (k+3); let W':= trib k q.budget q.importB D.T.high D.T.up (f:=D.f); let V':=material D.T.high D.T.up (f:=D.f); apply Eq.symm; apply berg (F:= q.eternal) (k:=k) (G:= q.bench) hs.1 hp' _ j hj; rw [show q.eternal-q.bench=(enact U-enact V'- W')∘ (shuttle D.B D.L) from ?_ ]; swap; · ext1 x; change (_+_)-( (D.fan P x)+W' _)= _-W' _; change (D.fan P x+(enact U-enact V') (shuttle D.B D.L x))- (D.fan P x+W' _)= _; abel
   have hW : AnalyticAt ℝ W' 0 := (loomT hi.2.lit).add ((tribX hi.2.lit).1); exact merkin ((he.vest.sub h₀.vest).sub hW) (Buyer.hands h.staples hi.2.lit hk hG hi.2.bankW he h₀).2 _ (shuttleH ..) (shuttle0 ..)
local notation "r" => (Loom.Patch.weight μ ∘ Loom.Capture.rol (Loom.Capture.codes K₀ γ α) k)
abbrev wagon (i:StagePort G U P X k L σ C M n) (x:i.dew.X):i.dew.X:= i.dew.grad⁻¹ • (i.flag • x)
lemma order_slots : ∀ᶠ i in atTop,∀ j≤ k, r j i= (Loom.Capture.branch (fun j=> meteor (r j)) (Loom.Patch.irisTail δ γ π) j i):= by
    filter_upwards [pilot p hG hk hn hp,p.parameter.pos] with i hv he j hj; let q:= Φ i; let Φ':=q.bench; let g:= q.dew.grad; let u:=wagon q; have hw:0<g:=he; let s:= Radar.spectrum (StagePort.μ q) q.eternal
    funext x; have H (x:q.dew.X) (j:ℕ) (hm:j≤ k): r j i x=g^j*s (1,u x) j:= by
       unfold s Radar.spectrum Function.comp Loom.Patch.weight; rw [costSum,← MeasureTheory.integral_const_mul]; apply integral_congr_ae; filter_upwards with z; change g^j*expsum _ _ _ (g⁻¹ • q.crab x z)=_; rw [show g⁻¹ • q.crab x z=((1,u x),z) from Prod.ext (Prod.ext (inv_mul_cancel₀ hw.ne') rfl) (inv_smul_smul₀ hw.ne' z),← expsum_limit (a:=Radial.layers q.bench) (funext fun _=>Radial.Stationary.layers_zero _) hm]; exact congr_arg _ (hv.2 j hm (((1:ℝ), u x), z));
    let L:= settle (G:=G) q.dew.c; let o i:= Z i; rw [H x _ hj,show s (1,u x) j= _ from Radar.transmission hv.1 (orchestra ..) (u x) _ hj]; unfold Loom.Capture.branch; rw [Finset.sum_apply,Finset.sum_apply,Finset.mul_sum]; apply sum_congr rfl; intro y hy
    have hz: y.1+y.2=j:= HasAntidiagonal.mem_antidiagonal.mp hy; erw [Pi.mul_apply,Pi.mul_apply]; change g^j*(s (1,0) y.1 * Radar.beats q.bare ((1:ℝ),L (u x)) y.2)= r y.1 i 0 * (g^y.2 * Radar.beats q.bare (g⁻¹ • q.smooth x) y.2); rw [H 0 y.1 (by omega)]; rw [show u 0=0 from (by simp [u,wagon]),show g⁻¹ • q.smooth x=((1:ℝ),L (u x)) from Prod.ext (inv_mul_cancel₀ hw.ne') ((L.map_smul ..).symm)]; change g^j*(s (1,0) y.1 * Radar.beats q.bare ((1:ℝ),L (u x)) y.2)=_; rw [show g^j=g ^y.1 * g^y.2 from (hz ▸ pow_add g y.1 y.2)]; ring
end Travel
end Provision
end YM.Contacts.Junction
